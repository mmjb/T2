////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      Symex
//
//  Abstract:
//
//      Symbolic execution of program commands.
//
// Copyright (c) Microsoft Corporation
//
// All rights reserved. 
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the ""Software""), to 
// deal in the Software without restriction, including without limitation the
// rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
// sell copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included 
// in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED *AS IS*, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
// THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
// FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
// DEALINGS IN THE SOFTWARE.

module Symex

open Utils
open Term
open Formula
open Programs

let get_var_index var_map v =
    match Map.tryFind v var_map with
    | Some(n) -> n
    | None -> 0

let substitute_map_in_formula var_map f =
    Formula.alpha (fun v -> Var.prime_var v (get_var_index var_map v)) f

/// Remove unneeded statements from path pi (assignments to variables that never influence assumes)
/// Second parameter gives commands that are relevant for the "needed" bit, but are not supposed to be cleaned
let slice_path pi relevantCmds =
    let depends_on = System.Collections.Generic.Dictionary()
    let needed_vars = ref Set.empty

    //Run through the path, get needed variables and dependencies:
    let needed_vars_from_cmd c =
        match c with
            | Assume(_, f) -> Formula.freevars f
            | Assign _ -> Set.empty
    let track_dependency c =
        match c with
        | Assign(_, v, t) ->
            let d = if depends_on.ContainsKey v then depends_on.[v] else Set.empty
            depends_on.[v] <- Set.union d (Term.freevars t)
        | Assume _ -> ()

    for (_, cs, _) in pi do
        for c in cs do
            needed_vars := Set.union !needed_vars (needed_vars_from_cmd c)
            track_dependency c
    for (_, cs, _) in relevantCmds do
        for c in cs do
            needed_vars := Set.union !needed_vars (needed_vars_from_cmd c)

    //Now do a fixpoint thing where we recursively compute all needed variables
    let queue = ref (Set.toList !needed_vars)
    let relevant = ref Set.empty
    while not (!queue).IsEmpty do
        let var = (!queue).Head
        queue := (!queue).Tail
        if not <| Set.contains var !relevant then
            relevant := (!relevant).Add var
            if depends_on.ContainsKey var then
                for v in depends_on.[var] do
                    queue := v::!queue

    //Filter everything that's not needed out:
    let is_relevant c =
        match c with
        | Assign(_, v, _) when Set.contains v !relevant -> true
        | Assign _ -> false
        | Assume _ -> true

    let filter_out c =
        if is_relevant c then
            c
        else
            Assume(c.Position, truec)

    pi |> List.map (fun (l1, cs, l2) -> (l1, List.map filter_out cs, l2))

let add_vars_to_map fs var_map =
    let vars = List.fold (fun accum f -> Set.union accum (Formula.freevars f)) Set.empty fs |> Set.toList
//    let vars = Formula.freevars f |> Set.toList
    let rec add_vars vars var_map =
        match vars with
        | [] -> var_map
        | h::t -> add_vars t (match Map.tryFind h var_map with | None -> Map.add h 0 var_map | _ -> var_map)
    add_vars vars var_map

///
/// Convert path to path formula, applying SSA transformation.
/// Var_map contains var to SSA version number.
/// Return pair (<list of transition formulae>, <new var_map>).
/// If variable is not present in var_map, its version is 0.
///
let path_to_transitions_and_var_map p var_map =
    let command_to_formula var_map c =
        match c with
        | Assign(_, v, Nondet) ->
            let idx = (get_var_index var_map v) + 1
            let lhs = Term.var (Var.prime_var v idx)
            let var_map' = Map.add v idx var_map
            (Formula.Eq(lhs, lhs), var_map')
        | Assign(_, v, t) ->
            let idx = (get_var_index var_map v) + 1
            let lhs = Term.var(Var.prime_var v idx)
            let rhs = Term.alpha (fun x -> Var.prime_var x (get_var_index var_map x)) t
            let var_map' = Map.add v idx var_map
            (Formula.Eq(lhs, rhs), var_map')
        | Assume(_, e) ->
            let var_map = add_vars_to_map [e] var_map
            let f = Formula.alpha (fun x -> Var.prime_var x (get_var_index var_map x)) e
            (f, var_map)
    let rec commands_to_formulae cs var_map =
        match cs with
        | c :: cs' -> let (fs, var_map') = command_to_formula var_map c
                      let (fs', var_map'') = commands_to_formulae cs' var_map'
                      (fs :: fs', var_map'')
        | [] -> ([], var_map)

    // Convert a path (sequence of commands) to a sequence of formulae over the program variables.
    let rec path_to_formulae' p var_map =
        let is_skip cmd =
            match cmd with
            | Assume(_,f) -> Formula.is_true_formula f
            | _ -> false
        match p with
        | (l1, cs_orig, l2) :: rest ->
            let cs = List.filter (is_skip >> not) cs_orig
            let (fs, var_map') = commands_to_formulae cs var_map
            let (rest_formulae, var_map'') = path_to_formulae' rest var_map'
            (l1, fs, l2) :: rest_formulae, var_map''
        | [] -> ([], var_map)

    path_to_formulae' p var_map

let path_to_formulae p =
    path_to_transitions_and_var_map p Map.empty |> fst

let transitions_to_formulae ts = List.concat [for (_, f, _) in ts -> f]

/// Vars from 'vars' go to prevars and postvars.
/// Prevars and postvars are guaranteed to be distinct.
let path_to_relation path vars =
    let cmds =
        [for _, cmds, _ in path do
            for cmd in cmds do
                if not (Programs.is_disj_cmd cmd) then
                    yield cmd]

    let written_vars = Set.intersect (Programs.modified cmds) vars

    let unwritten_vars = Set.difference vars written_vars

    let (transitions, var_map') = path_to_transitions_and_var_map path Map.empty

    let formulae = transitions_to_formulae transitions

    let copy_forward v idx =
        Formula.Eq(Term.var(Var.prime_var v idx), Term.var(Var.prime_var v (idx + 1)))

    let copy_formulae = [for v in unwritten_vars -> copy_forward v 0]

    let aggregate_formula = Formula.conj (formulae @ copy_formulae)

    let prevars = [for v in written_vars -> Var.var(Var.prime_var v 0)]
    let postvars = [for v in written_vars -> Var.var(Var.prime_var v (get_var_index var_map' v))]

    let copy_prevars = [for v in unwritten_vars -> Var.var(Var.prime_var v 0)]
    let copy_postvars = [for v in unwritten_vars -> Var.var(Var.prime_var v 1)]

    Relation.make aggregate_formula (prevars @ copy_prevars) (postvars @ copy_postvars)

let find_path_interpolant_old try_ignore_beginning distance invar_formulae pi initial final =
    let path_formulae = [for (_, fs, _) in pi -> Formula.conj fs]
    let final_formula = Formula.Not final

    let final_dnf = Formula.polyhedra_dnf final_formula
                    |> Formula.split_disjunction
                    |> List.map Formula.split_conjunction
    let dnf_paths = [for clause in final_dnf -> initial :: path_formulae @ [Formula.conj clause]]

    let dnf_interpolants =
        // if we fail at some point we stop the recursion and return [None]
        // (this is where we are better then just doing 'List.map path_interpolant')
        let rec path_interpolants dnf_paths =
            match dnf_paths with
            | [] -> []
            | h::t ->
                let path_interpolant fs =
                    match InterpolantSequence.synthesis try_ignore_beginning distance invar_formulae fs with
                    | Some(interpolants) -> Some(List.map (Formula.alpha Var.unprime_var) interpolants)
                    | None -> None
                match path_interpolant h with
                | None -> [None]
                | interpolants -> interpolants::(path_interpolants t)
        path_interpolants dnf_paths
    assert (List.length dnf_interpolants > 0)

    if List.contains None dnf_interpolants then
        None
    else
        // take elementwise conjunction
        let cnt = 1 + List.length path_formulae
        assert (not <| List.contains false [for intps in dnf_interpolants -> List.length intps.Value = cnt])

        Some [
            for i in [0 .. cnt-1] ->
                Formula.conj [for intps in dnf_interpolants -> List.nth intps.Value i]
        ]

let find_path_interpolant pi initial final =
    let path_formulae = [for (_, fs, _) in pi -> Formula.conj fs]
    let fs = initial::path_formulae@[Formula.negate final]

    match InterpolantSequence.synthesis false 0 [] fs with
    | Some (intps) -> Some(List.map (Formula.alpha Var.unprime_var) intps)
    | None -> None

// find_unsat_path_interpolant is the same as 'find_path_interpolant pi Formula.truec Formula.falsec'
// without the first and last interpolants (Formula.truec and Formula.falsec respectively).
// makes some heuristics work better
let find_unsat_path_interpolant pi =
    let fs = [for (_, fs, _) in pi -> Formula.conj fs]

    match InterpolantSequence.synthesis true 0 [] fs with
    | Some (intps) -> Some(List.map (Formula.alpha Var.unprime_var) intps)
    | None -> None

let get_scc_rels_for_lex_rf_synth_from_trans (scc_transitions:Set<Set<int> * (int * command list * int)>) =
    let scc_commands =
           [ for (_, (_, cmds, _)) in scc_transitions do yield cmds ]
        |> Seq.concat

    let scc_vars =
           Programs.freevars scc_commands
        |> Set.filter (fun v -> not(Formula.is_instr_var v || Formula.is_disj_var v))

    let scc_rels =
           scc_transitions
        |> Set.map (fun (trans_idx, (k, cmds, k')) -> (trans_idx, k, path_to_relation [(k, cmds |> List.map Programs.const_subst, k')] scc_vars, k'))

    //Add an extra constant variable to get affine interpretations:
    let extra_pre_var : Var.var = Var.var (Formula.const_var bigint.One ^ "^0")
    let extra_post_var : Var.var = Var.var (Formula.const_var bigint.One ^ "^post")
    let affine_scc_rels =
           scc_rels
        |> Set.map (fun (idx, k, rel, k') -> (idx, k, Programs.add_const1_var_to_relation extra_pre_var extra_post_var rel, k'))
    (scc_vars.Add (Var.unprime_var extra_pre_var), scc_transitions, affine_scc_rels)

let get_scc_rels_for_lex_rf_synth_from_program (p:Programs.Program) (scc_nodes:Set<int>) (cp:int) =
    let scc_transitions =
           !p.active
        |> Set.map (fun trans_idx -> (Set.singleton trans_idx, p.transitions.[trans_idx]))
        |> Set.filter (fun (_, (k, _, k')) -> scc_nodes.Contains k && scc_nodes.Contains k')
        |> Programs.filter_out_copied_transitions cp
        |> Programs.chain_transitions (Set.remove cp scc_nodes)

    get_scc_rels_for_lex_rf_synth_from_trans scc_transitions
