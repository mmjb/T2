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

module Microsoft.Research.T2.Symex

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
    let needed_vars = System.Collections.Generic.HashSet()

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

    for (_, cs, _) in pi @ relevantCmds do
        for c in cs do
            needed_vars.AddAll (needed_vars_from_cmd c)
            track_dependency c

    //Now do a fixpoint thing where we recursively compute all needed variables
    let mutable queue = List.ofSeq needed_vars
    let mutable relevant = Set.empty
    while not (queue).IsEmpty do
        let var = (queue).Head
        queue <- (queue).Tail
        if not <| Set.contains var relevant then
            relevant <- (relevant).Add var
            if depends_on.ContainsKey var then
                for v in depends_on.[var] do
                    queue <- v::queue

    //Filter everything that's not needed out:
    let relevant = relevant // rebind to use in closure
    let is_relevant c =
        match c with
        | Assign(_, v, _) when Set.contains v relevant -> true
        | Assign _ -> false
        | Assume _ -> true

    let filter_out c =
        if is_relevant c then
            [c]
        else
            []

    pi |> List.map (fun (l1, cs, l2) -> (l1, List.collect filter_out cs, l2))

let find_path_interpolant_old (pars : Parameters.parameters) try_ignore_beginning distance invar_formulae pi initial final =
    let path_formulae = [for (_, fs, _) in pi -> Formula.conj fs]
    let final_formula = Formula.Not final

    let final_dnf = 
        final_formula.PolyhedraDNF().SplitDisjunction()
        |> List.map (fun (f : formula) -> f.SplitConjunction())
    let dnf_paths = [for clause in final_dnf -> initial :: path_formulae @ [Formula.conj clause]]

    let dnf_interpolants =
        // if we fail at some point we stop the recursion and return [None]
        // (this is where we are better then just doing 'List.map path_interpolant')
        let rec path_interpolants dnf_paths =
            match dnf_paths with
            | [] -> []
            | h::t ->
                let interpolationProcedure = if pars.seq_interpolation then InterpolantSequence.synthesis else (fun pars _ _ _ -> InterpolantSingle.synthesis pars)
                let path_interpolant fs =
                    match interpolationProcedure pars try_ignore_beginning distance invar_formulae fs with
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

let find_path_interpolant (pars : Parameters.parameters) pi initial final =
    let path_formulae = [for (_, fs, _) in pi -> Formula.conj fs]
    let fs = initial::path_formulae@[Formula.negate final]

    let interpolationProcedure = if pars.seq_interpolation then InterpolantSequence.synthesis else (fun pars _ _ _ -> InterpolantSingle.synthesis pars)
    match interpolationProcedure pars false 0 [] fs with
    | Some (intps) -> Some(List.map (Formula.alpha Var.unprime_var) intps)
    | None -> None

// find_unsat_path_interpolant is the same as 'find_path_interpolant pi Formula.truec Formula.falsec'
// without the first and last interpolants (Formula.truec and Formula.falsec respectively).
// makes some heuristics work better
let find_unsat_path_interpolant (pars : Parameters.parameters) pi =
    let fs = [for (_, fs, _) in pi -> Formula.conj fs]

    let interpolationProcedure = if pars.seq_interpolation then InterpolantSequence.synthesis else (fun pars _ _ _ -> InterpolantSingle.synthesis pars)
    match interpolationProcedure pars true 0 [] fs with
    | Some (intps) -> Some(List.map (Formula.alpha Var.unprime_var) intps)
    | None -> None

let get_scc_rels_for_lex_rf_synth_from_trans (scc_transitions:Set<Set<int> * Transition>) =
    let scc_commands =
           [ for (_, (_, cmds, _)) in scc_transitions do yield cmds ]
        |> Seq.concat

    let scc_vars =
           Programs.freevars scc_commands
        |> Set.filter (fun v -> not(Formula.is_instr_var v))

    let scc_rels =
           scc_transitions
        |> Set.map (fun (trans_idx, (k, cmds, k')) -> (trans_idx, k, Programs.cmdPathToRelation [(k, cmds |> List.map Programs.const_subst, k')] scc_vars, k'))

    //Add an extra constant variable to get affine interpretations:
    let extra_pre_var : Var.var = Var.var (Formula.const_var bigint.One + "^0")
    let extra_post_var : Var.var = Var.var (Formula.const_var bigint.One + "^post")
    let affine_scc_rels =
           scc_rels
        |> Set.map (fun (idx, k, rel, k') -> (idx, k, Programs.add_const1_var_to_relation extra_pre_var extra_post_var rel, k'))
    (scc_vars.Add (Var.unprime_var extra_pre_var), scc_transitions, affine_scc_rels)

let get_scc_rels_for_lex_rf_synth_from_program (pars : Parameters.parameters) (p:Programs.Program) (scc_nodes:Set<int>) (cp : int option) =
    let mutable scc_transitions = Set.empty
    let scc_nodes_without_copy_nodes = System.Collections.Generic.HashSet()
    for (k, cmds, k') in p.Transitions do
        if scc_nodes.Contains k && scc_nodes.Contains k' then
            let is_no_copy_transition =
                   cmds
                |> Seq.filter
                    (function | Assume(_,_) -> false
                              | Assign(_,var,term) -> (Formula.is_copied_var var) && term.Equals(Term.constant 1))
                |> Seq.isEmpty
            if is_no_copy_transition then
                scc_nodes_without_copy_nodes.Add k' |> ignore

    let scc_transitions =
        p.TransitionsWithIdx
        |> Seq.filter (fun (_, (k, _, k')) ->    scc_nodes_without_copy_nodes.Contains k 
                                              && scc_nodes_without_copy_nodes.Contains k')
        |> Seq.map (fun (trans_idx, (k, cmds, k')) -> (Set.singleton trans_idx, (k, cmds, k')))
        |> List.ofSeq
                          
    let chainableLocs = if cp.IsSome then Set.remove cp.Value scc_nodes else scc_nodes
    let scc_transitions =
        match pars.export_cert with // Disable chaining in certification mode
        | Some _ -> scc_transitions |> Set.ofList
        | None -> Programs.chain_transitions chainableLocs scc_transitions

    get_scc_rels_for_lex_rf_synth_from_trans scc_transitions