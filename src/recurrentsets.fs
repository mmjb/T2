////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      RecurrentSets
//
//  Abstract:
//
//      Proving non-termination
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


module Microsoft.Research.T2.RecurrentSets

open SparseLinear
open Symex
open Utils

///
/// Find state that repeats itself after <count> iterations of <cycle>.
/// Return disjunction of conjunctions, characterizing state before <cycle>,
/// after one iteration of <cycle>, after two iterations of <cycle> etc.
///
let recurrent_state (pars : Parameters.parameters) vars stem cycle count =
    Log.log pars <| sprintf "Nontermination: Checking for state repetition after %i iterations" count
    let formulae = ref []
    let var_maps = ref []
    let var_map = ref Map.empty
    for segment in stem :: List.replicate count cycle do
        let f, new_var_map = path_to_transitions_and_var_map segment !var_map
        let f = project_transitions_to_formulae f |> Formula.conj
        var_map := new_var_map
        var_maps := !var_maps @ [!var_map]
        formulae := !formulae @ [f]

    let constr =
        Formula.conj [
            yield! !formulae
            for KeyValue(var, new_index) in !var_map do
                let old_index = get_var_index (!var_maps).Head var
                if  old_index < new_index then
                    yield Formula.Eq (
                        Term.var (Var.prime_var var old_index),
                        Term.var (Var.prime_var var new_index) )
        ]

    match Z.solve_k [Formula.z3 constr] with
    | Some(_, model) ->
        let set =
            Formula.disj [
                for var_map in List.all_but_last !var_maps do
                    yield Formula.conj [
                        for var in vars do
                            let value = Z.get_model_int_opt model (Z.var (Var.prime_var var (get_var_index var_map var)))
                            if value.IsSome then
                                yield Formula.Eq (Term.var var, Term.Const value.Value)
                    ]
            ]
        model.Dispose()
        Some set
    | None ->
        None

///
/// Following Sect. 4.2 of "Automated Detection of Non-Termination and NullPointerExceptions for Java Bytecode"
///

/// Obtain loop condition from cycle path in terms 
/// of variables at the beginning of the cycle
let separate_conditions_and_assignments prevars conjuncts =
    //I'm evil, using that the formula in the relation is built up step by step by an in-order run through the commands on the path.
    //As we have SSA, every equality with a newly appearing variable is an assignment and everything else is a condition:
    let seen_vars = ref prevars
    let constraints = ref []
    let assignments = ref []

    let handle_conj c =
        let c_vars = Formula.freevars c
        if Set.forall (fun k -> Set.contains k !seen_vars) c_vars then
            //we've seen every var before -> it's a constraint! Filter out the trivial stuff, though
            match c with
                | Formula.Le(c1, c2)
                | Formula.Ge(c1, c2)
                | Formula.Eq(c1, c2) when c1 = c2 -> ()
                | _ -> constraints := c::!constraints
        else
            //something new. assignment! However, filter out x^k == x^k things introduced by a = nondet()
            match c with 
            | Formula.Eq(c1, c2) when c1 = c2 -> ()
            | _ ->
                //We have to be careful here: If the coefficient on the fresh variable is not 1, then we can be in trouble.
                //Example: assume(2t = x), where t is fresh. Then, we have to parse this as a constraint, and not as an assignment:
                let freshVars = Set.removeAll c_vars !seen_vars
                let formulas_as_linterms = c |> SparseLinear.formula_to_linear_terms
                let hasNonUnitCoeff linterm v =
                    match Map.tryFind v linterm with
                    | Some i -> i > bigint.One || i < bigint.MinusOne
                    | None -> false
                if List.exists (fun linterm -> Set.exists (fun v -> hasNonUnitCoeff linterm v) freshVars) formulas_as_linterms then
                    constraints := c::!constraints
                else
                    assignments := c::!assignments
                seen_vars := Set.addAll !seen_vars c_vars

    Seq.iter handle_conj conjuncts
        
    (!constraints, !assignments)

let recurrent_set_from_path_conditions (pars : Parameters.parameters) stem cycle =
    Log.log pars <| sprintf "Nontermination: Checking for recurrent set constructed from constraints on counterexample cycle."

    //Get formula representation of the cycle, and a map of used variables / prime indices
    let cycle_formulas, varMap = path_to_transitions_and_var_map cycle Map.empty
    let cycle_formulas = cycle_formulas |> List.concatMap (fun (_, cs, _) -> cs)
    let prevars = varMap.Keys |> Seq.map (fun v -> Var.prime_var v 0) |> Set.ofSeq

    //Get path invariant for this CEx:
    let stem = List.concatMap (fun (_, cs, _) -> cs) stem
    let cycle = List.concatMap (fun (_, cs, _) -> cs) cycle
    let invariant = Analysis.path_invariant stem cycle

    //Reassemble things like x <= y, y <= x to equalities (for our heuristic splitting assignments / constraints).
    //Use foldBack because we need to keep the order of assignments stable for our heuristic.
    let cycle_formulas =
        List.foldBack
            (fun next_conj seen ->
                match next_conj with
                | Formula.Le(c1, c2) ->
                    let swapped_le = Formula.Le(c2, c1)
                    if List.contains swapped_le seen then
                        Formula.Eq(c1, c2)::(List.filter ((<>) swapped_le) seen)
                    else
                        next_conj::seen
                | _ ->
                    next_conj::seen
            )
            cycle_formulas
            []

    let constraints, assignments = separate_conditions_and_assignments prevars cycle_formulas
    let constraints = Formula.conj constraints
    let assignments = Formula.conj assignments

    // rename invariant vars to prevars
    let invariant = Formula.alpha (fun v -> Var.prime_var v 0) invariant

    // rename all variables to fresh names for second iteration
    let alpha_for_second_iteration v =
        let prime_idx = Var.get_prime_idx v
        let unprimed_v = Var.unprime_var v
        Var.prime_var unprimed_v (prime_idx + Map.findWithDefault unprimed_v 0 varMap)

    let constraints_2nd = Formula.alpha alpha_for_second_iteration constraints
    let assignments_2nd = Formula.alpha alpha_for_second_iteration assignments

    let exit_after_2nd_iteration = 
        Formula.conj 
            [ invariant
            ; constraints
            ; assignments
            ; Formula.negate constraints_2nd
            ; assignments_2nd
            ]

    (*
    Log.log <| sprintf "Invariant %A" invariant
    Log.log <| sprintf "1st round.\n  Assign: %A\n  Constr: %A" assignments constraints 
    Log.log <| sprintf "2nd round.\n  Assign: %A\n  Constr: %A" assignments_2nd (Formula.negate constraints_2nd) 
    *)

    // build invariant_renamed && constraints && assignments && not(constraints_renamed) && assignments_renamed to see if we exit after 2nd iteration
    if Formula.unsat exit_after_2nd_iteration then
        // If unsat, eliminate non-pre vars from constraints, rename pre-vars to just vars, return as recurrent set
        let recurrent_set_terms = ref (constraints |> formula_to_linear_terms)
        for var in varMap.Keys do
            for i in 1..(Map.find var varMap) do
                let var_prime = Var.prime_var var i
                recurrent_set_terms := eliminate_var var_prime !recurrent_set_terms
                recurrent_set_terms := simplify_as_inequalities !recurrent_set_terms

        let recurrent_set =
            Formula.And(
                invariant |> Formula.alpha Var.unprime_var, 
                List.map linear_term_to_formula !recurrent_set_terms |> Formula.conj |> Formula.alpha Var.unprime_var)

        Some recurrent_set
    else
        None

///
/// Return formula characterizing recurrent set (at the beginning of the cycle)
/// Optimistically calling this "synthesize" assuming that someday it will be
/// based on some smart technology
///
let synthesize (pars : Parameters.parameters) stem cycle (tryOneElementSets:bool) =
    let result = ref None

    let clean_commands cmds =
        cmds
        |> List.map (fun c -> Programs.const_subst c)

    let stem = List.map (fun (l, cmds, l') -> (l, clean_commands cmds, l')) stem
    let cycle = List.map (fun (l, cmds, l') -> (l, clean_commands cmds, l')) cycle

    let vars = Programs.freevars [for _, cmds, _ in cycle@stem do for cmd in cmds -> cmd]
    if tryOneElementSets then
        for i in 1..2 do
            if (!result).IsNone then
                result := recurrent_state pars vars stem cycle i

                if (!result).IsSome then
                    Stats.incCounter (sprintf "T2 - Looping nontermination after %i iterations" i)

    if (!result).IsNone then
        result := recurrent_set_from_path_conditions pars stem cycle

    !result
