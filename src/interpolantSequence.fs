/////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      InterpolantSequence (interpolantSequence.fs)
//
//  Abstract:
//
//       Farkas lemma based interpolant synthesis via Farkas lemma
//
//  Notes:
//
//      * This code builds up matrices of Z3 constraints.  To reduce overhead
//        we're operating directly on the Z3 constraints, not constraints from
//        formula.fs.
//      * Interpolants used primarily in reachability.fs. They get used a lot,
//        so performance here is something worth not ignoring.
//      * Sound for integers, but not complete (e.g., when \exists t . 2t = x would appear in the interpolant)
//      * A weakness of this procedure is that it doesn't support disjunction without a reduction to
//        disjunctive normal form, which isn't so nice. This forces T2 to make everything convex and then
//        try to work around the problem, which leads to some difficulties
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

module Microsoft.Research.T2.InterpolantSequence

/// all_implications: if set to true we generate constraints for all backwards implications.
/// Otherwise see number_of_implications.
let all_implications = ref false

/// number_of_implications: when all_implications is set to false this variable determines how many
/// implications to generate.
let number_of_implications = ref 5

/// number_of_invars:
let number_of_invars = ref 1

open SparseLinear
open Utils

let check_interpolant fs intps =
    let mutable prev = List.head fs
    for f, intp in List.zip fs (intps@[Formula.falsec]) do
        assert (Formula.entails (Formula.conj [prev; f]) intp)
        prev <- intp

let private print_interpolant fs intps =
    Printf.printf "-------------------\nInterpolants\n"
    let rec print_intps fs_x_intps prev_intp =
        match fs_x_intps with
        | [] -> ()
        | (f,intp)::t ->
            Printf.printf "\n\n"
            Printf.printf "{%s}\n" (Formula.pp prev_intp)
            Printf.printf "  %s\n" (Formula.pp f)
            Printf.printf "{%s}\n" (Formula.pp intp)
            print_intps t intp
    print_intps (List.zip fs (intps@[Formula.falsec])) Formula.truec

///
/// Generate interpolant constraints for a list of systems S, each system is of form A<=0.
/// Return (common constraints, constraints for non-strict case, interpolants, heuristics constraints).
/// Interpolants should be understood as intp<=0.
/// try_ignore_beginning: if true, the heuristics constraints will be a list of constraints enforcing the first lambdas to 0 (i.e. ignore the first nodes on the path)
let private gen_system (pars : Parameters.parameters) try_ignore_beginning remove_uncommon_vars (S: LinearTerm list list) =

    // simplify each element in S
    let S = List.map simplify_as_inequalities S

    let zero = Z.constantInt 0

    // for each system of S, create a vector of fresh vars the size of number of constrains in that system
    let (lambdas : Microsoft.Z3.ArithExpr list list ) = [for A in S -> [for _ in A -> (upcast Z.fresh_var())]]
    // epsilon lets the constant of the first invar be as small as possible making the invariants (all of them) as loose as possible
    let epsilon : Microsoft.Z3.ArithExpr = upcast Z.fresh_var()

    // a list of accumulative sums of S by lambdas (these are actually the interpolants)
    let accumulative_S_by_lambdas =
        // multiply each system A in S by its corresponding lambda
        let S_by_lambdas = List.map2 combine_with_z3_terms S lambdas
        // add epsilon to the first ONE
        let S_by_lambdas =
            match S_by_lambdas with
            | [] -> []
            | h::t ->
                match Map.tryFind ONE h with
                | None -> (Map.add ONE epsilon h)::t
                | Some term -> (Map.add ONE (Z.add term epsilon) h)::t

        let sum_vectors A B =
            let add map (var, term) =
                match Map.tryFind var map with
                | None -> Map.add var term map
                | Some resTerm -> Map.add var (Z.add resTerm term) map
            List.fold add A (Map.toList B)

        match S_by_lambdas with
        | [] -> []
        | h::t -> List.scan sum_vectors h t

    // extract the last element of accumulative_S_by_lambdas and save it as last_sum
    let constant, last_sum, accumulative_S_by_lambdas =
        match List.rev accumulative_S_by_lambdas with
        | [] -> zero, Map.empty, []
        | (h::t) -> h.FindWithDefault ONE zero , h.Remove ONE, List.rev t

    let phi =
        [
            yield Z.le epsilon zero
            for v in List.concat lambdas -> Z.ge v zero
            for _, coeff in last_sum.Items -> Z.eq coeff zero
        ]

    // intps_heuristics is a list of extra constraints (might not be sat) that try to enforce
    // we try to ignore the last few constraints (but not the very last)
    let intps_heuristics =
        if try_ignore_beginning then
            if pars.seq_interpolation_ignore_last_constr then
                // from the end (but not last)
                let rev_lambdas =
                    if !all_implications then List.rev lambdas |> List.tail
                    else List.take (!number_of_implications + 1) (List.rev lambdas) |> List.tail
                [for lambda in rev_lambdas -> Z.conj [for lam in lambda -> Z.eq lam zero]]
            else
                // from the beginning
                let lambdas =
                    if !all_implications then lambdas
                    else List.take !number_of_implications lambdas
                [for lambda in lambdas -> Z.conj [for lam in lambda -> Z.eq lam zero]]
        else []

    // when doing backwards entailment (i.e. invar(v) |= invar(w)) we need to remove the irelevant parts of the interpolants
    let accumulative_S_by_lambdas =
        if remove_uncommon_vars then
            let common_vars =
                let s_vars = [for A in S -> List.fold (fun prev (term: LinearTerm) -> Set.union prev (Set.ofSeq term.Keys)) Set.empty A |> Set.add ONE]
                let accumulative_union = List.scan Set.union Set.empty s_vars |> List.tail |> List.rev |> List.tail |> List.rev
                let reverse_accumulative_union = List.scanBack Set.union s_vars Set.empty |> List.tail |> List.rev |> List.tail |> List.rev
                List.map2 Set.intersect accumulative_union reverse_accumulative_union
            let keep_vars vars i =
                Map.filter (fun var _ -> Set.contains var vars) i
            List.map2 keep_vars common_vars accumulative_S_by_lambdas
        else accumulative_S_by_lambdas

    Z.conj phi, Z.eq constant (Z.constantInt 1), accumulative_S_by_lambdas, intps_heuristics

let private get_intps_model m intps =
    let model intp = Map.map (fun _ coeff -> Z.get_model_int m coeff) intp
    List.map (model >> linear_term_to_formula) intps

///
/// Compute path interpolants.
///
let private synthesis_base (pars : Parameters.parameters) try_ignore_beginning fs =
    assert (fs <> [])

    let (phi, case1, intps, intps_heuristics) = gen_system pars try_ignore_beginning false fs

    match Z.solve ((Z.conj2 phi case1) :: intps_heuristics) with
    | None ->
        None
    | Some(m) -> try Some (get_intps_model m intps) finally m.Dispose()

///
/// try to find interpolant such that v |= w, where v is the last interpolant and w is 'entail_distance' from last
/// if one inequality interpolation does not work we try to add invariants to support it
///
let private synthesis_base_with_entailment (pars : Parameters.parameters) fs entail_distance invar_fs =
    assert (fs <> [])

    // unprime the invar i
    let unprime i = [for (var,term) in Map.toList i -> (if var = ONE then ONE else Var.unprime_var var), term] |> Map.ofList

    // recursivly try to synthesise by adding more invariants
    let rec synthesis_with_invars n phis intpss v_intps w_intps =
        if n <= 0 then None
        else

        // NOTE: the following is exponantial in 'n'
        // generate the constraints for v |= w
        let entails =
            let v_sums =
                let sum_intps intps =
                    let sum intp1 intp2 =
                        let add map (var,term) =
                            match Map.tryFind var map with
                            | None -> Map.add var term map
                            | Some resTerm -> Map.add var (Z.add resTerm term) map
                        List.fold add intp1 (Map.toList intp2)
                    match intps with
                    | [] -> Map.empty
                    | h::t -> List.fold sum h t

                // make all posible sums of v invars combinations
                let rec make intps comb_intps =
                    match intps with
                    | [] -> [sum_intps comb_intps]
                    | (h::t) ->
                        let res1 = make t comb_intps
                        let res2 = make t (h::comb_intps)
                        res1@res2
                make v_intps []
            let gen_implication i1 i2 =
                let zero = Z.constantInt 0
                let vars (i1: Map<string,Microsoft.Z3.ArithExpr>) (i2: Map<string,Microsoft.Z3.ArithExpr>) = Seq.append i1.Keys i2.Keys |> Set.ofSeq |> Set.remove ONE
                Z.conj [
                           for var in (vars i1 i2) -> Z.eq (i1.FindWithDefault var zero) (i2.FindWithDefault var zero)
                           yield (Z.ge (i1.FindWithDefault ONE zero) (i2.FindWithDefault ONE zero))
                       ]
            let gen_entail w_intp =
                Z.disj [for intp in v_sums -> gen_implication intp w_intp]
            let false_intp = Map.add ONE (Z.constantInt 1) Map.empty
            let result = Z.conj [for intp in w_intps -> gen_entail intp]
            Z.disj [
                       yield result
                       for intp in v_intps -> gen_implication intp false_intp
                   ]

        let solution = try Z.solve [Z.conj (entails::phis)] with :? System.TimeoutException as e -> if e.Message = "z3 timeout" then None else reraise ()
        match solution with
        | None ->
            let (new_phi, new_case1, new_intps, _) = gen_system pars false true invar_fs
            let new_intps = List.all_but_last new_intps

            let phis = (Z.conj2 new_phi new_case1)::phis
            let intpss = new_intps::intpss

            let v_intps =
                assert ((new_intps.Length - 1) >= 0)
                let new_v_intp = unprime (List.last new_intps)
                new_v_intp::v_intps

            let w_intps =
                assert ((new_intps.Length - entail_distance - 1) >= 0)
                let new_w_intp = unprime new_intps.[new_intps.Length - entail_distance - 1]
                new_w_intp::w_intps
            synthesis_with_invars (n-1) phis intpss v_intps w_intps
        | Some m ->
            try
                let get_intpss_model m intpss =
                    let intpss = List.map (get_intps_model m) intpss

                    let intps_collection =
                        match intpss with
                        | [] -> []
                        | (h::t) ->
                            let h = List.map (fun i -> [i]) h
                            let collect_intps intps_collection intps =
                                List.map2 (fun list i -> i::list) intps_collection intps
                            List.fold collect_intps h t

                    List.map Formula.conj intps_collection

                Some (get_intpss_model m intpss)
            finally m.Dispose()

    // we initiate the recursion with the real interpolation constraints
    let (phi, case1, intps, _) = gen_system pars false true fs
    let v_intp =
        assert ((intps.Length - 1) >= 0)
        unprime (List.last intps)
    let w_intp =
        assert ((intps.Length - entail_distance - 1) >= 0)
        unprime intps.[intps.Length - entail_distance - 1]
    synthesis_with_invars (!number_of_invars + 1) [Z.conj2 phi case1] [intps] [v_intp] [w_intp]

let private path_synthesis (pars : Parameters.parameters) try_ignore_beginning entail_distance invar_fs fs =
    assert (fs <> [])
    Z.clear() // speed things up

    let ltfs = List.map formula_to_linear_terms fs
    let invar_ltfs = List.map formula_to_linear_terms invar_fs

    let result =
        if entail_distance = 0 then synthesis_base pars try_ignore_beginning ltfs
        else synthesis_base_with_entailment pars ltfs entail_distance invar_ltfs

    if pars.print_interpolants && result.IsSome then print_interpolant fs result.Value
    if pars.check_interpolants && result.IsSome then check_interpolant fs result.Value

    result

///
/// Compute path interpolants
///
let synthesis (pars : Parameters.parameters) try_ignore_beginning entail_distance invar_fs fs =
    //Printf.printf "Looking for interpolant for path: \n%s\n" (Formula.pp_list fs)

    match path_synthesis pars try_ignore_beginning entail_distance invar_fs fs with
    | Some intps ->
        Some intps
    | None ->
        if entail_distance = 0 && Formula.unsat (Formula.conj fs) then
            // this can actually happen, interpolation is not complete for Integers!
            dieWith "formula is unsat, but interpolant can't be found"
        else
            None
