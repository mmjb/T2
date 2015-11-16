/////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      InterpolantSingle
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

module Microsoft.Research.T2.InterpolantSingle

open Formula
open SparseLinear
open Utils

///
/// Generate interpolant constraints for systems A<=0, B<=0.
/// Return pair (constraints, intp). 
/// Interpolant should be understood as intp<=0.
///
let private gen_system (A: LinearTerm list) (B: LinearTerm list) = 

    let A = simplify_as_inequalities A
    let B = simplify_as_inequalities B

    let lambda : Microsoft.Z3.ArithExpr list = [for a in A -> (upcast Z.fresh_var()) ]
    let mu : Microsoft.Z3.ArithExpr list = [for b in B -> (upcast Z.fresh_var()) ]
    

    let a_vars = Seq.concat (List.map (fun (m:Map<_,_>) -> m.Keys) A) |> Set.ofSeq
    let b_vars = Seq.concat (List.map (fun (m:Map<_,_>) -> m.Keys) B) |> Set.ofSeq

    let common_vars = (Set.intersect a_vars b_vars).Remove ONE

    let i = seq {for v in common_vars -> (v, Z.fresh_var())} |> Map.ofSeq

    let zero = Z.constant bigint.Zero

    let A_by_lambda = combine_with_z3_terms A (lambda)
    let B_by_mu = combine_with_z3_terms B mu


    //
    // if we don't introduce fresh var for delta, prover hangs on some tests
    //
    let delta = Z.fresh_var()
    let delta_expression = A_by_lambda.FindWithDefault ONE zero


    let constant = Z.add delta (B_by_mu.FindWithDefault ONE zero)

    let A_by_lambda = A_by_lambda.Remove ONE
    let B_by_mu = B_by_mu.Remove ONE


    let constraints = 
        [for v in lambda @ mu -> Z.ge v zero] @
        [for KeyValue(v, coeff) in A_by_lambda ->
            if common_vars.Contains v then
                Z.eq coeff i.[v]
            else
                Z.eq coeff zero
        ] @
        [Z.eq delta delta_expression] @
        [for KeyValue(v, coeff) in B_by_mu ->
            if common_vars.Contains v then
                Z.eq coeff (Z.neg i.[v])
            else
                Z.eq coeff zero
        ] @
        [Z.ge constant (Z.constant bigint.One)]
        
    (Z.conj constraints, i.Add(ONE, delta))




///
/// Return interpolant between two formulas
///
let private synthesis_base (pars : Parameters.parameters) (a : formula) (b : formula) =

    let A = a.ToLinearTerms()
    let B = b.ToLinearTerms()

    let (Phi, intp) = gen_system A B

    match Z.solve [ Phi ] with
    | None ->
        None
    | Some(m) ->
        let intp = Map.map (fun _ coeff -> Z.get_model_int m coeff) intp
        let intp = formula.OfLinearTerm intp
        if pars.print_interpolants then
            printf "Interpolant: %s\n" (Formula.pp intp)
        m.Dispose()
        Some(intp)


//
// Compute path interpolants.  Currently we do something a little silly: rather than computing all of the interpolants at
// once we try computing an interpolant in the middle of the path and then using that to cut down the problem into two.
// It would be better to compute them all at once with one Z3 call, we are working on that.
//
let private path_synthesis (pars : Parameters.parameters) fs =
    assert (fs <> [])
    Z.refreshZ3Context()

    // compute interpolant for the middle of the path first
    let rec bisect_intps (fs: Formula.formula list) =
        assert (not fs.IsEmpty)
        if fs.Length = 1 then
            Some []
        else
            assert (fs.Length >= 2)
            let left = List.take (fs.Length/2) fs
            let right = List.drop (fs.Length/2) fs
            match synthesis_base pars (Formula.conj left) (Formula.conj right) with
            | Some i ->
                let not_i = i |> Formula.Not |> Formula.simplify
                let left' = List.all_but_last left @ [Formula.And (not_i, List.last left)]
                match bisect_intps left' with
                | Some left_intps ->
                    let right' = Formula.And (i, List.head right) :: List.tail right
                    match bisect_intps right' with
                    | Some right_intps ->
                        Some (left_intps @ [i] @ right_intps)
                    | None -> None
                | None -> None
            | None -> None    

    let result = bisect_intps fs

    result



///
/// Compute path interpolants 
///
let synthesis (pars : Parameters.parameters) fs =
    //printf "Looking for interpolant for path: \n%s\n" (Formula.pp_list fs)
    match path_synthesis pars fs with
    | Some(intps) -> 
        if pars.check_interpolants then
           InterpolantSequence.check_interpolant fs intps
        Some(intps)
    | None -> 
        if Formula.unsat (Formula.conj fs) then
            dieWith "formula is unsat, but interpolant can't be found"
        else 
            None
              
