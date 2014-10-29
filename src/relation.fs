////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      relation.fs
//
//  Abstract:
//
//      Datatype and operations on relations
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

module Relation

open Utils
open Term
open Formula

/// (formula, prevars, postvars)
type relation = Rel of formula * Var.var list * Var.var list

let make cn vs vs' = Rel(cn, vs, vs')

let rel2pp (Rel(cn,vs,vs')) =
    let s = Formula.pp cn
    let m = [for v, v' in List.zip vs vs' ->
             sprintf "%s |-> %s" (Var.pp v) (Var.pp v')]
    let m = System.String.Join(", ", m)

    sprintf "Rel %s\nwhere\n%s\n" m s

let unsat (Rel(cn,_,_)) = unsat cn
let subrel (Rel(cn1,vs1,vs1')) (Rel(cn2,vs2,vs2')) =
    if (not (vs1=vs2 && vs1'=vs2')) then die()
    Formula.entails cn1 cn2
let intersect (Rel(cn1,vs1,vs1')) (Rel(cn2,vs2,vs2')) =
    assert (vs1=vs2)
    assert (vs1'=vs2')
    Rel(Formula.conj[cn1;cn2],vs1,vs1')
let union (Rel(cn1,vs1,vs1')) (Rel(cn2,vs2,vs2')) =
    assert(vs1=vs2)
    assert(vs1'=vs2')
    Rel(Formula.disj[cn1;cn2],vs1,vs1')

let prevars (Rel(_,vs,_)) = vs
let postvars (Rel(_,_,vs)) = vs
let formula (Rel(cn,_,_)) = cn

///
/// List of additional variables mentioned in the relation formula
///
let existentials (Rel(cn,vs,vs')) =
        let vars_set = Set.ofList vs
        let vars_set' = Set.ofList vs'
        let all_vars = Formula.freevars cn
        all_vars - (vars_set + vars_set') |> Set.toList

let relation_to_linear_terms rel =
    // these are intermediate SSA vars. We want to eliminate them, so
    // that relation only involve prevars and postvars.
    let evars = existentials rel

    let mutable ts = SparseLinear.formula_to_linear_terms (formula rel)

    for var in evars do
        ts <- SparseLinear.eliminate_var var ts
    ts

let pre2post rel =
   let vs = prevars rel
   let vs' = postvars rel
   List.map2 (fun x y -> (x,Var(y))) vs vs'

let post2pre rel =
   let vs = prevars rel
   let vs' = postvars rel
   List.map2 (fun x y -> (x,Var(y))) vs' vs

let simplify (Rel(rel,vs,vs')) =
    let rel' = Formula.simplify rel
    Rel(rel',vs,vs')

/// Takes in a relation, and replaces the postvar indices with "post" throughout
let standardise_postvars (rel:relation) =
    let orig_postvars = postvars rel
    let new_postvars = List.map (fun v -> (Var.unprime_var v)+"^post") orig_postvars

    let orig_formula = formula rel |> ref
    let new_formula =
        for postvar in orig_postvars do
            let f v = if v=postvar then Term.var ((Var.unprime_var v)+"^post") else Term.var v
            orig_formula := Formula.subst f !orig_formula
        !orig_formula

    make new_formula (prevars rel) new_postvars
