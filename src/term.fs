////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      term.fs
//
//  Abstract:
//
//      Representation for arithmetic terms
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


module Microsoft.Research.T2.Term

open Utils

[<StructuredFormatDisplayAttribute("{pp}")>]
type term =
    | Nondet | Const of bigint | Var of Var.var | Neg of term | Add of term * term
    | Sub of term * term | Mul of term * term


    member self.pp =
        // For instance, term t1*t2 has strength 2.
        // Outside force that is trying to tear the term apart.
        // For instance, unary minus exerts force 3 on underlying term.
        // To protect itself, term encloses itself in braces, so we get -(t1*t2).

        let protect strength force s =
            if strength >= force then s else "(" + s + ")"

        let rec term2pp' force e =
            match e with
            | Nondet -> "nondet()"
            | Const(i) -> string(i)
            | Var(v) -> Var.pp v
            | Neg(e) -> "-" + term2pp' 3 e
            | Add(Const(c1), e2) when c1 = bigint.Zero ->
                protect 1 force (term2pp' 1 e2)
            | Add(e1, Const(c2)) when c2 = bigint.Zero ->
                protect 1 force (term2pp' 1 e1)
            | Add(e1, Mul(Const(c), e22)) when c = bigint.MinusOne ->
                protect 1 force (term2pp' 1 e1 + "-" + term2pp' 2 e22)
            | Add(e1, Mul(Const(c), e22)) when c < bigint.MinusOne ->
                protect 1 force (term2pp' 1 e1 + "-" + term2pp' 2 (Mul(Const(-c), e22)))
            | Add(e1,e2) -> protect 1 force (term2pp' 1 e1 + "+" + term2pp' 1 e2)
            | Sub(e1,e2) -> protect 1 force (term2pp' 1 e1 + "-" + term2pp' 2 e2) // force on second arg is 2 because we want to get a-(b+c) instead of a-b+c
            | Mul(e1,e2) when e1 = Const(bigint.MinusOne) -> protect 2 force ("-" + term2pp' 2 e2)
            | Mul(e1,e2) when e1 = Const(bigint.One) -> protect 2 force (term2pp' 2 e2)
            | Mul(e1,e2) -> protect 2 force (term2pp' 2 e1 + "*" + term2pp' 2 e2)

        term2pp' 0 self

    override self.ToString () = self.pp

    member self.prefix_pp =
        match self with
            | Nondet -> "nondet()"
            | Const(i) -> string(i)
            | Var(v) -> Var.pp v
            | Neg(e) -> sprintf "(- %s)" e.prefix_pp
            | Add(e1,e2) -> sprintf "(+ %s %s)" e1.prefix_pp e2.prefix_pp
            | Sub(e1,e2) -> sprintf "(- %s %s)" e1.prefix_pp e2.prefix_pp
            | Mul(e1,e2) -> sprintf "(* %s %s)" e1.prefix_pp e2.prefix_pp

    member self.clause_pp varPP =
        match self with
        | Nondet -> "_"
        | Const(i) -> i.ToString()
        | Var(v) -> varPP v
        | Neg(e) -> sprintf " -%s" (e.clause_pp varPP)
        | Add(e1,e2) -> sprintf "(%s + %s)" (e1.clause_pp varPP) (e2.clause_pp varPP)
        | Sub(e1,e2) -> sprintf "(%s - %s)" (e1.clause_pp varPP) (e2.clause_pp varPP)
        | Mul(e1,e2) -> sprintf "(%s * %s)" (e1.clause_pp varPP) (e2.clause_pp varPP)

    member self.isVar =
        match self with
            | Var(_) -> true
            | _ -> false

let nondet = Nondet
let constant (x:int) = Const (bigint x)
let var x = Var(x)
let neg x = Neg(x)
let add x y = Add(x,y)
let sub x y = Sub(x,y)
let mul x y = Mul(x,y)

//
// Evaluate predicates on terms
//
let rec contains f tm =
    if f tm then true
    else match tm with
         | Neg(tm1) -> contains f tm1
         | Sub(tm1,tm2)
         | Add(tm1,tm2)
         | Mul(tm1,tm2) -> contains f tm1 || contains f tm2
         | _ -> false

let contains_nondet = contains (function Nondet -> true | _ -> false)

let rec freevars e =
    match e with
    | Nondet -> Set.empty
    | Const(_) -> Set.empty
    | Var(v) -> Set.singleton v
    | Neg(e) -> freevars e
    | Sub(e1,e2) -> Set.union (freevars e1) (freevars e2)
    | Add(e1,e2) -> Set.union (freevars e1) (freevars e2)
    | Mul(e1,e2) -> Set.union (freevars e1) (freevars e2)

let rec eval e =
    match e with
    | Nondet -> dieWith "Can't evaluate nondet()"
    | Const(i) -> i
    | Var(_) -> dieWith "Can't evaluate vars"
    | Neg(e) ->  bigint.Negate (eval e)
    | Sub(e1,e2) -> eval e1 - eval e2
    | Add(e1,e2) -> eval e1 + eval e2
    | Mul(e1,e2) -> eval e1 * eval e2

let rec try_eval e =
    match e with
    | Nondet -> None
    | Const(i) -> Some(i)
    | Var(_) -> None
    | Neg(e) -> maybe { let! v = try_eval e
                        return (bigint.Negate v)
                      }
    | Sub(e1,e2) -> maybe { let! v = try_eval e1
                            let! v' = try_eval e2
                            return (v-v')
                          }
    | Add(e1,e2) -> maybe { let! v = try_eval e1
                            let! v' = try_eval e2
                            return (v+v')
                          }
    | Mul(e1,e2) -> maybe { let! v = try_eval e1
                            let! v' = try_eval e2
                            return (v*v')
                          }

let rec subst env e =
    match e with
    | Var v -> env v
    | Const _
    | Nondet -> e
    | Neg e ->  Neg(subst env e)
    | Sub(e1,e2) -> Sub(subst env e1, subst env e2)
    | Add(e1,e2) -> Add(subst env e1, subst env e2)
    | Mul(e1,e2) -> Mul(subst env e1, subst env e2)

/// Alpha-renaming
let rec alpha m t = subst (m >> Var) t

let rec z3 e =
    match e with
    | Const(i) -> Z.constant i
    | Var(v) -> upcast Z.var (Var.pp v)
    | Neg(e) -> Z.neg (z3 e)
    | Sub(e1,e2) -> Z.sub (z3 e1) (z3 e2)
    | Add(e1,e2) -> Z.add (z3 e1) (z3 e2)
    | Mul(e1,e2) -> Z.mul (z3 e1) (z3 e2)
    | Nondet -> die()
