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
//
//  Abstract:  Provides differnt filters for formulae
//  Author:    Maria Gorinova

module Microsoft.Research.T2.Filter

open Var
open Term
open Formula

let infinity = bigint 2147483647 //TODO: This is not infinity. Maybe use IntervalIntDom.Bound?


/// Filters redundant equalities in a formula.
/// Use before applying quantifier elimination
let redundant terms = 

    // formula_qelim fails to produce correct result if there are redundant equalities
    // in the conjunction. For example x <= 0 AND x' = x+y AND y' = y+z. 
    // The last conjunctive is redundant and the produced result is 
    // x <= 0 AND z <= -1 AND z >= 1 .
    // That is because y' = y+z is transformed to y'-y-z <= 0 AND y'-y-z >= 0.
    // Thus, after stripping the primes we get z <= 0 AND z >= 0. However, if we 
    // do forall elimination, we need that result negated, ergo z >= 1 OR z <= -1,
    // which is equivalent to z != 0 - a condition that doesn't have to 
    // necessary hold for the initial formula to be valid.
    //
    // Thus, filter formula with "filter_redundant" after applying the rest of the
    // procedure to filter the redundant equalities
    
    let result = ref []
    let flag = ref false

    for t in terms do
        flag := false
        for u in terms do
            match (t,u) with
            | (Le(e1, Const(c0)), Le(e2, Const(c0'))) when c0 = bigint.Zero && c0' = bigint.Zero ->
                let lhs = (Formula.clean_formula (Le(Add(e1, e2), Const(c0))))
                match lhs with
                | Ge(a, b) -> if((Term.try_eval a) = Some(c0) && (Term.try_eval b) = Some(c0)) then flag := true
                | Le(a, b) -> if((Term.try_eval a) = Some(c0) && (Term.try_eval b) = Some(c0)) then flag := true
                                  
        if(not !flag) then result := t::(!result)
    
    !result


/// For a formula f, it checks if rest_of_f => p for p being some subformula of f
/// If f = p AND q and q => p, then we can simplify f to q
let redundant_conjunction (f:formula) = 

    let disjs =  f |> Formula.split_disjunction |> ref
    let result = ref []

    let rec checker_conj (prev:formula list) (cur:formula) (next:formula list) =

        match next with
        | [] -> if (Formula.entails (Formula.conj (prev)) cur) then
                    prev
                else cur::prev
        | _ -> if (Formula.entails (Formula.conj (prev@next)) cur) then
                    checker_conj prev next.Head next.Tail
               else 
                checker_conj (cur::prev) next.Head next.Tail


    for d in !disjs do
        let c::cs = Formula.split_conjunction d
        //printfn "%s %s" (c).pp (Formula.conj cs).pp
        let chk = Formula.conj (List.rev (checker_conj [] c cs))
        if (not (Formula.unsat chk)) then result := chk::(!result) 

    Formula.disj !result


/// For a formula f, it checks if p => rest_of_f for p being some subformula of f
/// If f = p OR q and p => q, then we can simplify f to q
let redundant_disjunctions (f:formula) =

    let result_len = ref 0
    let disjs = ref (Formula.split_disjunction f)
    let result = ref []
    let len = ref (!disjs).Length

    let rec checker_disj (prev:formula list) (cur:formula) (next:formula list) =
        
        match next with
        | [] -> if (Formula.entails cur (Formula.disj (prev))) then
                    prev
                else cur::prev
        | _ -> if (Formula.entails cur (Formula.disj (prev@next))) then 
                    checker_disj prev next.Head next.Tail
               else checker_disj (cur::prev) next.Head next.Tail  

    result := !disjs
        
    while (!len > !result_len) do
        len := (!result).Length 
        try result := checker_disj [] ((!result).Head) ((!result).Tail) with
        | _ -> len := !result_len
        result_len := (!result).Length       

    Formula.disj !result


/// A heuristic that generalises formulas like 
/// x<0 AND x+y<0 AND x+2y<0 AND... to (in this case) y<=0 AND x<0
let generalise f:formula =
    // TODO: fix this as it will give error in some cases 
    // (e.g. there are cases in which it will assume incorrectly 
    // that given coefficients are increasing with time, but
    // there might be actually decreasing

    let monotone (coeff : bigint list) = 

        let rec constant list head = 
            match list with
            | [] -> true
            | x::xs -> if(x = head) then constant xs head else false

        let rec increasing list prev =
            match list with
            | [] -> true
            | c::cs -> if (c > prev) then increasing cs c else false
            
        let rec decreasing list prev =
            match list with
            | [] -> true
            | c::cs -> if (c < prev) then decreasing cs c else false   
         
        if constant coeff (List.head coeff) then bigint.Zero
        elif increasing coeff -infinity then bigint.One
        elif decreasing coeff infinity then bigint.MinusOne
        else bigint 2

    // each term in terms is >= 0
    let terms = Formula.split_conjunction f |> formulae_to_terms
    let vars = Formula.freevars f

    if List.length terms >= 3 then

        // flag marks if all the coefficients of vars in the sequence 
        // either stay the same, increase or decrease    
        let flag = ref true
        let incr_coeff_vars = ref []
        let reminder = ref (List.head terms)

        for v in vars do
            let coeff = ref []

            for t in terms do
                coeff := (Term.get_coefficient t v)::(!coeff)

            let m = monotone !coeff  
            if(m = bigint.One || m = bigint.MinusOne) then 
                incr_coeff_vars := (m,v)::(!incr_coeff_vars)
                reminder := Term.remove_var !reminder v

            elif(m = bigint.Zero && List.head !coeff <> bigint.Zero) then incr_coeff_vars := (m,v)::(!incr_coeff_vars)
            else flag := false
    
        let result = ref []    
              
        if(!flag) then

            for (m,v) in !incr_coeff_vars do
            
                // The conditions we generate here don't have to neccessarily be true
                // in order for the program to terminate, but there are some simple
                // rules for which it definitely terminates. Again, we are building an
                // underapproximation - it's important to findsome conditions for which
                // the program terminates, not all of them (as often that might involve
                // some infinite conjunctions)

                if(m = bigint.MinusOne) then result := (Le(Const(bigint.Zero), Var(v)))::(!result)
                elif(m = bigint.One) then result := (Le(Var(v), Const(bigint.Zero)))::(!result)               

            result := (Le(Const(bigint.Zero), !reminder))::(!result)
            Formula.conj !result
        
         else f
    else f      

