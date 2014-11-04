////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      z.fs
//
//  Abstract:
//
//      Interface to the Z3 decision procedure
//
//  Environment:
//
//
//  Notes:
//
//      * Z3 seems to slow down if you call it relentlessly.  To avoid this, we must reset the Z3 context from
//        time to time. Resetting the context after every call makes things awkward, as we're hoping to
//        construct complex Z3 terms first and then call the validity procedure a lot.  Thus, at startup we
//        build a context and provide clear(). clear() should not be called between the creation
//        of a Z3 term and the call to the validity checker.
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

module Z

open Microsoft.Z3
open Microsoft.FSharp.Math
open Utils

//
// Z3 setup Load up Z3.  Note: we need to dispose of z3 at the end.
//
let create_config () =
    let p = new System.Collections.Generic.Dictionary<string, string>()
    p.Add("MODEL", "true")
    p

let set_solver_parameters (z3 : Context) (solver : Solver) =
    let p = z3.MkParams()
    p.Add("soft_timeout", 10000u)
    solver.Parameters <- p
    Microsoft.Z3.Global.SetParameter("model_evaluator.completion", "true")

let p = create_config()
let mutable z3 = new Microsoft.Z3.Context(p)

//
// Reset Z3. See comment
//
let clear() =
    System.GC.SuppressFinalize z3
    z3.Dispose()
    let p = create_config()
    z3 <- new Microsoft.Z3.Context(p)
//
// Register clear() to be called during "downtime"
//
Utils.add_clear clear

let finished() = z3.Dispose()

//
// Arithmetic wrappers and overloading
//
type z3e = Expr

let make_type (z3:Context) = z3.MkIntSort ()

let constant (i:bigint) = z3.MkNumeral(string(i), make_type z3) :?> ArithExpr
let constantInt (i:int) = z3.MkNumeral(i, make_type z3) :?> ArithExpr

let add a b = z3.MkAdd(a,b)
let sub a b = z3.MkSub(a,b)
let mul a b = z3.MkMul(a,b)
let neg z = mul (constant (bigint.MinusOne)) z

let eq q1 q2 = z3.MkEq(q1,q2)
let ge q1 q2 = z3.MkGe(q1,q2)
let lt q1 q2 = z3.MkLt(q1,q2)
let le q1 q2 = z3.MkLe(q1,q2)
let gt q1 q2 = z3.MkGt(q1,q2)
let ite x y z = z3.MkITE(x,y,z)

let mk_not q1 = z3.MkNot(q1)
let neq q1 q2 = mk_not (eq q1 q2)
let implies q1 q2 = z3.MkImplies(q1,q2)

let var (name:string) =  z3.MkIntConst(name)
let bool_var (name:string) = z3.MkBoolConst(name)
let symbol (name:string) =  z3.MkSymbol(name)

let conj (xs : BoolExpr list) = z3.MkAnd(Array.ofList xs)
let conj2 f1 f2 = z3.MkAnd (f1, f2)
let disj (xs : BoolExpr list)  = z3.MkOr(Array.ofList xs)
let disj2 f1 f2 = z3.MkOr (f1, f2)

let make_constraint f (v:RowVector<Expr>) =
    let vl = Vector.Generic.fold (fun x y -> y::x) [] (v.Transpose) in
    let cs = List.map f vl in
    conj cs

let rec solve_more_rec k l (solver : Solver) =
    match l with
    | [] -> None
    | (q::qs) ->
        solver.Push()
        try
            solver.Assert([| q |])
            match solver.Check() with
            | Status.SATISFIABLE ->
                let model = solver.Model
                match solve_more_rec (k+1) qs solver with
                            | None -> Some (k, model)
                            | other -> model.Dispose();  other
            | Status.UNSATISFIABLE -> None
            | Status.UNKNOWN -> raise (System.TimeoutException "z3 timeout")
            | _ -> die()
        finally
            solver.Pop()

let sat_opt q =
    Stats.start_time "Z3"
    let solver = z3.MkSimpleSolver()
    set_solver_parameters z3 solver

    solver.Push()
    solver.Assert(q)
    let result =
        match solver.Check() with
        | Status.SATISFIABLE -> Some true
        | Status.UNSATISFIABLE -> Some false
        | _ -> None
    solver.Pop()
    solver.Dispose()
    Stats.end_time "Z3"

    result

let sat q =
    match sat_opt q with
    | Some true -> true
    | Some false -> false
    | None -> dieWith("z3 returned 'unknown'")

let unsat_core assertions =
    !Utils.check_timeout ()
    let assumptions = Array.init (Array.length assertions) (fun _ -> z3.MkBoolConst ("unsat_core") :> Expr)

    let solver = z3.MkSimpleSolver()
    set_solver_parameters z3 solver
    solver.Push()
    try
        let make_assertion assertion (assumption : Expr) = solver.Assert (z3.MkOr (assertion, z3.MkNot (assumption :?> BoolExpr)))
        Array.iter2 make_assertion assertions assumptions
        let core = ref null

        Stats.start_time "Z3"
        let result = solver.Check(assumptions)
        //(model, assumptions, proof, core)
        Stats.end_time "Z3"

        match result with
        | Status.SATISFIABLE ->
            None
        | Status.UNSATISFIABLE ->
            let result =
                [
                    for i=0 to (Array.length assertions - 1) do
                        yield (Array.exists (fun x -> x = assumptions.[i]) !core)
                ]
            Some result
        | _ -> die ()
    finally
        solver.Pop ()
        solver.Dispose ()

let valid q = not (sat ([| mk_not q |]))

///
/// Return Some(k, model) for largest k such that formulae 0..k are SAT.
/// In case such k does not exist (that is, should be -1), return None.
///
/// Typical use is to call it with a list [f, h1, h2...], where f is formula
/// we absolutely want to satisfy, and h1, h2... are heuristics we'd like to
/// satisfy if possible.
///
let solve_k fs =
    (!Utils.check_timeout)()
    Stats.start_time "Z3"
    let solver = z3.MkSimpleSolver()
    solver.Push()
    let result = try (try solve_more_rec 0 fs solver with :? System.TimeoutException as e -> Stats.inc_stat "solve_k, Timeout"; raise e) finally Stats.end_time "Z3"

    match result with
    | Some (k, _) -> Stats.inc_stat ("solve_k, k=" + k.ToString())
    | None -> Stats.inc_stat "solve_k, None"
    solver.Pop()
    solver.Dispose()

    result

///
/// Satisfy as much formulae in the beginning of the list as possible.
/// If list is empty or first formula is UNSAT, return None.
///
/// Typical use is to call it with a list [f, h1, h2...], where f is formula
/// we absolutely want to satisfy, and h1, h2... are heuristics we'd like to
/// satisfy if possible.
///
let solve fs = match solve_k fs with
               | None -> None
               | Some(_,m) -> Some(m)

let fresh_var _ = var (Gensym.fresh_var())
let fresh_bool_var _ = bool_var (Gensym.fresh_var())
let fresh_var_list n : ArithExpr list = List.map (fun v -> upcast fresh_var v) [for i in [1 .. n] do yield i]
let fresh_vars c = RowVector.Generic.init c fresh_var

let get_model_int (m:Model) x =
        match (m.Eval x) with
        | :? IntNum as i -> i.BigInteger
        | :? IntExpr -> bigint.Zero
        | _ -> dieWith "Z.get_model_int failed"
let get_model_int_opt (m:Model) x =
        match (m.Eval x) with
        | :? IntNum as i -> Some i.BigInteger
        | :? IntExpr -> Some bigint.Zero
        | _ -> None

let get_model_string (m:Model) x = (m.Eval x).ToString()

let get_model_bool_opt (m:Model) x =
    match (m.Eval x).BoolValue with
    | Z3_lbool.Z3_L_TRUE -> Some true
    | Z3_lbool.Z3_L_FALSE -> Some false
    | _ -> None

///
/// Z3 term simplificaton
///
let simplify (t : Expr) = t.Simplify()

///
/// SAT-solve and then print the model.  Useful for debugging.
///
let print_sat_model q vs =
    match solve q with
    | None -> printfn "No model possible"
    | Some m ->
        let model = List.map (fun v -> (v,get_model_int m v)) (Set.toList vs)
        printfn "%A" model
        m.Dispose()
