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

module Microsoft.Research.T2.Z

open Microsoft.Z3
open Microsoft.FSharp.Math
open Utils

// A parameter (dictionary) object we use to configure the Z3 Solver instance
let z3Config =
    let p = new System.Collections.Generic.Dictionary<string, string>()
    p.Add("MODEL", "true")
    p

/// The actual z3 context through we which pipe all of our work.
/// It should be disposed at the end of a run.
// TODO: This should be wrapped into a context, to be thread-safe.
let mutable z3Context : Microsoft.Z3.Context = null
let getZ3Context () =
    new Microsoft.Z3.Context(z3Config)
let refreshZ3Context () =
    if z3Context <> null then
        System.GC.SuppressFinalize z3Context
        z3Context.Dispose()
    z3Context <- getZ3Context()
refreshZ3Context()

// Register clear() createZ3Context when we "clear" the prover state. This dumps
// internal z3 state and provides a fresh solver.
Utils.add_clear refreshZ3Context

/// Create a simple z3 SMT Solver. Caller has to take care of disposal of the object.
let getSolver (solverTimeout : uint32 option) =
    let solver = z3Context.MkSimpleSolver()
    let p = z3Context.MkParams()
    match solverTimeout with
    | Some timeout -> p.Add("timeout", timeout)
    | None -> p.Add("timeout", 10000u)
    solver.Parameters <- p
    Microsoft.Z3.Global.SetParameter("model_evaluator.completion", "true")
    solver

let finished() = z3Context.Dispose()

////////// Arithmetic wrappers
let defaultType () = z3Context.MkIntSort ()

let constant (i:bigint) = z3Context.MkNumeral(string(i), defaultType()) :?> ArithExpr
let constantInt (i:int) = z3Context.MkNumeral(i, defaultType()) :?> ArithExpr

let add a b = z3Context.MkAdd(a,b)
let sub a b = z3Context.MkSub(a,b)
let mul a b = z3Context.MkMul(a,b)
let neg z = mul (constant (bigint.MinusOne)) z

let eq q1 q2 = z3Context.MkEq(q1,q2)
let ge q1 q2 = z3Context.MkGe(q1,q2)
let lt q1 q2 = z3Context.MkLt(q1,q2)
let le q1 q2 = z3Context.MkLe(q1,q2)
let gt q1 q2 = z3Context.MkGt(q1,q2)
let ite x y z = z3Context.MkITE(x,y,z)

let mk_not q1 = z3Context.MkNot(q1)
let neq q1 q2 = mk_not (eq q1 q2)
let implies q1 q2 = z3Context.MkImplies(q1,q2)

let var (name:string) =  z3Context.MkIntConst(name)
let bool_var (name:string) = z3Context.MkBoolConst(name)
let symbol (name:string) =  z3Context.MkSymbol(name)

let conj (xs : BoolExpr list) = z3Context.MkAnd(Array.ofList xs)
let conj2 f1 f2 = z3Context.MkAnd (f1, f2)
let disj (xs : BoolExpr list)  = z3Context.MkOr(Array.ofList xs)
let disj2 f1 f2 = z3Context.MkOr (f1, f2)

////////// The actual querying routines:
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
                //Try to get a better model, if possible. Otherwise, return ours:
                match solve_more_rec (k+1) qs solver with
                | None ->
                    Some (k, model)
                | Some betterModel ->
                    model.Dispose()
                    Some betterModel
            | Status.UNSATISFIABLE -> None
            | Status.UNKNOWN -> raise (System.TimeoutException "z3 timeout")
            | _ -> die()
        finally
            solver.Pop()

let sat_opt q =
    Stats.startTimer "Z3 - Satisfiability"

    let result =
        try
            use solver = getSolver None
            solver.Assert(q)
            match solver.Check() with
            | Status.SATISFIABLE -> Some true
            | Status.UNSATISFIABLE -> Some false
            | _ -> None
        finally
            Stats.endTimer "Z3 - Satisfiability"

    result

let sat q =
    match sat_opt q with
    | Some true -> true
    | Some false -> false
    | None -> dieWith("z3 returned 'unknown'")

let unsat_core assertions =
    !Utils.check_timeout ()
    let assumptions = Array.init (Array.length assertions) (fun _ -> z3Context.MkBoolConst ("unsat_core") :> Expr)

    use solver = getSolver None
    let make_assertion assertion (assumption : Expr) = solver.Assert (z3Context.MkOr (assertion, z3Context.MkNot (assumption :?> BoolExpr)))
    Array.iter2 make_assertion assertions assumptions
    let core = ref null

    Stats.startTimer "Z3 - Unsat Core"
    let result =
        try
            solver.Check(assumptions)
        finally
            Stats.endTimer "Z3 - Unsat Core"

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

let valid q = not (sat ([| mk_not q |]))

///
/// Return Some(k, model) for largest k such that formulae 0..k are SAT.
/// In case such k does not exist (that is, should be -1), return None.
///
/// Typical use is to call it with a list [f, h1, h2...], where f is formula
/// we absolutely want to satisfy, and h1, h2... are heuristics we'd like to
/// satisfy if possible.
///
let solve_k solverTimeout fs =
    (!Utils.check_timeout)()
    Stats.startTimer "Z3 - Satisfiability (opt)"

    use solver = getSolver solverTimeout
    let result =
        try
            try
                solve_more_rec 0 fs solver
            with
            :? System.TimeoutException as e ->
                Stats.incCounter "Z3 - Timeout"
                None
        finally
            Stats.endTimer "Z3 - Satisfiability (opt)"

    result

///
/// Satisfy as much formulae in the beginning of the list as possible.
/// If list is empty or first formula is UNSAT, return None.
///
/// Typical use is to call it with a list [f, h1, h2...], where f is formula
/// we absolutely want to satisfy, and h1, h2... are heuristics we'd like to
/// satisfy if possible.
///
let private internalSolve solverTimeout fs =
    match solve_k solverTimeout fs with
    | None -> None
    | Some(_,m) -> Some(m)

let solve fs = internalSolve None fs
let quickSolve fs = internalSolve (Some 500u) fs

let fresh_var _ = var (Gensym.fresh_var())
let fresh_bool_var _ = bool_var (Gensym.fresh_var())
let fresh_var_list n : ArithExpr list = List.map (fun v -> upcast fresh_var v) [for i in [1 .. n] do yield i]

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