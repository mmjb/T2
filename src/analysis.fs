////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      analysis.fs
//
//  Abstract:
//
//      Various program analysis tools
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

module Microsoft.Research.T2.Analysis

open Term
open Programs

//
// Cheap analysis for convex constraints of the form k<=v<=k
//
let constants p =
    let changed = ref Set.empty

    let locs = Programs.locations p

    let basic =  Map.empty
    let true_inv = Some(basic)
    let false_inv = None

    let inv = ref Map.empty
    for l in locs do
        inv := Map.add l false_inv !inv
    done

    inv := Map.add !p.initial true_inv !inv

    changed := Set.singleton !p.initial

    let union s t =
       match (s,t) with
       | (None,None) -> None
       | (None,t) ->  t
       | (s,None) -> s
       | (Some(m),Some(m')) -> Some(Map.filter (fun x y -> match Map.tryFind x m with
                                                           | None -> false
                                                           | Some(a) -> a = y
                                                ) m')

    let equal s t = s = t

    let exec s c =
        let update_val m v n = Map.add v n m
        let remove_val m v  = Map.remove v m

        let execute_cmd s c =
            match c with
            | Assume(_,e) when Formula.is_true_formula e  -> s
            | Assume(_,_)           -> s
            | Assign(_,v,Const(k))  -> update_val s v k
            | Assign(_,v,_)         -> remove_val s v
        match s with
        | None ->  Some(execute_cmd basic c)
        | Some(m) -> Some(execute_cmd m c)

    let symbolic_execution T s = List.fold exec s T

    while not (Set.isEmpty !changed) do
        let loc = (!changed).MinimumElement
        changed := Set.remove loc !changed
        let next = Programs.transitions_from p loc
        let s = Map.find loc !inv
        List.iter (fun (T,loc') ->
            let old_inv = Map.find loc' !inv
            let s' = symbolic_execution T s
            let new_inv = union old_inv s'
            if not (equal old_inv new_inv) then
                changed := Set.add loc' !changed
                inv := Map.add loc' new_inv !inv
            ) next
    done

    let tbl = ref Map.empty
    Map.iter (fun loc s ->
       match s with
       | None -> tbl := Map.add loc Map.empty !tbl
       | Some(s') -> tbl := Map.add loc s' !tbl
    ) !inv
    !tbl

//
// Variable liveness analysis
//
let liveness p alwaysLive =
    let locs = Programs.locations p

    let live = ref Map.empty
    for l in locs do
        live := Map.add l alwaysLive !live

    let rec kill_cmd cmd =
       match cmd with
       | Assign(_,v,_) when Formula.is_disj_var v ->
           let cmds = Map.find v !p.abstracted_disjunctions |> Set.ofList
           Set.map kill_cmd cmds |> Set.unionMany |> Set.add v
       | Assign(_,v,_) -> Set.singleton v
       | Assume(_,_) -> Set.empty

    let rec gen_cmd cmd =
       match cmd with
       | Assign(_,v,t) when Formula.is_disj_var v ->
           let cmds = Map.find v !p.abstracted_disjunctions |> Set.ofList
           Set.map gen_cmd cmds |> Set.unionMany |> Set.union (Term.freevars t)
       | Assign(_,_,t) ->   Term.freevars t
       | Assume(_,e) -> Formula.freevars e

    let next live cmd = Set.union (gen_cmd cmd) (Set.difference live (kill_cmd cmd))
    let exec live  = List.rev >> List.fold next live //(List.rev cmds)

    let changed = ref locs
    while not (Set.isEmpty !changed) do
        let loc = (!changed).MaximumElement
        changed := Set.remove loc !changed
        let nexts = Programs.transitions_from p loc |> Set.ofList
        let Ts = Set.map fst nexts
        let next_locs = Set.map snd nexts
        let prev_locs = Programs.transitions_to p loc |> Set.ofList |> Set.map snd
        let live_in = Map.find loc !live
        let live_out = Set.fold (fun live_out succ -> Set.union live_out (Map.find succ !live)) Set.empty next_locs
        let live_in' = Set.fold (fun li T -> Set.union li (exec live_out T)) Set.empty Ts
        let live' = Set.union live_in live_in'
        if live'.Count <> live_in.Count then
            changed := Set.union prev_locs !changed
            live := Map.add loc live' !live
    done
    !live

let exec_cmd (int_dom:IIntAbsDom.IIntAbsDom) cmd =
    match cmd with
        | Assume (_, f)    -> int_dom.assume f
        | Assign (_, v, t) -> int_dom.assign v t

let path_invariant stem cycle =
    let oct = Octagon2.Oct.create

    for cmd in stem do
        exec_cmd oct cmd

    oct.tight_closure

    let mutable finished = false
    while not finished do
        let new_oct = oct.clone
        for cmd in cycle do
            exec_cmd new_oct cmd
        new_oct.tight_closure


        finished <- not <| oct.widen new_oct
        // Note that we don't do tight_closure with oct.
        // Mine warns against it in his paper!

    oct.to_formula

let program_absint start_pp start_intdom transitions command_filter =
    let outgoing_trans = new System.Collections.Generic.Dictionary<int, System.Collections.Generic.HashSet<Programs.command list * int>>()
    for (_, (k, trans, k')) in transitions do
        if not(outgoing_trans.ContainsKey k) then
            outgoing_trans.Add(k, new System.Collections.Generic.HashSet<Programs.command list * int>())
        outgoing_trans.[k].Add((trans, k')) |> ignore

    let pp_to_intdom = new System.Collections.Generic.Dictionary<int, IIntAbsDom.IIntAbsDom>()
    let todo = new System.Collections.Generic.Queue<int>()
    todo.Enqueue start_pp
    pp_to_intdom.Add(start_pp, start_intdom)

    /// Note the new integer values for program position pp. Returns true if this changed the current knowledge
    let set_or_widen pp intdom =
        if pp_to_intdom.ContainsKey pp then
            pp_to_intdom.[pp].widen intdom
        else
            pp_to_intdom.Add(pp, intdom)
            true

    while todo.Count > 0 do
        let cur_pp = todo.Dequeue()
        let cur_intdom = pp_to_intdom.[cur_pp]
        if outgoing_trans.ContainsKey cur_pp then
            for (cmds, target_pp) in outgoing_trans.[cur_pp] do
                let new_intdom = cur_intdom.clone
                for cmd in (command_filter cmds) do
                    exec_cmd new_intdom cmd
                new_intdom.tight_closure
                let widened = set_or_widen target_pp new_intdom
                if widened && not(todo.Contains target_pp) then
                    todo.Enqueue(target_pp)

    pp_to_intdom

let get_interval_analysis (p:Programs.Program) (e : Formula.formula)=
    let pp_to_interval =
            program_absint
                !p.initial
                IntervalIntDom.Intervals.create
                (p.transitions |> Seq.map (fun (k,c,k') -> (k, (k,c,k'))))
                id
    let pp_to_seq = pp_to_interval |> Seq.sortBy (fun (KeyValue(k,_)) -> k)
    let pp_to_form = pp_to_seq |> Seq.map(fun x -> (x.Key,x.Value.to_formula))
    let to_check = pp_to_form |> Seq.filter(fun (_,y) ->  not(Formula.entails y e) || Formula.unsat (Formula.conj[y;e]))
                                    |> Seq.map(fun (x,_) -> x)

    to_check

let rec weakest_precondition (pi : (int*Programs.command*int) list) =

    match pi with
    | (_,Programs.Assume(_,f),_)::tail ->   //let vars = Formula.freevars f
                                            //if vars.Contains Formula.subcalls_var || vars.Contains Formula.subrets_var then
                                            if Formula.contains_instr_var f then
                                                (weakest_precondition tail)
                                            else
                                                Formula.disj[(Formula.negate(f));(weakest_precondition tail)]
    | (_,Programs.Assign(_,v,t),_)::tail -> let subvar_t x = if v = x then t else Var(x)
                                            if Term.contains_nondet t then
                                                let f = Formula.polyhedra_dnf (weakest_precondition tail) |> Formula.split_disjunction
                                                let f = f |> List.map(fun x -> SparseLinear.eliminate_var v (SparseLinear.formula_to_linear_terms x))
                                                f |> List.map(fun x -> x |> List.map (fun y -> SparseLinear.linear_term_to_formula y) |> Formula.conj) |> Formula.disj
                                            else
                                                let f = Formula.subst subvar_t (weakest_precondition tail)
                                                f
    | [] -> Formula.falsec
