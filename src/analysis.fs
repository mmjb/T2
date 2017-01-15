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
let constants (p : Programs.Program) =
    let mutable changed = Set.empty

    let basic = Map.empty
    let true_inv = Some basic
    let false_inv = None

    let mutable inv = Map.empty
    for l in p.Locations do
        inv <- Map.add l false_inv inv
    done

    inv <- Map.add p.Initial true_inv inv

    changed <- Set.singleton p.Initial

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

    while not (Set.isEmpty changed) do
        let loc = (changed).MinimumElement
        changed <- Set.remove loc changed
        let next = p.TransitionsFrom loc
        let s = Map.find loc inv
        for (_, (_, T, loc')) in next do
            let old_inv = Map.find loc' inv
            let s' = symbolic_execution T s
            let new_inv = union old_inv s'
            if not (equal old_inv new_inv) then
                changed <- Set.add loc' changed
                inv <- Map.add loc' new_inv inv

    let mutable tbl = Map.empty
    for KeyValue (loc, s) in inv do
        match s with
        | None -> tbl <- Map.add loc Map.empty tbl
        | Some s' -> tbl <- Map.add loc s' tbl
    tbl

//
// Variable liveness analysis
//
let liveness (p : Programs.Program) (alwaysLive : Set<Var.var>) =
    let live = System.Collections.Generic.Dictionary()
    for l in p.Locations do
        live.[l] <- alwaysLive

    let collect_live_vars_backwards live_vars_at_end cmds =
        //Gets variable defined in this command
        let get_assigned_var cmd =
           match cmd with
           | Assign(_, v, _) -> Set.singleton v
           | Assume(_, _)    -> Set.empty

        //Gets variables used by this command.
        //Note: If we don't care about a variable, we don't care about what gets assigned to it.
        let get_used_vars live_vars cmd =
           match cmd with
           | Assign (_, v, t) when Set.contains v live_vars -> Term.freevars t
           | Assign _                                       -> Set.empty
           | Assume (_, e)                                  -> Formula.freevars e

        //Backwards collection: At each step, remove variables that are assigned from set of live variables, add all variables used in expressions / guards
        let handle_one_cmd cmd live = Set.union (get_used_vars live cmd) (Set.difference live (get_assigned_var cmd))
        List.foldBack handle_one_cmd cmds live_vars_at_end

    //Queue of locations that still need to be processed
    let mutable queue = p.Locations
    while not (Set.isEmpty queue) do
        let loc = queue.MaximumElement
        queue <- Set.remove loc queue
        //Propagate backwards from all direct successors of loc
        let mutable new_live_at_loc = alwaysLive
        for (_, (_, cmds, target_loc)) in p.TransitionsFrom loc do
            new_live_at_loc <- Set.union new_live_at_loc (collect_live_vars_backwards live.[target_loc] cmds)
        if new_live_at_loc.Count <> live.[loc].Count then
            let prev_locs = p.TransitionsTo loc |> Seq.map (fun (_, (prev, _, _)) -> prev) |> Set.ofSeq
            queue <- Set.union prev_locs queue
            live.[loc] <- new_live_at_loc
    live

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
    let outgoing_trans = new System.Collections.Generic.Dictionary<int, System.Collections.Generic.HashSet<Programs.Command list * int>>()
    for (k, trans, k') in transitions do
        if not(outgoing_trans.ContainsKey k) then
            outgoing_trans.Add(k, new System.Collections.Generic.HashSet<Programs.Command list * int>())
        outgoing_trans.[k].Add((trans, k')) |> ignore

    let pp_to_intdom = new System.Collections.Generic.Dictionary<int, IIntAbsDom.IIntAbsDom>()
    let todo = new System.Collections.Generic.Queue<int>()
    todo.Enqueue start_pp
    pp_to_intdom.Add(start_pp, start_intdom)

    /// Note the new integer values for program position pp. Returns true if this changed the current knowledge
    let set_or_widen pp (intdom : IIntAbsDom.IIntAbsDom) =
        match pp_to_intdom.TryGetValue pp with
        | (true, pp_intdom) ->
            pp_intdom.widen intdom
        | (false, _) -> 
            pp_to_intdom.[pp] <- intdom
            true

    while todo.Count > 0 do
        let cur_pp = todo.Dequeue()
        let cur_intdom = pp_to_intdom.[cur_pp]
        if outgoing_trans.ContainsKey cur_pp then
            for (cmds, target_pp) in outgoing_trans.[cur_pp] do
                let new_intdom = cur_intdom.clone()
                for cmd in (command_filter cmds) do
                    exec_cmd new_intdom cmd
                new_intdom.tight_closure
                let widened = set_or_widen target_pp new_intdom
                if widened && not(todo.Contains target_pp) then
                    todo.Enqueue(target_pp)

    pp_to_intdom