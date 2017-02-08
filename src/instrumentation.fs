////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      instrumentation.fs
//
//  Abstract:
//
//       * Does program modifications for safety-based iterative proofs.
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


module Microsoft.Research.T2.Instrumentation
open Utils
open System.Collections.Generic
open Formula
open Var
open SafetyInterface
type Dictionary<'Key, 'Value> = System.Collections.Generic.Dictionary<'Key, 'Value>

let FINAL_LOC_LABEL = Programs.CutpointRFCheckLocation "final_loc"

//This is a data structure to keep all the relevant information about the search for lexicographic RFs
type LexicographicInfo =
    {
        //
        //STANDARD LEXICOGRAPHIC STUFF
        //

        ///a map from each cp to the order of relations being used currently
        mutable partial_orders : Map<int,Relation.relation list>

        ///a map from each cp to any lexicographic solutions we found in the past, but did not instrument. Last in first out
        mutable past_lex_options : Map<int, ((Formula.formula * Formula.formula * Formula.formula) list * Relation.relation list) list>

        //
        //INITIAL CONDITION STUFF
        //

        ///a map from each cp to a bool describing whether we are currently doing the "detect initial condition" improvement
        mutable cp_init_cond : Map<int,bool>

        ///a map from each cutpoint to a map.
        ///the map is from a counter to the index location of the counter's lex checkers
        mutable cp_rf_init_cond : Map<int,Map<int,int list>>

        ///is the counter identity of the path just found
        mutable current_counter : int

        ///map from cp to map.
        ///the map is from counters to current partial order for that counter
        mutable partial_orders_init_cond : Map<int,Map<int,Relation.relation list>>

        //
        //UNROLLING STUFF
        //

        ///a map from cp to a bool describing whether we are currently doing the "unrolling" improvement
        mutable cp_unrolling : Map<int,bool>

        ///a map from cp to the current number of iterations we're unrolling. Note it starts off at 2 for all cps.
        mutable cp_current_iter : Map<int,int>

        ///a map from cp to the index of the transition that contains the guard
        mutable cp_iter_guard : Map<int,int>

        //
        //POLYRANKING STUFF
        //

        ///a map from cp to whether we're currently finding polyranking fns for this cutpoint. Starts as false, then switches to true as necessary
        mutable cp_polyrank : Map<int,bool>

    }

//initialises lex_info
let init_lex_info (pars : Parameters.parameters) (cutpoints : Set<int>) =

    {
        partial_orders= [for cp in cutpoints -> (cp,[])] |> Map.ofList
        past_lex_options = [for cp in cutpoints -> (cp,[])] |> Map.ofList

        cp_init_cond = [for cp in cutpoints -> (cp,false)] |> Map.ofList
        cp_rf_init_cond = Map.empty
        current_counter = -1
        partial_orders_init_cond = [for cp in cutpoints -> (cp,Map.empty)]|>Map.ofList

        cp_unrolling = [for cp in cutpoints -> (cp,false)] |> Map.ofList
        cp_current_iter = [for cp in cutpoints -> (cp,2)] |> Map.ofList
        cp_iter_guard = Map.empty

        cp_polyrank = [for cp in cutpoints -> (cp,false)] |> Map.ofList

    }


///////////////////////////////////////////////////////////////////////////////
//////// Helper functions instrumenting RFs into the program graph ////////////
///////////////////////////////////////////////////////////////////////////////

///Returns true if cmds contains assume(copied_cp<1)
let contains_copied_lt_1 cp (cmds:Programs.Command list)=
    let copy = Formula.took_snapshot_var cp
    let mutable found = false
    for cmd in cmds do
        match cmd with
        | Programs.Assume(_,Formula.Lt(Term.Var(v),Term.Const c)) when c = bigint.One && (v=copy) ->
            found <- true
        | _ -> ()
    found

///Returns true if cmds contains copied_cp:=1
let contains_copied_gets_1 cp (cmds:Programs.Command list)=
    let copy = Formula.took_snapshot_var cp
    let mutable found = false
    for cmd in cmds do
        match cmd with
        | Programs.Assign(_,v,Term.Const c) when c = bigint.One && (v=copy) ->
            found <- true
        | _ -> ()
    found

///Takes in the indexes of the transitions that are lexicographic checkers, deletes them, and returns start and end node of the old check transition (so that you can stuff new checkers in there)
let delete_lex_checkers (lex_checkers : int list) (p : Programs.Program) =
    let (first_check_node,_,_) = p.GetTransition (List.head lex_checkers)
    let (_,_,last_check_node) = p.GetTransition (List.last lex_checkers)

    //Delete all the old lexicographic checkers from the program
    for checker in lex_checkers do
        p.RemoveTransition checker

    (first_check_node, last_check_node)

///Replaces a list of old lexicographic checkers by a new list
let replace_lex_rf_checkers p old_checker_trans_ids number_of_checkers (ith_checker_formulas: int -> formula list) =
    //remove old lex checkers for this counter
    let (k, k') = delete_lex_checkers old_checker_trans_ids p

    //Now we insert new lexicographic RF checkers from k to k'
    let checker_nodes = k::[for _ in 1..(number_of_checkers - 1) -> p.NewLocation Programs.CutpointRFCheckLocation]@[k']
    let new_checker_trans_ids =
        [ for i in 0 .. number_of_checkers - 1 do
              for trans in ith_checker_formulas i do
                  yield p.AddTransition
                            checker_nodes.[i]
                            [Programs.assume (Formula.Not(trans))]
                            checker_nodes.[i + 1]
        ]
    (k, new_checker_trans_ids)

let make_lex_RF_ith_check_component (rf_check_formulas : (formula * formula * formula) list) i =
    [
        let mutable j = 0
        for (decr_check_formula, non_incr_check_formula, bnd_check_formula) in rf_check_formulas do
            if i = j then
                yield decr_check_formula // i-th RF actually decreases
            if j <= i then
                yield bnd_check_formula // current and all earlier RFs are bounded from below
            if j < i then
                yield non_incr_check_formula// all earlier RFs are not increasing
            j <- j + 1
    ]

//Instruments a lexicographic RF to p_final
let instrument_lex_RF (pars : Parameters.parameters) cp (rf_check_formulas : (formula * formula * formula) list) found_lex_rfs (cp_rf_lex:Dictionary<int, int list>) (p_final:Programs.Program) (safety : SafetyProver) lex_info =
    let doing_init_cond = (lex_info.cp_init_cond).[cp]

    //Standard lexicographic RFs:
    if not doing_init_cond then
        assert(cp_rf_lex.ContainsKey(cp))

        //cp_rf_lex supplies the index (in p_final.transitions) of all lexicographic checkers, in correct order
        let old_checker_trans_ids = cp_rf_lex.[cp]
        found_lex_rfs := !found_lex_rfs |> Map.remove cp |> Map.add cp rf_check_formulas
        let (first_checker_node, new_lex_checker_trans_ids) = replace_lex_rf_checkers p_final old_checker_trans_ids rf_check_formulas.Length (make_lex_RF_ith_check_component rf_check_formulas) 
        cp_rf_lex.[cp] <- new_lex_checker_trans_ids
        safety.ResetFrom first_checker_node

    //We are instrumenting the Lex RF under a particular initial condition for the cp:
    else
        //Which initial condition did the path we just found represent?
        let counter = lex_info.current_counter

        //map from counters to the index locations of the counter's lex checkers
        let counters_to_checkers = (lex_info.cp_rf_init_cond).[cp]
        let old_checker_trans_ids = counters_to_checkers.[counter]
        let (first_checker_node, new_lex_checker_trans_ids) = replace_lex_rf_checkers p_final old_checker_trans_ids rf_check_formulas.Length (make_lex_RF_ith_check_component rf_check_formulas) 
        let new_counter_checkers_map = Map.add counter new_lex_checker_trans_ids counters_to_checkers
        lex_info.cp_rf_init_cond <- Map.add cp new_counter_checkers_map lex_info.cp_rf_init_cond
        safety.ResetFrom first_checker_node

    if pars.dottify_input_pgms then
        Output.print_dot_program p_final "input__instrumented_lex_RF.dot"

//Instruments a lexicographic polyranking function to p_final.
let instrument_poly_RF (pars : Parameters.parameters) cp (poly_checkers:Formula.formula list list) (cp_rf_lex:Dictionary<int, int list>) (p_final:Programs.Program) (safety : SafetyProver) =
    assert(cp_rf_lex.ContainsKey(cp))

    //cp_rf_lex supplies the index (in p_final.transitions) of all lexicographic checkers, in correct order
    //Here we extract the first and last node, k and k'
    let old_checker_trans_ids = cp_rf_lex.[cp]
    let ith_trans_formula i = poly_checkers.[i]
    let (first_checker_node, new_lex_checker_trans_ids) = replace_lex_rf_checkers p_final old_checker_trans_ids poly_checkers.Length ith_trans_formula
    cp_rf_lex.[cp] <- new_lex_checker_trans_ids

    safety.ResetFrom first_checker_node
    if pars.dottify_input_pgms then
        Output.print_dot_program p_final "input__instrumented_poly_lex_RF.dot"

///Fetches the past lex option at the head of the queue for failure_cp
let switch_to_past_lex_RF (pars : Parameters.parameters) lex_info failure_cp =
    //Take the lex RF at the head of the queue out
    let past_lex_options = (lex_info.past_lex_options).[failure_cp]
    let new_lex_WF = past_lex_options.Head
    lex_info.past_lex_options <- Map.add failure_cp past_lex_options.Tail lex_info.past_lex_options

    let (lex_RF, new_partial_order) = new_lex_WF
    lex_info.partial_orders <- Map.add failure_cp new_partial_order lex_info.partial_orders
    if pars.print_log then
        let (rfs, bnds) = List.fold (fun (rfs, bnds) (rf, _, bnd) ->  (rf::rfs, bnd::bnds)) ([], []) lex_RF
        Log.log pars <| sprintf "Reverting to a past lexicographic RF:\n %A\n with bounds:\n %A" rfs bnds
    lex_RF

///Deletes the old lex checkers for failure_cp and get ready to start finding lex polyranking functions
let switch_to_polyrank (pars : Parameters.parameters) lex_info failure_cp (cp_rf_lex:Dictionary<int, int list>) (p_final:Programs.Program) (safety : SafetyProver) =
    Log.log pars <| sprintf "Now looking for polyranking functions for cp %d" failure_cp
    lex_info.cp_polyrank <- Map.add failure_cp true lex_info.cp_polyrank

    //remove old checkers at cutpoint
    let lex_checkers = cp_rf_lex.[failure_cp]
    let (k,k') = delete_lex_checkers lex_checkers p_final
    let checkTransition = p_final.AddTransition k [Programs.assume Formula.truec] k'

    //and update cp_rf_lex and clear partial_order for cp
    cp_rf_lex.[failure_cp]<- [checkTransition]
    lex_info.partial_orders <- Map.add failure_cp [] lex_info.partial_orders

    safety.ResetFrom k
    if pars.dottify_input_pgms then
        Output.print_dot_program p_final "input__instrumented_switch_to_polyrank.dot"

///Performs the transformation that detects the initial condition at cp and separates the checkers according to the initial condition
let init_cond_trans (pars : Parameters.parameters) (cp:int) (p:Programs.Program) (cp_rf_lex:Dictionary<int, int list>)=
    assert false
    //make rho variable for cp
    let rho:var = Formula.init_cond_var cp

    let assign_rho_m1 =  Programs.assign rho (Term.constant -1)
    let assume_rho_le_m1 = Programs.assume (Formula.Le((Term.var rho), (Term.constant -1)))
    let assume_rho_ge_0 = Programs.assume (Formula.Ge((Term.var rho), (Term.constant 0)))

    //A map from cp to all nodes in its loop
    let (loops, _) = p.FindLoops()
    let cp_loop_nodes = loops.[cp]

    //add rho:=-1 to all trans TO cp from outside, i.e. not on trans to cp from within its own loop
    for (n, (k, cmds, k')) in p.TransitionsWithIdx do
        //if it's a trans TO cp:
        if k'=cp then
            //if it's from the outside:
            if not(Set.contains k cp_loop_nodes) then
                let new_cmds = assign_rho_m1::cmds
                p.SetTransition n (k, new_cmds, k')

    //the node from cp with assume(copied<1)
    let important_node =
        let trans_from_cp_with_copied_lt_1 = p.TransitionsFrom cp |> List.filter (fun (_, (_, cmds, _)) -> contains_copied_lt_1 cp cmds)
        assert (trans_from_cp_with_copied_lt_1.Length=1)
        let (_, (_, _, k')) = trans_from_cp_with_copied_lt_1.Head
        k'

    //yields the index of the transition from imp_node, with "true" if it's the copier and "false" if it isn't
    let trans_from_imp_node =
        [for (n, (k, cmds, _)) in p.TransitionsWithIdx do
            if k = important_node then
                if contains_copied_gets_1 cp cmds then
                    yield (n,true)
                else
                    yield (n,false)]

    //these are indexes
    let ord_trans_from_imp_node = (List.filter (fun (_,b) -> not(b)) trans_from_imp_node) |> List.map fst
    let copier_trans_from_imp_node = List.filter (fun (_,b) -> b) trans_from_imp_node |> List.map fst
    assert (copier_trans_from_imp_node.Length=1)

    //this is the copier node
    let copier =
        let (_,_,k') = p.GetTransition copier_trans_from_imp_node.Head
        k'

    //indexes of trans from copier
    let trans_from_copier = [for (idx, _) in p.TransitionsFrom copier do yield idx]

    assert (trans_from_copier.Length=ord_trans_from_imp_node.Length)

    //map from transition index (of ord trans from imp) to counter
    let counter_map = List.mapi (fun n index ->
                                    (index,n))
                                    ord_trans_from_imp_node
                                    |> Map.ofList

    //prints what the various initial conditions are
    for entry in counter_map do
        let index = entry.Key
        let counter = entry.Value
        let (_,cmds,_) = p.GetTransition index
        (sprintf "initial condition %d:\n %A\n" counter cmds) |> Log.log pars

    //make new_node
    let new_node = p.NewLocation Programs.CutpointRFCheckLocation

    //for copying trans make copy and add on assume(rho<=-1) to the copy
    for index in copier_trans_from_imp_node do
        let (imp_node,cmds,_) = p.GetTransition index
        let new_cmds = assume_rho_le_m1::cmds
        p.AddTransition imp_node new_cmds new_node |> ignore

    //for ord trans from imp node, make copies and add on assume(rho<=-1) and the rho counter assignment to the copies
    for index in ord_trans_from_imp_node do
        let (imp_node,cmds,k') = p.GetTransition index
        let counter = counter_map.[index]
        let assign_rho_counter = Programs.assign rho (Term.constant counter)
        let new_cmds = [assume_rho_le_m1;assign_rho_counter]@cmds
        p.AddTransition imp_node new_cmds k' |> ignore

    //for each ord_trans_from_imp_node,
    //then create a copy from new_node, with the rho assignment
    for index in ord_trans_from_imp_node do
        let (_,cmds,k') = p.GetTransition index
        let counter = counter_map.[index]
        let assign_rho_counter = Programs.assign rho (Term.constant counter)
        let new_cmds = assign_rho_counter::cmds
        p.AddTransition new_node new_cmds k' |> ignore

    //for each ord_trans_from_imp_node and copier_trans_from_imp_node, add assume(rho>=0)
    for index in copier_trans_from_imp_node@ord_trans_from_imp_node do
        let (imp_node,cmds,k') = p.GetTransition index
        let new_cmds = assume_rho_ge_0::cmds
        p.SetTransition index (imp_node,new_cmds,k')

    //Remove old lex checkers:
    //cp_rf_lex supplies the index (in p_final.transitions) of all lexicographic checkers, in correct order
    //Here we extract the first and last node, k and k'
    let lex_checkers = cp_rf_lex.[cp]
    let (k, k') = delete_lex_checkers lex_checkers p

    let mutable counter_checker_map : Map<int,int list> = Map.empty

    //ADD NEW RHO-GUARDED CHECKERS:

    for entry in counter_map do
        //printfn "entry: %A" entry
        let counter = entry.Value
        let new_node = p.NewLocation Programs.CutpointRFCheckLocation
        let assume_rho_counter = Programs.assume (Formula.Eq(Term.Var(rho),Term.constant counter))
        p.AddTransition k [assume_rho_counter] new_node |> ignore
        let counterCheckTrans = p.AddTransition new_node [] k'
        counter_checker_map <- Map.add counter [counterCheckTrans] counter_checker_map

    //like cp_rf_lex, but maps from a cutpoint to a map
    //and the map goes from the rho-counter to the list of indexes of lex checkers, in order
    //starts off just from our cp to an empty map
    let cp_rf_init_cond : Map<int,Map<int,int list>> = [(cp,counter_checker_map)] |> Map.ofList

    cp_rf_init_cond

///Switches to detecting initial condition for failure_cp
let do_init_cond (pars : Parameters.parameters) (lex_info:LexicographicInfo) failure_cp p_final cp_rf_lex (safety : SafetyProver) =
    assert false
    (sprintf "\nDetecting initial condition for cp %d" failure_cp) |> Log.log pars

    //Performs the transformation that detects the initial condition at cp and separates the checkers according to the initial condition
    let cp_rf_init_cond = init_cond_trans pars failure_cp p_final cp_rf_lex

    //Put the new info in lex_info
    lex_info.cp_init_cond <- Map.add failure_cp true lex_info.cp_init_cond
    lex_info.cp_rf_init_cond <- cp_rf_init_cond
    let new_partial_orders =
        [for entry in cp_rf_init_cond.[failure_cp] do
            let counter = entry.Key
            yield (counter,[])] |> Map.ofList
    lex_info.partial_orders_init_cond <- Map.add failure_cp new_partial_orders lex_info.partial_orders_init_cond
    lex_info.past_lex_options <- Map.add failure_cp [] lex_info.past_lex_options

    safety.ResetFrom p_final.Initial
    if pars.dottify_input_pgms then
        Output.print_dot_program p_final "input__init_cond.dot"

///Performs that transformation that counts how many times we've looped through cp, and only checks for more than some number of iterations
let unrolling_trans (cp:int) (cp_rf_lex:Dictionary<int, int list>) (p:Programs.Program) (termination_only:bool) =
    assert false
    //make iteration variable for cp
    let iters:var = Formula.iters_var cp

    let assign_iters_0 = Programs.assign iters (Term.constant 0)
    let increment_iters = Programs.assign iters (Term.Add(Term.var(iters),Term.constant 1))
    let assume_iters_ge_n n = Programs.assume (Formula.Ge(Term.var(iters),Term.constant n))

    // A map from cp to all nodes in its loop
    let (loops, _) = p.FindLoops()
    let cp_loop_nodes = loops.[cp]

    //add iters:=0 to all trans TO cp from outside, i.e. not on trans to cp from within its own loop
    for (n, (k, cmds, k')) in p.TransitionsTo cp do
        //if it's from the outside:
        if not(Set.contains k cp_loop_nodes) then
            let new_cmds = assign_iters_0::cmds
            p.SetTransition n (k, new_cmds, k')

    //add an increment of iters to the assume(copied<1) trans out of cp, but only to the one going back to the loop (i.e., the one leading to a node from which we set copied = 1!)
    // We look for the transition starting from the CP that checks the corresponding copied variable is still unset, and then sets it to 1.
    // We use this to insert increments to our unrolling counter.
    let trans_from_cp_with_copied_lt_1 =
        [for (n, (k, cmds, k')) in p.TransitionsFrom cp do
            if (contains_copied_lt_1 cp cmds) then
                let is_trans_in_loop =
                    p.TransitionsFrom k'
                    |> Seq.filter (fun (_, (_, cmds, _)) -> contains_copied_gets_1 cp cmds)
                    |> Seq.isEmpty
                    |> not
                if is_trans_in_loop then
                    let new_cmds = increment_iters::cmds
                    p.SetTransition n (k, new_cmds, k')
                    yield n]
    assert (trans_from_cp_with_copied_lt_1.Length=1)

    //Remove old lex checkers:
    //cp_rf_lex supplies the index (in p_final.transitions) of all lexicographic checkers, in correct order
    //Here we extract the first and last node, k and k'
    let lex_checkers = cp_rf_lex.[cp]
    let (k, k') = delete_lex_checkers lex_checkers p

    //guard the checkers with assume(iters>=2)
    let new_node = p.NewLocation Programs.CutpointRFCheckLocation
    let iterCheckTrans = p.AddTransition k [assume_iters_ge_n 2] new_node
    let rfCheckTrans = p.AddTransition new_node [] k'
    cp_rf_lex.[cp] <- [rfCheckTrans]

    //iterCheckTrans is the location of the guard
    iterCheckTrans

///Return true if we can use unrolling technique:
let can_unroll (pars : Parameters.parameters) (lex_info:LexicographicInfo) failure_cp =
    let already_unrolling = (lex_info.cp_unrolling).[failure_cp]
    if not(already_unrolling) then
        true
    else
        let current_iter = (lex_info.cp_current_iter).[failure_cp]
        current_iter < pars.unrolling_limit

//Unrolls failure_cp until we reach unrolling_limit. Returns true if we reached limit.
let do_unrolling (pars : Parameters.parameters) (lex_info:LexicographicInfo) failure_cp cp_rf_lex p_final (safety : SafetyProver) termination_only =

    let already_unrolling = ((lex_info.cp_unrolling).[failure_cp])

    if not already_unrolling then //Start unrolling

        (sprintf "\nUnrolling cp %d" failure_cp) |> Log.log pars
        (sprintf "Start with iters >= 2") |> Log.log pars

        //Performs the transformation that counts how many iterations of cp's loop we've done
        //This returns the index of where the guard is
        let guard_index = unrolling_trans failure_cp cp_rf_lex p_final termination_only

        //Put the new info in lex_info
        lex_info.cp_unrolling <- Map.add failure_cp true lex_info.cp_unrolling
        lex_info.partial_orders <- Map.add failure_cp [] lex_info.partial_orders
        lex_info.past_lex_options <- Map.add failure_cp [] lex_info.past_lex_options
        lex_info.cp_iter_guard <- Map.add failure_cp guard_index lex_info.cp_iter_guard

        safety.ResetFrom p_final.Initial
        if pars.dottify_input_pgms then
            Output.print_dot_program p_final "input_unrolling_002.dot"

    else //Else we're already unrolling

        let current_iter = (lex_info.cp_current_iter).[failure_cp]

        if current_iter<(pars.unrolling_limit) then //Unroll some more

            //remove lex checkers at cutpoint
            let lex_checkers = cp_rf_lex.[failure_cp]
            let (j,j') = delete_lex_checkers lex_checkers p_final
            let rfCheckTrans = p_final.AddTransition j [] j'
            cp_rf_lex.[failure_cp] <- [rfCheckTrans]

            lex_info.partial_orders <- Map.add failure_cp [] lex_info.partial_orders
            lex_info.past_lex_options <- Map.add failure_cp [] lex_info.past_lex_options

            //increment the iter guard
            lex_info.cp_current_iter <- Map.add failure_cp (current_iter+1) lex_info.cp_current_iter
            let guard_index = (lex_info.cp_iter_guard).[failure_cp]
            let (k,_,k') = p_final.GetTransition guard_index
            let (iters:Var.var) = Formula.iters_var failure_cp
            let new_cmds = [Programs.assume (Formula.Ge(Term.var(iters),Term.constant (current_iter+1)))]
            p_final.SetTransition guard_index (k,new_cmds,k')

            (sprintf "\nUnrolling cp %d" failure_cp) |> Log.log pars
            (sprintf "iters >= %d" (current_iter+1)) |> Log.log pars

            safety.ResetFrom k
            if pars.dottify_input_pgms then
                let filename = sprintf "input_unrolling_%03d.dot" (current_iter+1)
                Output.print_dot_program p_final filename

        else //Else we've reached the unrolling limit
            dieWith "Reached unrolling limit, but trying to continue."

//////////////////////////////////////////////////////////////////////////////////////////////////
//////// Helper functions setting up the initial instrumentation of the program graph ////////////
//////////////////////////////////////////////////////////////////////////////////////////////////

///Make new copied variables and assume commands to store a copy
///Returns a list of assignments of old vars to new (renamed) vars.
let var_copy_commands (prog : Programs.Program) cp =
    prog.Variables
    |> Set.filter (fun x -> not(Formula.is_const_var x) && not(Formula.is_instr_var x))
    |> Seq.map (fun v -> Programs.assign (Formula.state_snapshot_var cp v) (Term.Var v))
    |> List.ofSeq

let termination_instrumentation (pars : Parameters.parameters) (p : Programs.Program) =
    let p_F = p.Clone()
    let true_assume = Programs.assume Formula.truec
    let final_loc = p_F.GetLabelledLocation FINAL_LOC_LABEL

    let (p_loops, p_sccs) = p.FindLoops()
    let loc_to_scc_locs =
       p_sccs.Items
    |> Seq.map (fun (_, scc_locs) -> scc_locs |> Seq.map (fun n -> (n, scc_locs)))
    |> Seq.concat
    |> Seq.groupBy fst
    |> Seq.map (fun (n, loc_sets) -> (n, Set.unionMany (Seq.map snd loc_sets)))
    |> Map.ofSeq

    (* Do Cooperation Graph transformation, mostly as described in the CAV'13 paper:
       (1) Create a copy of all program locations that occur in loops.
       (2) For all cutpoints, insert some extra magic:
           (a) Switchover transition from the uncopied program
           (b) Extra locations which we use to make snapshots of variables at the beginning of a cycle through an SCC
           (c) Path to the error location on which we will check ranking functions
       (3) Create a copy of all transitions that stay in an SCC.
    *)

    // Step (1): Makes copies of all SCC locations:
    let loc_to_coopLocCopy = Dictionary()
    for (_, scc_locs) in p_sccs.Items do
        for loc in scc_locs do
            match p.GetLocationLabel loc with
            | Programs.OriginalLocation orig_label ->
                if not (loc_to_coopLocCopy.ContainsKey loc) then
                    let loc_copy =
                        if p_loops.ContainsKey loc then
                            p_F.GetLabelledLocation (Programs.DuplicatedCutpointLocation orig_label)
                        else
                            p_F.GetLabelledLocation (Programs.DuplicatedLocation orig_label)
                    loc_to_coopLocCopy.Add(loc, loc_copy)
            | label -> failwithf "Instrumenting program with non-original location %i (label %A)" loc label

    // Step (2): Add extra instrumentation bits for the cutpoints:
    let transDupId_to_transId = Dictionary()
    let cp_to_toCoopTransId = Dictionary()
    let cutpoint_to_before_cp_varcopy_loc = Dictionary()
    let cutpoint_to_after_cp_varcopy_loc = Dictionary()
    ///Maps cutpoint to the index of the transition from it that leads to the error location (that's where the RFs will go!)
    let cp_to_rfCheckTransId = Dictionary()
    for cp in p_loops.Keys do
        let cp_label =
            match p.GetLocationLabel cp with
            | Programs.OriginalLocation label -> label
            | label -> failwithf "Instrumenting program with non-original location %i (label %A)" cp label 
        let cp_copy = loc_to_coopLocCopy.[cp]
        let current_cfg_scc_locs = Map.find cp loc_to_scc_locs
        let current_cfg_cps = current_cfg_scc_locs |> Set.filter p_loops.ContainsKey

        // Add a jump edge from the original node to its new copy:
        let to_coop_transId = p_F.AddTransition cp [true_assume ; Programs.skip] cp_copy
        cp_to_toCoopTransId.Add(cp, to_coop_transId)

        // Create a new node in which we have copied all the variables, and do the copying:
        let after_varcopy_loc = p_F.NewLocationWithLabel (Programs.CutpointVarSnapshotLocation cp_label) 
        cutpoint_to_after_cp_varcopy_loc.Add(cp, after_varcopy_loc)
        let snapshot_transIdx =
            p_F.AddTransition
                cp_copy
                     (true_assume
                      ::[for cp in current_cfg_cps do yield Programs.assume (Formula.Lt(Term.Var(Formula.took_snapshot_var cp), Term.constant 1))]
                      @((Programs.assign (Formula.took_snapshot_var cp) (Term.constant 1))
                      ::(var_copy_commands p_F cp)))
                after_varcopy_loc

        // Also one transition on which we do not copy anything
        let no_snapshot_transIdx =
            p_F.AddTransition
                cp_copy
                     (true_assume
                      ::var_copy_commands p_F cp)
                after_varcopy_loc
        transDupId_to_transId.Add(no_snapshot_transIdx, (snapshot_transIdx, false))

        let before_cp = p_F.NewLocationWithLabel (Programs.CutpointDummyEntryLocation cp_label)
        cutpoint_to_before_cp_varcopy_loc.Add(cp, before_cp)
        p_F.AddTransition before_cp [] cp_copy |> ignore

        // Now also add the instrumentation for the ranking function in:
        // - copy of CP to pre_RF_check_loc where we check that we actually did copy values
        // - pre_RF_check_loc to after_RF_check_loc, where later on the rfs are added in
        // - after_RF_check_loc to final - we only need this for the CTL encoding
        let pre_RF_check_loc = p_F.GetLabelledLocation (Programs.CutpointRFCheckLocation (cp_label + "_pre"))
        p_F.AddTransition
            cp_copy
                    [ true_assume
                    ; Programs.assume (Formula.Ge(Term.Var(Formula.took_snapshot_var cp), Term.Const(bigint.One))) ]
            pre_RF_check_loc |> ignore

        let after_RF_check_loc = p_F.GetLabelledLocation (Programs.CutpointRFCheckLocation (cp_label + "_post"))
        // Start with rf 'true' (0=0).
        let rf_check_transIdx =
            p_F.AddTransition
                pre_RF_check_loc
                    [ true_assume
                    ; Programs.assume (Formula.Eq(Term.Const(bigint.Zero), Term.Const(bigint.Zero))) ]
                after_RF_check_loc
        cp_to_rfCheckTransId.[cp] <- rf_check_transIdx

        p_F.AddTransition
            after_RF_check_loc
                [ true_assume ]
            final_loc |> ignore

    // Step (3): Copy over transitions.
    for (transId, (k, cmds, k')) in p.TransitionsWithIdx do
        // Initialize variables signifying that we too a snapshot:
        if k = p_F.Initial then
            let init_copied_var_cmmds = p_loops.Keys |> Seq.map (fun cp -> (Programs.assign (Formula.took_snapshot_var cp) (Term.Const(bigint.Zero))))
            p_F.SetTransition transId (k, (cmds@(List.ofSeq(init_copied_var_cmmds))), k')

        // Only make copies of transitions that are in an SCC, and stay in that SCC:
        match (loc_to_coopLocCopy.TryGetValue k, loc_to_coopLocCopy.TryGetValue k') with
        | ((true, k_copy), (true, k'_copy)) when Set.contains k' loc_to_scc_locs.[k] ->
            let k'_copy =
                match cutpoint_to_before_cp_varcopy_loc.TryGetValue k' with
                | (true, before_cp) -> before_cp
                | _ -> k'_copy

            //For cutpoint, we have the duplicated transition start in the extra node in which we made variable snapshots:
            let new_source = if p_loops.ContainsKey k then cutpoint_to_after_cp_varcopy_loc.[k] else k_copy
            let dup_transId = p_F.AddTransition new_source cmds k'_copy
            transDupId_to_transId.Add(dup_transId, (transId, true))
        | _ -> ()
                
    let loc_to_coopLocCopy = loc_to_coopLocCopy |> Seq.map (fun x -> (x.Key, x.Value)) |> Map.ofSeq

    //Constants propagation
    if pars.constant_propagation then
        p_F.ConstantPropagation (Analysis.constants p_F)
    p_F.AddSymbolConstantInformation()

    // Clean up program using live variable analysis
    if pars.export_cert.IsNone then
        p_F.LetConvert (Analysis.liveness p_F Set.empty) 
    (p_F, final_loc, cp_to_rfCheckTransId, loc_to_coopLocCopy, transDupId_to_transId, cp_to_toCoopTransId)