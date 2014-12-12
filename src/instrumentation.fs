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
open CTL

//This is a data structure to keep all the relevant information about the search for lexicographic RFs
type LexicographicInfo =
    {
        //
        //STANDARD LEXICOGRAPHIC STUFF
        //

        ///a map from each cp to the order of relations being used currently
        partial_orders : Map<int,Relation.relation list> ref

        ///a map from each cp to any lexicographic solutions we found in the past, but did not instrument. Last in first out
        past_lex_options : Map<int, ((Formula.formula list * Formula.formula list * Formula.formula list)*Relation.relation list) list> ref

        ///a map from each cp to a bool describing whether we are currently doing the lexicographic method (true) or disjunctive method (false)
        cp_attempt_lex: Map<int, bool> ref

        //
        //INITIAL CONDITION STUFF
        //

        ///a map from each cp to a bool describing whether we are currently doing the "detect initial condition" improvement
        cp_init_cond: Map<int,bool> ref

        ///a map from each cutpoint to a map.
        ///the map is from a counter to the index location of the counter's lex checkers
        cp_rf_init_cond : Map<int,Map<int,int list>> ref

        ///is the counter identity of the path just found
        current_counter: int ref

        ///map from cp to map.
        ///the map is from counters to current partial order for that counter
        partial_orders_init_cond: Map<int,Map<int,Relation.relation list>> ref

        //
        //UNROLLING STUFF
        //

        ///a map from cp to a bool describing whether we are currently doing the "unrolling" improvement
        cp_unrolling: Map<int,bool> ref

        ///a map from cp to the current number of iterations we're unrolling. Note it starts off at 2 for all cps.
        cp_current_iter: Map<int,int> ref

        ///a map from cp to the index of the transition that contains the guard
        cp_iter_guard: Map<int,int> ref

        //
        //POLYRANKING STUFF
        //

        ///a map from cp to whether we're currently finding polyranking fns for this cutpoint. Starts as false, then switches to true as necessary
        cp_polyrank: Map<int,bool> ref

    }

//initialises lex_info
let init_lex_info (pars : Parameters.parameters) (cutpoints:int list) =

    {
        partial_orders= ref ([for cp in cutpoints -> (cp,[])] |> Map.ofList)
        past_lex_options = ref ([for cp in cutpoints -> (cp,[])] |> Map.ofList)
        cp_attempt_lex = ref ([for cp in cutpoints -> (cp,pars.lexicographic)] |> Map.ofList)

        cp_init_cond = ref ([for cp in cutpoints -> (cp,false)] |> Map.ofList)
        cp_rf_init_cond = ref Map.empty
        current_counter = ref -1
        partial_orders_init_cond = ref ([for cp in cutpoints -> (cp,Map.empty)]|>Map.ofList)

        cp_unrolling = ref ([for cp in cutpoints -> (cp,false)] |> Map.ofList)
        cp_current_iter = ref ([for cp in cutpoints -> (cp,2)] |> Map.ofList)
        cp_iter_guard = ref Map.empty

        cp_polyrank = ref ([for cp in cutpoints -> (cp,false)] |> Map.ofList)

    }


///////////////////////////////////////////////////////////////////////////////
//////// Helper functions instrumenting RFs into the program graph ////////////
///////////////////////////////////////////////////////////////////////////////

///Returns true if cmds contains assume(copied_cp<1)
let contains_copied_lt_1 cp (cmds:Programs.command list)=
    let copy = Formula.copy_var cp
    let found = ref false
    for cmd in cmds do
        match cmd with
        | Programs.Assume(_,Formula.Lt(Term.Var(v),Term.Const c)) when c = bigint.One && (v=copy) ->
            found := true
        | _ -> ()
    !found

///Returns true if cmds contains copied_cp:=1
let contains_copied_gets_1 cp (cmds:Programs.command list)=
    let copy = Formula.copy_var cp
    let found = ref false
    for cmd in cmds do
        match cmd with
        | Programs.Assign(_,v,Term.Const c) when c = bigint.One && (v=copy) ->
            found := true
        | _ -> ()
    !found

//Instruments a RF to p_final (when we're doing the disjunctive method).
let instrument_disj_RF (pars : Parameters.parameters) cp rf bnd (found_disj_rfs : Map<int, (formula * formula) list> ref) (cp_rf:Dictionary<int,int>) (p_final:Programs.Program) graph =
    let old_rfs_for_cp = (!found_disj_rfs).FindWithDefault cp []
    found_disj_rfs := !found_disj_rfs |> Map.remove cp |> Map.add cp ((rf, bnd)::old_rfs_for_cp)

    assert(cp_rf.ContainsKey(cp))

    // This is the transition from the checked cutpoint to the error location, where we check the RF found so far
    let check_trans = cp_rf.[cp]
    let (k, _, _) = p_final.transitions.[check_trans]
    
    //We are now looking for the transition that leads to the checker transition, i.e., the one that goes to node k:
    let pre_check_trans = Seq.find (fun n -> let (_, _, l') = p_final.transitions.[n] in l' = k) !p_final.active
    let (l, cmds', k) = p_final.transitions.[pre_check_trans]

    (* 
        This thing in a picture, where things in () are nodes. Old transitions:
          ... (l) -- cmds' -->                                  (k) -- "old rf check" --> (k')
        New transitions:
          ... (l) -- cmds' --> (new_node) -- "new rf check" --> (k) -- "old rf check" --> (k')
        Here, l is always (?) be the checked cutpoint, but that's not a hard requirement
    *)
    let new_node = Programs.new_node p_final
    p_final.transitions.[pre_check_trans] <- (l, cmds', new_node)
    
    //Store the ID of one of the new checker transitions, use it in cp_rf
    let cnt = !p_final.transitions_cnt
    Programs.plain_add_transition p_final new_node [Programs.assume (Formula.Not(rf))] k
    Programs.plain_add_transition p_final new_node [Programs.assume (Formula.Not(bnd))] k
    cp_rf.[cp] <- (cnt)

    Log.log pars <| sprintf "Instrumented in disjunctive RF between %i and %i" new_node k
    
    //Now reset the reachability graph and remove every (incomplete) unwinding that has passed behind (l), as we changed the program there:
    Reachability.reset pars graph l
    if pars.dottify_input_pgms then
        Output.print_dot_program p_final "input__instrumented_disjunctive_rf.dot"

///Takes in the indexes of the transitions that are lexicographic checkers, deletes them, and returns start and end node of the old check transition (so that you can stuff new checkers in there)
let delete_lex_checkers (pars : Parameters.parameters) (lex_checkers:int list) (p:Programs.Program) =
    let (first_check_node,_,_) = p.transitions.[List.head lex_checkers]
    let (_,_,last_check_node) = p.transitions.[List.last lex_checkers]

    //Delete all the old lexicographic checkers from the program
    for checker in lex_checkers do
        Programs.remove_transition p checker

    (first_check_node, last_check_node)

///Replaces a list of old lexicographic checkers by a new list
let replace_lex_rf_checkers (pars : Parameters.parameters) p old_checker_trans_ids number_of_checkers (ith_checker_formulas: int -> formula list) =
    //remove old lex checkers for this counter
    let (k,k') = delete_lex_checkers pars old_checker_trans_ids p

    //Now we insert new lexicographic RF checkers from k to k'
    let new_nodes = k::[for _ in 1..(number_of_checkers-1) -> Programs.new_node p]@[k']
    let new_checker_trans_ids = ref []
    for i in 1..number_of_checkers do
        for trans in ith_checker_formulas i do
            let trans_id = !p.transitions_cnt
            Programs.plain_add_transition p new_nodes.[i-1] [Programs.assume (Formula.Not(trans))] new_nodes.[i]
            new_checker_trans_ids := !new_checker_trans_ids@[trans_id]
    (k, !new_checker_trans_ids)

//Instruments a lexicographic RF to p_final
let instrument_lex_RF (pars : Parameters.parameters) cp (decr_list : Formula.formula list) (not_incr_list : Formula.formula list) (bnd_list : Formula.formula list) found_lex_rfs (cp_rf_lex:System.Collections.Generic.Dictionary<int, int list>) (p_final:Programs.Program) graph lex_info =
    let doing_init_cond = (!lex_info.cp_init_cond).[cp]

    //Standard lexicographic RFs:
    if not doing_init_cond then
        assert(cp_rf_lex.ContainsKey(cp))

        //cp_rf_lex supplies the index (in p_final.transitions) of all lexicographic checkers, in correct order
        let old_checker_trans_ids = cp_rf_lex.[cp]
        found_lex_rfs := !found_lex_rfs |> Map.remove cp |> Map.add cp (decr_list, not_incr_list, bnd_list)
        //This gives the formulas that should hold for the i-th step in the check:
        let ith_trans_formula i = decr_list.[i-1]::bnd_list.[i-1]::[for j in 1..i-1 -> not_incr_list.[j-1]]
        let (first_checker_node, new_lex_checker_trans_ids) = replace_lex_rf_checkers pars p_final old_checker_trans_ids decr_list.Length ith_trans_formula
        cp_rf_lex.[cp] <- new_lex_checker_trans_ids
        Reachability.reset pars graph first_checker_node

    //We are instrumenting the Lex RF under a particular initial condition for the cp:
    else
        //Which initial condition did the path we just found represent?
        let counter = !lex_info.current_counter

        //map from counters to the index locations of the counter's lex checkers
        let counters_to_checkers = (!lex_info.cp_rf_init_cond).[cp]
        let old_checker_trans_ids = counters_to_checkers.[counter]
        //This gives the formulas that should hold for the i-th step in the check:
        let ith_trans_formula i = decr_list.[i-1]::bnd_list.[i-1]::[for j in 1..i-1 -> not_incr_list.[j-1]]
        let (first_checker_node, new_lex_checker_trans_ids) = replace_lex_rf_checkers pars p_final old_checker_trans_ids decr_list.Length ith_trans_formula
        let new_counter_checkers_map = Map.add counter new_lex_checker_trans_ids counters_to_checkers
        lex_info.cp_rf_init_cond := Map.add cp new_counter_checkers_map !lex_info.cp_rf_init_cond

        Reachability.reset pars graph first_checker_node

    if pars.dottify_input_pgms then
        Output.print_dot_program p_final "input__instrumented_lex_RF.dot"

//Instruments a lexicographic polyranking function to p_final.
let instrument_poly_RF (pars : Parameters.parameters) cp (poly_checkers:Formula.formula list list) (cp_rf_lex:System.Collections.Generic.Dictionary<int, int list>) (p_final:Programs.Program) graph =
    assert(cp_rf_lex.ContainsKey(cp))

    //cp_rf_lex supplies the index (in p_final.transitions) of all lexicographic checkers, in correct order
    //Here we extract the first and last node, k and k'
    let old_checker_trans_ids = cp_rf_lex.[cp]
    let ith_trans_formula i = poly_checkers.[i-1]
    let (first_checker_node, new_lex_checker_trans_ids) = replace_lex_rf_checkers pars p_final old_checker_trans_ids poly_checkers.Length ith_trans_formula
    cp_rf_lex.[cp] <- new_lex_checker_trans_ids

    Reachability.reset pars graph first_checker_node
    if pars.dottify_input_pgms then
        Output.print_dot_program p_final "input__instrumented_poly_lex_RF.dot"

///Fetches the past lex option at the head of the queue for failure_cp
let switch_to_past_lex_RF (pars : Parameters.parameters) lex_info failure_cp =
    //Take the lex RF at the head of the queue out
    let past_lex_options = (!lex_info.past_lex_options).[failure_cp]
    let new_lex_WF = past_lex_options.Head
    lex_info.past_lex_options := Map.add failure_cp past_lex_options.Tail !lex_info.past_lex_options

    let ((decr_list, not_incr_list, bnd_list),new_partial_order) = new_lex_WF
    lex_info.partial_orders:= Map.add failure_cp new_partial_order !lex_info.partial_orders
    Log.log pars <| sprintf "Reverting to a past lexicographic RF:\n %A\n with bounds:\n %A" decr_list bnd_list
    (decr_list,not_incr_list,bnd_list)

///Deletes the old lex checkers for failure_cp and get ready to start finding lex polyranking functions
let switch_to_polyrank (pars : Parameters.parameters) lex_info failure_cp (cp_rf_lex:System.Collections.Generic.Dictionary<int, int list>) (p_final:Programs.Program) graph=
    Log.log pars <| sprintf "Now looking for polyranking functions for cp %d" failure_cp
    lex_info.cp_polyrank:= Map.add failure_cp true !lex_info.cp_polyrank

    //remove old checkers at cutpoint
    let lex_checkers = cp_rf_lex.[failure_cp]
    let (k,k') = delete_lex_checkers pars lex_checkers p_final
    let cnt = !p_final.transitions_cnt
    Programs.plain_add_transition p_final k [Programs.assume Formula.truec] k'

    //and update cp_rf_lex and clear partial_order for cp
    cp_rf_lex.[failure_cp]<-[cnt]
    lex_info.partial_orders := Map.add failure_cp [] !lex_info.partial_orders

    Reachability.reset pars graph k
    if pars.dottify_input_pgms then
        Output.print_dot_program p_final "input__instrumented_switch_to_polyrank.dot"

///Performs the transformation that detects the initial condition at cp and separates the checkers according to the initial condition
let init_cond_trans (pars : Parameters.parameters) (cp:int) (p:Programs.Program) (cp_rf_lex:System.Collections.Generic.Dictionary<int, int list>)=

    //make rho variable for cp
    let rho:var = Formula.init_cond_var cp

    let assign_rho_m1 =  Programs.assign rho (Term.constant -1)
    let assume_rho_le_m1 = Programs.assume (Formula.Le((Term.var rho), (Term.constant -1)))
    let assume_rho_ge_0 = Programs.assume (Formula.Ge((Term.var rho), (Term.constant 0)))

    //A map from cp to all nodes in its loop
    let (loops, _) = Programs.find_loops p
    let cp_loop_nodes = loops.[cp]

    //add rho:=-1 to all trans TO cp from outside, i.e. not on trans to cp from within its own loop
    for n in !p.active do
        let (k,cmds,k') = p.transitions.[n]
        //if it's a trans TO cp:
        if k'=cp then
            //if it's from the outside:
            if not(Set.contains k cp_loop_nodes) then
                let new_cmds = assign_rho_m1::cmds
                p.transitions.[n] <- (k,new_cmds,k')

    //the node from cp with assume(copied<1)
    let important_node =
        let trans_from_cp_with_copied_lt_1 = Programs.transitions_from p cp |> List.filter (fun (cmds,_) -> contains_copied_lt_1 cp cmds)
        assert (trans_from_cp_with_copied_lt_1.Length=1)
        let (_,k') = trans_from_cp_with_copied_lt_1.Head
        k'

    //yields the index of the transition from imp_node, with "true" if it's the copier and "false" if it isn't
    let trans_from_imp_node =
        [for n in !p.active do
            let (k,cmds,_) = p.transitions.[n]
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
        let (_,_,k') = p.transitions.[copier_trans_from_imp_node.Head]
        k'

    //indexes of trans from copier
    let trans_from_copier =
        [for n in !p.active do
            let (k,_,_) = p.transitions.[n]
            if k = copier then
                yield n]

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
        let (_,cmds,_) = p.transitions.[index]
        (sprintf "initial condition %d:\n %A\n" counter cmds) |> Log.log pars

    //make new_node
    let new_node = Programs.new_node p

    //for copying trans make copy and add on assume(rho<=-1) to the copy
    for index in copier_trans_from_imp_node do
        let (imp_node,cmds,_) = p.transitions.[index]
        let new_cmds = assume_rho_le_m1::cmds
        Programs.plain_add_transition p imp_node new_cmds new_node

    //for ord trans from imp node, make copies and add on assume(rho<=-1) and the rho counter assignment to the copies
    for index in ord_trans_from_imp_node do
        let (imp_node,cmds,k') = p.transitions.[index]
        let counter = counter_map.[index]
        let assign_rho_counter = Programs.assign rho (Term.constant counter)
        let new_cmds = [assume_rho_le_m1;assign_rho_counter]@cmds
        Programs.plain_add_transition p imp_node new_cmds k'

    //for each ord_trans_from_imp_node,
    //then create a copy from new_node, with the rho assignment
    for index in ord_trans_from_imp_node do
        let (_,cmds,k') = p.transitions.[index]
        let counter = counter_map.[index]
        let assign_rho_counter = Programs.assign rho (Term.constant counter)
        let new_cmds = assign_rho_counter::cmds
        Programs.plain_add_transition p new_node new_cmds k'

    //for each ord_trans_from_imp_node and copier_trans_from_imp_node, add assume(rho>=0)
    for index in copier_trans_from_imp_node@ord_trans_from_imp_node do
        let (imp_node,cmds,k') = p.transitions.[index]
        let new_cmds = assume_rho_ge_0::cmds
        p.transitions.[index] <- (imp_node,new_cmds,k')

    //Remove old lex checkers:
    //cp_rf_lex supplies the index (in p_final.transitions) of all lexicographic checkers, in correct order
    //Here we extract the first and last node, k and k'
    let lex_checkers = cp_rf_lex.[cp]
    let (k,k') = delete_lex_checkers pars lex_checkers p

    let (counter_checker_map:Map<int,int list> ref) = ref Map.empty

    //ADD NEW RHO-GUARDED CHECKERS:

    for entry in counter_map do
        //printfn "entry: %A" entry
        let counter = entry.Value
        let new_node = Programs.new_node p
        let assume_rho_counter = Programs.assume (Formula.Eq(Term.Var(rho),Term.constant counter))
        Programs.plain_add_transition p k [assume_rho_counter] new_node
        let cnt = !p.transitions_cnt
        Programs.plain_add_transition p new_node [] k'
        counter_checker_map := Map.add counter [cnt] !counter_checker_map

    //like cp_rf_lex, but maps from a cutpoint to a map
    //and the map goes from the rho-counter to the list of indexes of lex checkers, in order
    //starts off just from our cp to an empty map
    let cp_rf_init_cond:Map<int,Map<int,int list>> ref = [(cp,!counter_checker_map)] |> Map.ofList |> ref

    !cp_rf_init_cond

///Switches to detecting initial condition for failure_cp
let do_init_cond (pars : Parameters.parameters) (lex_info:LexicographicInfo) failure_cp p_final cp_rf_lex graph =

    (sprintf "\nDetecting initial condition for cp %d" failure_cp) |> Log.log pars

    //Performs the transformation that detects the initial condition at cp and separates the checkers according to the initial condition
    let cp_rf_init_cond = init_cond_trans pars failure_cp p_final cp_rf_lex

    //Put the new info in lex_info
    lex_info.cp_init_cond := Map.add failure_cp true !lex_info.cp_init_cond
    lex_info.cp_rf_init_cond := cp_rf_init_cond
    let new_partial_orders =
        [for entry in cp_rf_init_cond.[failure_cp] do
            let counter = entry.Key
            yield (counter,[])] |> Map.ofList
    lex_info.partial_orders_init_cond:= Map.add failure_cp new_partial_orders !lex_info.partial_orders_init_cond
    lex_info.past_lex_options:= Map.add failure_cp [] !lex_info.past_lex_options

    Reachability.reset pars graph !p_final.initial
    if pars.dottify_input_pgms then
        Output.print_dot_program p_final "input__init_cond.dot"

///Performs that transformation that counts how many times we've looped through cp, and only checks for more than some number of iterations
let unrolling_trans (pars : Parameters.parameters) (cp:int) (cp_rf_lex:System.Collections.Generic.Dictionary<int, int list>) (p:Programs.Program) (termination_only:bool) =

    //make iteration variable for cp
    let iters:var = Formula.iters_var cp

    let assign_iters_0 = Programs.assign iters (Term.constant 0)
    let increment_iters = Programs.assign iters (Term.Add(Term.var(iters),Term.constant 1))
    let assume_iters_ge_n n = Programs.assume (Formula.Ge(Term.var(iters),Term.constant n))

    // A map from cp to all nodes in its loop
    let (loops, _) = Programs.find_loops p
    let cp_loop_nodes = loops.[cp]

    //add iters:=0 to all trans TO cp from outside, i.e. not on trans to cp from within its own loop
    for n in !p.active do
        let (k,cmds,k') = p.transitions.[n]
        //if it's a trans TO cp:
        if k'=cp then
            //if it's from the outside:
            if not(Set.contains k cp_loop_nodes) then
                let new_cmds = assign_iters_0::cmds
                p.transitions.[n] <- (k,new_cmds,k')

    //add an increment of iters to the assume(copied<1) trans out of cp, but only to the one going back to the loop (i.e., the one leading to a node from which we set copied = 1!)
    if termination_only then
        // We look for the transition starting from the CP that checks the corresponding copied variable is still unset, and then sets it to 1.
        // We use this to insert increments to our unrolling counter.
        let trans_from_cp_with_copied_lt_1 =
            [for n in !p.active do
                let (k,cmds,k') = p.transitions.[n]
                if (k=cp) && (contains_copied_lt_1 cp cmds) then
                    let is_trans_in_loop =
                           !p.active
                        |> Seq.map (fun n -> p.transitions.[n])
                        |> Seq.filter (fun (l,cmds,_) -> l = k' && contains_copied_gets_1 cp cmds)
                        |> Seq.isEmpty
                        |> not
                    if is_trans_in_loop then
                        let new_cmds = increment_iters::cmds
                        p.transitions.[n] <- (k,new_cmds,k')
                        yield n]
        assert (trans_from_cp_with_copied_lt_1.Length=1)
    else
        // This is similar to the termination_only case, but the CTL instrumentation introduces several further intermediate nodes for checks of subproperties.
        match Seq.tryFind (fun n -> let (k, _, _) = p.transitions.[n] in k = cp) !p.active with
        | None -> dieWith "?"
        | Some n -> //k' should be "start_of_subproperty_nodeK"
            let (_, _, k') = p.transitions.[n]
            match Programs.findLabel p k' with
            | None -> dieWith "?"
            | Some label -> 
                let endLabel = label.Replace ("start_of", "end_of")
                let endPropertyNode = Programs.map p endLabel
                let trans_from_cp_with_copied_lt_1 =
                    [for n in !p.active do
                        let (k,cmds,k') = p.transitions.[n]
                        if (k=endPropertyNode) && (contains_copied_lt_1 cp cmds) then
                            let is_trans_in_loop =
                                   !p.active
                                |> Seq.map (fun n -> p.transitions.[n])
                                |> Seq.filter (fun (l,cmds,_) -> l = k' && contains_copied_gets_1 cp cmds)
                                |> Seq.isEmpty
                                |> not
                            if is_trans_in_loop then
                                let new_cmds = increment_iters::cmds
                                p.transitions.[n] <- (k,new_cmds,k')
                                yield n]
                assert (trans_from_cp_with_copied_lt_1.Length=1)

    //Remove old lex checkers:

    //cp_rf_lex supplies the index (in p_final.transitions) of all lexicographic checkers, in correct order
    //Here we extract the first and last node, k and k'
    let lex_checkers = cp_rf_lex.[cp]
    let (k,k') = delete_lex_checkers pars lex_checkers p

    //guard the checkers with assume(iters>=2)
    let new_node = Programs.new_node p
    let cnt1 = !p.transitions_cnt
    Programs.plain_add_transition p k [assume_iters_ge_n 2] new_node
    let cnt2 = !p.transitions_cnt
    Programs.plain_add_transition p new_node [] k'
    cp_rf_lex.[cp] <- [cnt2]

    //cnt1 is the location of the guard
    cnt1

///Return true if we can use unrolling technique:
let can_unroll (pars : Parameters.parameters) (lex_info:LexicographicInfo) failure_cp =
    let already_unrolling = (!lex_info.cp_unrolling).[failure_cp]
    if not(already_unrolling) then
        true
    else
        let current_iter = (!lex_info.cp_current_iter).[failure_cp]
        current_iter < pars.unrolling_limit

//Unrolls failure_cp until we reach unrolling_limit. Returns true if we reached limit.
let do_unrolling (pars : Parameters.parameters) (lex_info:LexicographicInfo) failure_cp cp_rf_lex p_final graph termination_only =

    let already_unrolling = ((!lex_info.cp_unrolling).[failure_cp])

    if not already_unrolling then //Start unrolling

        (sprintf "\nUnrolling cp %d" failure_cp) |> Log.log pars
        (sprintf "Start with iters >= 2") |> Log.log pars

        //Performs the transformation that counts how many iterations of cp's loop we've done
        //This returns the index of where the guard is
        let guard_index = unrolling_trans pars failure_cp cp_rf_lex p_final termination_only

        //Put the new info in lex_info
        lex_info.cp_unrolling := Map.add failure_cp true !lex_info.cp_unrolling
        lex_info.partial_orders := Map.add failure_cp [] !lex_info.partial_orders
        lex_info.past_lex_options := Map.add failure_cp [] !lex_info.past_lex_options
        lex_info.cp_iter_guard := Map.add failure_cp guard_index !lex_info.cp_iter_guard

        Reachability.reset pars graph !p_final.initial
        if pars.dottify_input_pgms then
            Output.print_dot_program p_final "input_unrolling_002.dot"

    else //Else we're already unrolling

        let current_iter = (!lex_info.cp_current_iter).[failure_cp]

        if current_iter<(pars.unrolling_limit) then //Unroll some more

            //remove lex checkers at cutpoint
            let lex_checkers = cp_rf_lex.[failure_cp]
            let (j,j') = delete_lex_checkers pars lex_checkers p_final
            let cnt = !p_final.transitions_cnt
            Programs.plain_add_transition p_final j [] j'
            cp_rf_lex.[failure_cp] <- [cnt]

            lex_info.partial_orders := Map.add failure_cp [] !lex_info.partial_orders
            lex_info.past_lex_options := Map.add failure_cp [] !lex_info.past_lex_options

            //increment the iter guard
            lex_info.cp_current_iter:=Map.add failure_cp (current_iter+1) !lex_info.cp_current_iter
            let guard_index = (!lex_info.cp_iter_guard).[failure_cp]
            let (k,_,k') = p_final.transitions.[guard_index]
            let (iters:Var.var) = Formula.iters_var failure_cp
            let new_cmds = [Programs.assume (Formula.Ge(Term.var(iters),Term.constant (current_iter+1)))]
            p_final.transitions.[guard_index] <- (k,new_cmds,k')

            (sprintf "\nUnrolling cp %d" failure_cp) |> Log.log pars
            (sprintf "iters >= %d" (current_iter+1)) |> Log.log pars

            //printfn "k:%d" k

            Reachability.reset pars graph k
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
let var_copy_commands (p_orig: Programs.Program) (p_c : Programs.Program) cp =
    //We had a bug where variables were abstracted away by lazy disjunction, then after disjunctive callback, they weren't in the copying transition as required.
    //Here I'm putting all variables, even those abstracted away, in at the beginning.
    let vars =
        let retrieve_vars (_, cmds) =
            [for cmd in cmds do
                    let vars_in_cmd =
                        match cmd with
                            |Programs.Assume(_,f) ->
                                Formula.freevars f
                            |_ -> failwith "unexpected"
                    yield vars_in_cmd] |> Set.unionMany
        let vars_from_lazy_disj = (!p_orig.abstracted_disjunctions).Items |> Seq.map retrieve_vars  |> Set.unionMany
        let filtered_pvars = !p_orig.vars |> Set.filter (fun x -> not(Formula.is_disj_var x) && not(Formula.is_const_var x))
        Set.union vars_from_lazy_disj filtered_pvars

    let copy_vars = vars |> Seq.map (fun x -> Formula.save_state_var x cp)

    p_c.vars := (!p_c.vars).addMany copy_vars

    //Add to mapping of variables
    let copy_vars_to_vars = (vars,copy_vars) ||> Seq.zip |> Seq.fold (fun (acc:Map<var,var>) (x,y) -> acc.Add(y,x)) Map.empty

    //Make new command list that assigns var to var_old_CP
    copy_vars_to_vars |> Seq.map (fun x -> Programs.assign x.Key (Term.Var(x.Value)))

// Either it's a Prop or not (AG, AF, AW).
// Used to unify return types from instrument_prop and instrument_*.
type Either<'a,'b> =
        | IsAProp of 'a
        | IsNotAProp of 'b

let generate_checker_instrumentation_nodes n p =
    let end_of_subproperty_node_s = "end_of_subproperty_node" + n.ToString();
    let start_of_subproperty_node_s = "start_of_subproperty_node" + n.ToString();
    let end_of_subproperty_node = Programs.map p end_of_subproperty_node_s
    //Node to point at other nested graphs later.
    let start_of_subproperty_node = Programs.map p start_of_subproperty_node_s

    (end_of_subproperty_node, start_of_subproperty_node)

//******************************************************************************************************//
// HK: Experimental Code : Bottom Up Temporal Property Verification of Infinite State Transition Systems//
//******************************************************************************************************//

let eliminate_redun (lst : (int * Formula.formula) list) : (int*Formula.formula) list =
    let var_terms = System.Collections.Generic.Dictionary<Term.term, bigint>()
    let simplify (x, y) =
        let disjuncts = (Formula.polyhedra_dnf y |> Formula.split_disjunction)
        let split_var = (disjuncts |> Formula.freevars_list) |> Set.map(fun z -> Term.Var(z))
        let removeRedundantBounds n =
            match n with
            | Le (s, t) when s.isVar && not(t.isVar) && split_var.Contains s ->
                if var_terms.ContainsKey(s) then
                    if Term.eval(t) > var_terms.[s] then
                        var_terms.Add(s,Term.eval(t))
                        Le (s, t)
                    else
                        Le (s, Term.Const(var_terms.[s]))
                else
                    var_terms.Add(s,Term.eval(t))
                    Le (s, t)
            |_ -> n

        let y =
               disjuncts
            |> List.map removeRedundantBounds
            |> Set.ofList |> Set.toList |> Formula.disj
            |> Formula.z3 |> Z.simplify |> Formula.fromZ3
        (x, y)
    lst |> Set.ofList |> Set.map simplify |> Set.toList

/// Extracts the precondition for the current subproperty at cutpoint cp, and adds in new checkers for this subproperty between
/// start_node_for_subproperty and ret_true_node (for cases where it holds)/ret_false_node (for cases where it does not hold)
let add_subproperty_conditions p conditions_per_cp cp isExistential start_node_for_subproperty ret_true_node ret_false_node =
    let distribute xss =
        let rec f xss rs rss =
            match xss with
            | (x::xs)::xss -> f xss (x::rs) (f (xs::xss) rs rss)
            | []::_ -> rss
            | [] -> rs::rss
        f xss [] []

    //A list of lists, where the rows are conjunctions and the columns are disjunctions. This means that we want to create a DNF
    //out of CNF. The reason why we're doing this is because we cannot represent disjunction in our graph, thus we must branch with
    //every disjunction possible. This may be expensive, but it seems that we only get two disjunctions at most.
    //Note that for E we need the disjunction of the pre-conditions for a location, versus the conjunction. This is dealt
    //with in another function through flattening the formulas with the same node through disjunction. This is not done for A
    let cond = conditions_per_cp |> List.filter (fun (x,_) -> x = cp) |> List.map (fun (_,y) ->  Formula.polyhedra_dnf y |> Formula.split_disjunction)

    //We generate a list of disjunctions of conjunctions (list of lists), then we flatten to just a list of disjunctions
    //between conjucted formulas
    let dnf_cond = distribute cond |> List.map (fun x -> Formula.conj x)

    //Generate the equivalent for the negation:
    let neg_cond = conditions_per_cp |> List.filter (fun (x,_) -> x = cp) |> List.map (fun (_,y) -> Formula.negate(y)) |> Formula.disj
    let neg_cond = neg_cond |> Formula.polyhedra_dnf  |> Formula.split_disjunction

    //If existential then we want to reverse dnf_cond and neg_cond because we are doing the negation of A
    let (dnf_cond, neg_cond) = if isExistential then (neg_cond, dnf_cond) else (dnf_cond, neg_cond)

    //Handling dnf_cond  instrumentation
    for l in dnf_cond do
        //Since we're doing disjunctions, must add transition for each disjunction
        Programs.plain_add_transition p
            start_node_for_subproperty
                [ (Programs.assume l) ]
            ret_true_node

    //Handling neg_cond instrumentation
    for l in neg_cond do
        Programs.plain_add_transition p
            start_node_for_subproperty
                [ (Programs.assume l) ]
            ret_false_node
    ()

/// Add transitions that ensure the fairness constraint (which may well be None) to the program p, between nodes ret_true_node/ret_false_node and end_node_of_subproperty.
///
/// This also takes care of assigning the correct value to ret_var, based on whether we are coming from ret_true_node/ret_false_node.
let add_fairness_check_transititions p (fairness_constraint : ((Programs.command list * Programs.command list) * Programs.command list list) option) trans_idx ret_var ret_true_node ret_false_node end_node_of_subproperty =
    if fairness_constraint.IsNone then
        Programs.plain_add_transition p ret_true_node [Programs.assign ret_var (Term.Const(bigint.One))] end_node_of_subproperty
        Programs.plain_add_transition p ret_false_node [Programs.assign ret_var (Term.Const(bigint.Zero))] end_node_of_subproperty

    else
        let fair_node = Programs.map p ("FAIR_" + trans_idx.ToString())
        Programs.plain_add_transition p ret_true_node [Programs.assign ret_var (Term.Const(bigint.One))] fair_node
        Programs.plain_add_transition p ret_false_node [Programs.assign ret_var (Term.Const(bigint.Zero))] fair_node

        let fair_node2 = Programs.new_node p
        let((fair, fair_1), fair_2) = fairness_constraint.Value
        Programs.plain_add_transition p fair_node fair fair_node2
        Programs.plain_add_transition p fair_node2 fair_1 end_node_of_subproperty

        for n in fair_2 do
            Programs.plain_add_transition p fair_node n end_node_of_subproperty

let instrument_X p formula (propertyMap : ListDictionary<CTL_Formula, int * Formula.formula>) (fairness_constraint : ((Programs.command list * Programs.command list) * Programs.command list list) option) isExistential =
    let p_X = Programs.copy p
    let final_loc = Programs.new_node p_X
    let p_X_copy = Programs.copy p_X
    let first_states = ref Set.empty
    let next_states = ref Set.empty
    //Add return value to instrumented program, and also add it to set to keep track of all the return values
    let ret = Formula.subcheck_return_var "0"
    p_X.vars := Set.add ret !p_X.vars

    //let cp_conditions = eliminate_redun propertyMap.[formula]
    let cp_conditions = propertyMap.[formula]
    let cp = cp_conditions |> List.map(fun (x,_) -> x)

    for n in !p_X_copy.active do
        let (k,_,k') = p_X.transitions.[n]
        if(k = !p_X.initial) then
            first_states := Set.add k' !first_states

    for n in !p_X_copy.active do
        let (k,_,k') = p_X.transitions.[n]
        if(Set.contains k !first_states) then
            next_states := Set.add k' !next_states

    // 2. Instrument in the sub-property: Only for the next state.
    let node_to_end_of_subproperty_node_map = new Dictionary<int,int>()
    for n in !p_X.active do
        let (k,c,k') = p_X.transitions.[n]
        //For Bottom up, we're also checking that it's a node/cp that has a pre-condition
        if (Set.contains k !next_states) && not(node_to_end_of_subproperty_node_map.ContainsKey k) && (List.contains k cp) then

            // Create the two nodes between which we nest the encoding of the subproperty we consider:
            let (end_node_of_subproperty, start_node_for_subproperty) = generate_checker_instrumentation_nodes k p_X
            let ret_true_node = Programs.map p_X ("RET_TRUE" + n.ToString())
            let ret_false_node = Programs.map p_X ("RET_FALSE" + n.ToString())

            //Very similar to traditional AG, except we are only adding propositional conditions where there are cut-points
            //We're also handling disjunctions
            Programs.plain_add_transition p_X k [] start_node_for_subproperty

            add_subproperty_conditions p_X cp_conditions k isExistential start_node_for_subproperty ret_true_node ret_false_node
            
            add_fairness_check_transititions p_X fairness_constraint n ret ret_true_node ret_false_node end_node_of_subproperty

            //Hmm in the old AG we just repeated the commands, but it could just be a skip
            Programs.plain_add_transition p_X end_node_of_subproperty [] final_loc

            node_to_end_of_subproperty_node_map.Add (k, end_node_of_subproperty)

            Programs.plain_add_transition p_X end_node_of_subproperty c k'
            //Remove original transition
            Programs.remove_transition p_X n

    (p_X, ret, final_loc, [], Map.empty)

let instrument_G p formula (propertyMap : ListDictionary<CTL_Formula, int * Formula.formula>) (fairness_constraint : ((Programs.command list * Programs.command list) * Programs.command list list) option) isExistential =
    let p_G = Programs.copy p
    let final_loc = Programs.new_node p_G
    let p_G_copy = Programs.copy p_G
    //Add return value to instrumented program, and also add it to set to keep track of all the return values
    let ret = Formula.subcheck_return_var "0"
    p_G.vars := Set.add ret !p_G.vars
    //let cp_conditions = eliminate_redun propertyMap.[formula]
    let cp_conditions = propertyMap.[formula]
    let cp = cp_conditions |> List.map(fun (x,_) -> x)

    // 2. Instrument in the sub-property: Visit every state, and add links to the check for the sub-property.
    let node_to_end_of_subproperty_node_map = new System.Collections.Generic.Dictionary<int,int>()
    for n in !p_G.active do
        let (k,_,_) = p_G.transitions.[n]
        //For Bottom up, we're also checking that it's a node/cp that has a pre-condition
        if (k <> !p_G.initial) && not(node_to_end_of_subproperty_node_map.ContainsKey k) && (List.contains k cp) then
            // Create the two nodes between which we nest the encoding of the subproperty we consider:
            let (end_node_of_subproperty, start_node_for_subproperty) = generate_checker_instrumentation_nodes k p_G
            let ret_true_node = Programs.map p_G ("RET_TRUE" + n.ToString())
            let ret_false_node = Programs.map p_G ("RET_FALSE" + n.ToString())

            Programs.plain_add_transition p_G k [] start_node_for_subproperty

            add_subproperty_conditions p_G cp_conditions k isExistential start_node_for_subproperty ret_true_node ret_false_node

            add_fairness_check_transititions p_G fairness_constraint n ret ret_true_node ret_false_node end_node_of_subproperty

            //Hmm in the old AG we just repeated the commands, but it could just be a skip
            Programs.plain_add_transition p_G end_node_of_subproperty [] final_loc

            node_to_end_of_subproperty_node_map.Add (k, end_node_of_subproperty)

    for n in !p_G_copy.active do
        let (k,c,k') = p_G.transitions.[n]
        if(k <> !p_G.initial && (List.contains k cp)) then
            let end_node_of_subproperty = node_to_end_of_subproperty_node_map.[k]

            Programs.plain_add_transition p_G end_node_of_subproperty c k'
            Programs.remove_transition p_G n

    (p_G, ret, final_loc, [], Map.empty)

let instrument_F (pars : Parameters.parameters) p formula (propertyMap : ListDictionary<CTL_Formula, int * Formula.formula>) isTerminationOnly (fairness_constraint : ((Programs.command list * Programs.command list) * Programs.command list list) option) findPreconds isExistential =
    let p_F = Programs.copy p
    let final_loc = Programs.new_node p_F

    //Add return value to instrumented program, and also add it to set to keep track of all the return values
    let ret = Formula.subcheck_return_var "0"
    p_F.vars := Set.add ret !p_F.vars

    //Map from each node starting a loop to the corresponding __copied_ variable
    let copy_loop_var = new System.Collections.Generic.Dictionary<int, var>()
    let (p_loops, p_sccs) = Programs.find_loops p

    /// Copy of the original program, as p_AF is our working copy that gets changed all the time
    let p_F_copy = Programs.copy p_F

    //let cp_conditions = eliminate_redun propertyMap.[formula]
    let cp_conditions = propertyMap.[formula]
    let cp_propMap = cp_conditions |> List.map(fun (x,_) -> x)

    //Prepare node copies for the splitted-out AF instrumentation
    let loopnode_to_copiednode = new System.Collections.Generic.Dictionary<int,int>()
    for (_, scc_nodes) in p_sccs.Items do
        for node in scc_nodes do
            if not (loopnode_to_copiednode.ContainsKey node) then
                let copiednode = Programs.new_node p_F
                loopnode_to_copiednode.Add(node, copiednode)

    /// Gives the copy of the loopnode in the instrumented loop copy if DependencyPair-style lex. rfs are searched for
    let get_copy_of_loopnode node =
        if loopnode_to_copiednode.ContainsKey node then
            loopnode_to_copiednode.[node]
        else
            node

    //For every loop, we want to add a boolean copied value before each loop node, generate this variable here
    //Also determine the set of transitions outgoing frin the loop dominated by this cutpoint.
    for n in !p_F.active do
        let (_,_,k') = p_F.transitions.[n]
        if (p_loops.ContainsKey k') then
            let cutpoint_copy = get_copy_of_loopnode k'
            let copy = Formula.copy_var cutpoint_copy
            if not(copy_loop_var.ContainsKey(cutpoint_copy)) then
                copy_loop_var.Add(cutpoint_copy, copy)

    let node_to_scc_nodes =
       p_sccs.Items
    |> Seq.map (fun (_, scc_nodes) -> scc_nodes |> Seq.map (fun n -> (n, scc_nodes)))
    |> Seq.concat
    |> Map.ofSeq

    // 2. Instrument in the sub-property if we do more than termination.
    //    Visit every state, and check/add links to the check for the sub-property.
    //    If the sub-property holds, we may go to the final location directly, otherwise we just dangle there
    let node_to_end_of_subproperty_node_map = new System.Collections.Generic.Dictionary<int,int>()
    if not(isTerminationOnly) then
        for n in !p_F.active do
            let (k,_,_) = p_F.transitions.[n]
            if (k <> !p_F.initial) && not(node_to_end_of_subproperty_node_map.ContainsKey k) &&
                                            (List.contains k cp_propMap || p_loops.ContainsKey k) then

                // Create the two nodes between which we nest the encoding of the subproperty we consider:
                let (end_node_of_subproperty, start_node_for_subproperty) = generate_checker_instrumentation_nodes k p_F
                let proper_k = get_copy_of_loopnode k

                Programs.plain_add_transition p_F proper_k [] start_node_for_subproperty

                //See comments in AG to understand how this works.
                if List.contains k cp_propMap then
                    let ret_true_node = Programs.map p_F ("RET_TRUE" + n.ToString())
                    let ret_false_node = Programs.map p_F ("RET_FALSE" + n.ToString())
                    
                    add_subproperty_conditions p_F cp_conditions k isExistential start_node_for_subproperty ret_true_node ret_false_node

                    add_fairness_check_transititions p_F fairness_constraint n ret ret_true_node ret_false_node end_node_of_subproperty

                else if p_loops.ContainsKey k then
                    //Meaning that this cutpoint had no preconditions associated with it, meaning it was true.
                     //In G we ignored these cases, but in F they're necessary because it means we can exit!
                     //Thus this is the old strategy for instrumenting properties into F
                    // Set RET to 1/0 depending on the truth value of the subproperty:
                    Programs.plain_add_transition p_F
                        start_node_for_subproperty
                            [ (Programs.assign ret (Term.Const(bigint.One))) ]
                        end_node_of_subproperty
                    Programs.plain_add_transition p_F
                        start_node_for_subproperty
                            [ Programs.assume (Formula.falsec)
                            ; (Programs.assign ret (Term.Const(bigint.Zero))) ]
                        end_node_of_subproperty

                // If the subproperty holds, we may now go on to the final location. Otherwise, we will have to loop.
                Programs.plain_add_transition p_F
                    end_node_of_subproperty
                        [Programs.assume (Formula.Ge(Term.Var(ret),Term.Const(bigint.One)))]
                    final_loc
                node_to_end_of_subproperty_node_map.Add (k, end_node_of_subproperty)

    (*
      3. Add the instrumentation for the termination proof.
         For this, we create a second copy of each loop, to which we jump after some transitions, and in this 
         copy, we can do transformations that are unsound for the general case. Steps towards that:
          (1) Make a copy of each node occurring in a loop (done above, when filling loopnode_to_copiednode)
          (2) Instrument only the copied version, let program exist as before
          (3) Add jumps from cutpoints in the original version to cutpoints in the copied version
    *)

    let visited_cp_map = new System.Collections.Generic.Dictionary<int,(int*int)>()
    for n in !p_F_copy.active do
        let (k,cmds,k') = p_F.transitions.[n]
        if(k <> !p_F.initial) then
            let assume_ret_value_false_cmd =
                if isTerminationOnly then []
                else [Programs.assume (Formula.Eq(Term.Var(ret),Term.Const(bigint.Zero)))]

            let trans_stays_in_scc = if node_to_scc_nodes.ContainsKey k then node_to_scc_nodes.[k].Contains k' else false
            //If we do the AI first, every transition has a new assume at the beginning. We only want that in the instr loop
            let cmds_without_ai_res = if pars.did_ai_first then List.tail cmds else cmds
            let copied_k = get_copy_of_loopnode k

            if (p_loops.ContainsKey k) then //Source of the transition is a CP!
                let end_of_subproperty_node =
                    if isTerminationOnly then get_copy_of_loopnode k
                    else node_to_end_of_subproperty_node_map.[k]
                let copied_var = copy_loop_var.[copied_k]

                //This contains all nodes in the loop:
                let in_set = Map.find k p_loops

                if Set.contains k' in_set then
                    //Remove the old transition. We replace it.
                    Programs.remove_transition p_F n

                    //This is a CP, but we haven't visited it yet and thus have to add the nodes for the copying magic first:
                    if not(visited_cp_map.ContainsKey k) then
                        //First new path: Do the actual copying:
                        // - copy of CP to not_copied_node, where we check that we didn't copy yet (or the corresponding end of the nested subproperty check)
                        // - not_copied_node to copying, where we perform the actual copying
                        let not_copied_node = Programs.new_node p_F
                        Programs.plain_add_transition p_F
                            end_of_subproperty_node
                                (  Programs.assume (Formula.Lt(Term.Var(copied_var), Term.Const(bigint.One)))
                                 ::assume_ret_value_false_cmd)
                            not_copied_node

                        let copying = Programs.new_node p_F
                        //Below is for transitions where variables are not copied
                        Programs.plain_add_transition p_F
                            not_copied_node
                                ((Programs.assign copied_var (Term.Const(bigint.One)))
                                ::List.ofSeq(var_copy_commands p p_F copied_k))
                            copying

                        visited_cp_map.Add(k, (copying, not_copied_node))

                        //Second new path: We already copied our vars - now add path to the error loc on which we instrument in the rfs later on:
                        //This path has four steps:
                        // - CP to copy of CP (if we do a copy of the loop)
                        // - copy of CP to node_after_copying, where we check that we actually did copy values
                        // - node_after_copying to pre_final, where later on the rfs are added in
                        // - pre_final to final - we only need this for the CTL encoding
                        Programs.plain_add_transition p_F k [] copied_k

                        let node_after_copying = Programs.new_node p_F
                        if not(isTerminationOnly) then
                            Programs.plain_add_transition p_F
                                node_to_end_of_subproperty_node_map.[k]
                                      (Programs.assume (Formula.Ge(Term.Var(copied_var), Term.Const(bigint.One)))
                                      ::assume_ret_value_false_cmd)
                                node_after_copying
                        else
                            Programs.plain_add_transition p_F
                                copied_k
                                        (Programs.assume (Formula.Ge(Term.Var(copied_var), Term.Const(bigint.One)))
                                        ::assume_ret_value_false_cmd)
                                node_after_copying

                        let pre_final = Programs.new_node p_F
                        // Start with rf 'true' (0=0).
                        Programs.plain_add_transition p_F
                            node_after_copying
                                [ Programs.assume (Formula.Eq(Term.Const(bigint.Zero), Term.Const(bigint.Zero))) ]
                            pre_final

                        //If we reach the (pre-)final location, we had no ranking function => AF p might never be true! Hence, we return false to allow for backtracking
                        Programs.plain_add_transition p_F
                            pre_final
                                [ Programs.assign ret (Term.Const(bigint.Zero)) ]
                            final_loc

                    //Instead of original transition from CP, add one from the node in which we copied the variables:
                    let (copying, not_copied_node) = visited_cp_map.[k]
                    let copied_k' = get_copy_of_loopnode k'
                    //Add a copy of the transition starting in the node after we did the copying - but if we copied the loop out, we only need to do that for transitions in the loop.
                    if trans_stays_in_scc then
                        Programs.plain_add_transition p_F copying cmds_without_ai_res copied_k'
                    if pars.lexicographic then
                        //If we do lex rfs, also add one from the node in which we did not copy the variables (and don't, if we don't need it as above)
                        if trans_stays_in_scc then
                            if not(findPreconds) then
                                Programs.plain_add_transition p_F not_copied_node
                                    (assume_ret_value_false_cmd@cmds) copied_k'
                            else if p_sccs.ContainsKey k' then
                                if p_sccs.[k'].Contains k then
                                     Programs.plain_add_transition p_F not_copied_node
                                        (assume_ret_value_false_cmd@cmds) copied_k'
                            else
                                Programs.plain_add_transition p_F not_copied_node cmds copied_k'
                        else
                            Programs.plain_add_transition p_F end_of_subproperty_node cmds copied_k'
                    else
                        //If we're going to be finding lexicographic RFs, then we don't need to check for transitive closure,
                        //so we put extra assume(copied<1) on transitions out of a cutpoint.
                        if not(findPreconds) then
                            Programs.plain_add_transition p_F
                                end_of_subproperty_node (assume_ret_value_false_cmd@cmds) copied_k'
                         else if p_sccs.ContainsKey k' then
                                if p_sccs.[k'].Contains k then
                                    Programs.plain_add_transition p_F
                                        end_of_subproperty_node (assume_ret_value_false_cmd@cmds) copied_k'
                        else
                            Programs.plain_add_transition p_F end_of_subproperty_node cmds copied_k'

                    //Now also add a new transition from the original k to k' (where the iteration variable is incremented, if we need that)
                    Programs.plain_add_transition p_F k (cmds_without_ai_res) k'

                else // if Set.contains k' in_set
                    let new_out_cmmd = Programs.assume (Formula.Lt(Term.Var(copied_var), Term.Const(bigint.One)))::cmds_without_ai_res
                    let proper_k' = get_copy_of_loopnode k'
                    if not(findPreconds) then
                        Programs.plain_add_transition p_F end_of_subproperty_node (new_out_cmmd@assume_ret_value_false_cmd) proper_k'
                    else
                        Programs.plain_add_transition p_F end_of_subproperty_node new_out_cmmd proper_k'

            else // if(F_loops.ContainsKey k)
                // Other transitions are just copied. If we do loop duplication, we can avoid a few cases:
                let selected_node = if List.contains k cp_propMap then
                                        if isTerminationOnly then copied_k
                                        else node_to_end_of_subproperty_node_map.[k]
                                    else copied_k

                let trans_in_loop = (loopnode_to_copiednode.ContainsKey k) && (loopnode_to_copiednode.ContainsKey k')
                if trans_in_loop then
                    let copied_k' = loopnode_to_copiednode.[k']
                    if not(findPreconds) then
                        Programs.plain_add_transition p_F selected_node (assume_ret_value_false_cmd@cmds) copied_k'
                    else if p_sccs.ContainsKey k' then
                            if p_sccs.[k'].Contains k then
                                Programs.plain_add_transition p_F selected_node (assume_ret_value_false_cmd@cmds) copied_k'
                            else
                                Programs.plain_add_transition p_F selected_node cmds copied_k'
                    else
                        Programs.plain_add_transition p_F selected_node cmds copied_k'

        else // if(k <> !p_F.initial)
            let init_copied_var_cmmds = copy_loop_var |> Seq.map (fun x -> (Programs.assign x.Value (Term.Const(bigint.Zero))))
            if fairness_constraint.IsSome then
                p_F.transitions.[n] <- k, (cmds@(List.ofSeq(init_copied_var_cmmds))@
                    ([Programs.assume (Formula.Gt(Term.Var Formula.fair_proph_var,Term.Const(bigint.MinusOne)));
                            Programs.assign Formula.fair_proph_old_var (Term.Var Formula.fair_proph_var);
                                Programs.assign Formula.fair_term_var (Term.Const(bigint.Zero))])), k'
            else
                p_F.transitions.[n] <- k, (cmds@(List.ofSeq(init_copied_var_cmmds))), k'

    let loop_var_cmmd = copy_loop_var |> Seq.map (fun x -> Programs.assign x.Value (Term.Const(bigint.Zero)))
    p_F.vars := copy_loop_var |> Seq.fold (fun acc x -> Set.add x.Value acc) !p_F.vars

    let loopnode_to_copiednode = loopnode_to_copiednode |> Seq.map (fun x -> (x.Key, x.Value)) |> Map.ofSeq
    (p_F, ret, final_loc, List.ofSeq(loop_var_cmmd), loopnode_to_copiednode)

let instrument_AndOr p formula (propertyMap : ListDictionary<CTL_Formula, int * Formula.formula>) =
    let p_AndOr = Programs.copy p
    let final_loc = Programs.new_node p_AndOr
    //Add return value to instrumented program, and also add it to set to keep track of all the return values
    let ret = Formula.subcheck_return_var "0"
    p_AndOr.vars := Set.add ret !p_AndOr.vars

    //let cp_conditions = eliminate_redun propertyMap.[formula]
    let cp_conditions = propertyMap.[formula]

    // 2. Instrument in the sub-property only for the initial state
    let init_check_node = ref -1

    for n in !p_AndOr.active do
        let (k,_,k') = p_AndOr.transitions.[n]
        if k = !p_AndOr.initial then
            init_check_node := k'
    assert(!init_check_node <> -1)

    for n in !p_AndOr.active do
        let (k,c,k') = p_AndOr.transitions.[n]
        if k = !init_check_node then
            // Create the two nodes between which we nest the encoding of the subproperty we consider:
            let (end_node_of_subproperty, start_node_for_subproperty) = generate_checker_instrumentation_nodes k p_AndOr
            let ret_true_node = Programs.map p_AndOr ("RET_TRUE" + n.ToString())
            let ret_false_node = Programs.map p_AndOr ("RET_FALSE" + n.ToString())

            Programs.plain_add_transition p_AndOr k [] start_node_for_subproperty

            add_subproperty_conditions p_AndOr cp_conditions k false start_node_for_subproperty ret_true_node ret_false_node

            Programs.plain_add_transition p_AndOr ret_true_node [Programs.assign ret (Term.Const(bigint.One))] end_node_of_subproperty
            Programs.plain_add_transition p_AndOr ret_false_node [Programs.assign ret (Term.Const(bigint.Zero))] end_node_of_subproperty

            Programs.plain_add_transition p_AndOr end_node_of_subproperty c k'
            Programs.remove_transition p_AndOr n

            Programs.plain_add_transition p_AndOr end_node_of_subproperty [] final_loc

    (p_AndOr, ret, final_loc, [], Map.empty)

let bottomUp_AW p formula1 formula2 (propertyMap : ListDictionary<CTL_Formula, int * Formula.formula>) fairness_constraint =
    let p_AW = Programs.copy p

    if fairness_constraint <> None then
        raise (new System.NotImplementedException "Fairness for AW constaints not yet implemented")

    let final_loc = Programs.new_node p_AW
    //Add return value to instrumented program, and also add it to set to keep track of all the return values
    let ret1 = Formula.subcheck_return_var "1_1"
    let ret2 = Formula.subcheck_return_var "2_1"
    let ret = Formula.subcheck_return_var "0"
    p_AW.vars := Set.add ret !p_AW.vars
    p_AW.vars := Set.add ret1 !p_AW.vars
    p_AW.vars := Set.add ret2 !p_AW.vars
    
    //let cp_conditions1 = eliminate_redun propertyMap.[formula1]
    //let cp_conditions2 = eliminate_redun propertyMap.[formula2]
    let cp_conditions1 = propertyMap.[formula1]
    let cp_conditions2 = propertyMap.[formula2]
    let cps = Set.union (Set.ofList (cp_conditions1 |> List.map(fun (x,_) -> x)))
                             (Set.ofList (cp_conditions2 |> List.map(fun (x,_) -> x)))

    //Need to add true if the cp in one propertyMaps isn't there for the other.

    let node_to_end_of_subproperty_node_map = new System.Collections.Generic.Dictionary<int,int>()
    for n in !p_AW.active do
        let (k,c,k') = p_AW.transitions.[n]
        if(k <> !p_AW.initial) then
            if (k <> !p_AW.initial) && not(node_to_end_of_subproperty_node_map.ContainsKey k) && (cps.Contains k) then

                let (end_node_of_subproperty, start_node_for_subproperty) = generate_checker_instrumentation_nodes k p_AW
                
                Programs.plain_add_transition p_AW k [] start_node_for_subproperty

                // Create two nodes to check the first subproperty we consider:
                let ret_true_node1 = Programs.map p_AW ("RET1_TRUE" + n.ToString())
                let ret_false_node1 = Programs.map p_AW ("RET1_FALSE" + n.ToString())

                add_subproperty_conditions p_AW cp_conditions1 k false start_node_for_subproperty ret_true_node1 ret_false_node1

                // Connect these to a checker for the second subproperty:
                let second_node_for_subproperty = Programs.map p_AW ("second_node_for_subproperty" + n.ToString())
                Programs.plain_add_transition p_AW ret_true_node1 [Programs.assign ret1 (Term.Const(bigint.One));
                                                                        Programs.assign ret (Term.Const(bigint.One))] second_node_for_subproperty
                Programs.plain_add_transition p_AW ret_false_node1 [Programs.assign ret1 (Term.Const(bigint.Zero));
                                                                        Programs.assign ret (Term.Const(bigint.Zero))] second_node_for_subproperty
                                 
                // Create two nodes to check the second subproperty we consider:
                let ret_true_node2 = Programs.map p_AW ("RET_TRUE" + n.ToString())
                let ret_false_node2 = Programs.map p_AW ("RET_FALSE" + n.ToString())

                add_subproperty_conditions p_AW cp_conditions2 k false start_node_for_subproperty ret_true_node2 ret_false_node2

                // Connect these to the end of the overall checker
                Programs.plain_add_transition p_AW ret_true_node2 [Programs.assign ret2 (Term.Const(bigint.One));
                                            Programs.assign ret (Term.Const(bigint.One))] end_node_of_subproperty
                Programs.plain_add_transition p_AW ret_false_node2 [Programs.assign ret2 (Term.Const(bigint.Zero))] end_node_of_subproperty

                Programs.plain_add_transition p_AW
                    end_node_of_subproperty
                        [Programs.assume (Formula.Le(Term.var(ret2),(Term.Const(bigint.Zero))));
                         Programs.assume (Formula.Le(Term.var(ret1),(Term.Const(bigint.Zero))))]
                    final_loc

                Programs.plain_add_transition p_AW
                    end_node_of_subproperty
                        [Programs.assume (Formula.Ge(Term.var(ret2),(Term.Const(bigint.One))))]
                    final_loc

                //Only continue to the next transition if the first property is satisfied, but the second isn't.
                Programs.plain_add_transition p_AW end_node_of_subproperty
                    ([Programs.assume (Formula.Le(Term.var(ret2),(Term.Const(bigint.Zero)))); Programs.assume (Formula.Ge(Term.var(ret),(Term.Const(bigint.One))))]@c)
                  k'
                //Remove original transition
                Programs.remove_transition p_AW n

                node_to_end_of_subproperty_node_map.Add (k, end_node_of_subproperty)
    (p_AW, ret, final_loc, [], Map.empty)

let bottomUp_AX p formula (propertyMap : ListDictionary<CTL_Formula, int * Formula.formula>) fairness_constraint =
    instrument_X p formula propertyMap fairness_constraint false
let bottomUp_EX p formula (propertyMap : ListDictionary<CTL_Formula, int * Formula.formula>) fairness_constraint =
    instrument_X p formula propertyMap fairness_constraint true

let bottomUp_AG p formula propertyMap fairness_constraint =
    instrument_G p formula propertyMap fairness_constraint false
let bottomUp_EG (pars : Parameters.parameters) p formula (propertyMap : ListDictionary<CTL_Formula, int * Formula.formula>) isTerminationOnly fairness_constraint findPreconds =
    //is_false in EG is meant for the purpose of recurrent sets, so in this case we attempt to find termination only for AF
    instrument_F pars p formula propertyMap isTerminationOnly fairness_constraint findPreconds true

let bottomUp_AF (pars : Parameters.parameters) p formula propertyMap isTerminationOnly fairness_constraint findPreconds =
    instrument_F pars p formula propertyMap isTerminationOnly fairness_constraint findPreconds false
let bottomUp_EF p formula (propertyMap : ListDictionary<CTL_Formula, int * Formula.formula>) fairness_constraint =
    instrument_G p formula propertyMap fairness_constraint true

//Instrumentation of the proposition happens here because in the AF/AG case, I automatically incorporate it.
//Thus, this is for the case that we have something just like x = 0 without AF or AG
let instrument_Prop p_orig e =
    let p_Prop = Programs.copy p_orig
    for n in !p_Prop.active do
        let (k,c,k') = p_Prop.transitions.[n]
        if k = -1 then
            p_Prop.transitions.[n] <- k, (c@[(Programs.assume e)]), k'

    let error_loc = Programs.new_node p_Prop
    Programs.plain_add_transition p_Prop -1 [Programs.assume (Formula.Not(e))] error_loc

    (p_Prop, error_loc, e)

/// Returns the programs that encodes both input program and the checked property,
/// the error location and a map from cutpoints to the first transition leading to
/// the error location (this is where the rfs are later added in)
let mergeProgramAndProperty (pars : Parameters.parameters) p actl_prop (is_false : bool) propertyMap (fairness_constraint : (Formula.formula * Formula.formula) option) findPreconds next =
    Programs.remove_unreachable p
    if pars.dottify_input_pgms then
        Output.print_dot_program p "input.dot"

    //Propechy variable old and new
    let proph_var = Formula.fair_proph_var
    let proph = Term.Var Formula.fair_proph_var
    let proph_old_var = Formula.fair_proph_old_var
    let proph_old = Term.Var Formula.fair_proph_old_var

    //Changing the two formula of fairness constraints into 3 commands (Disjunction and what not), in order to instrument in easily
    //An array of array pairs
    let fairness_constraint : ((Programs.command list * Programs.command list) * Programs.command list list) option =
        if fairness_constraint.IsSome then
            let (fair_1,fair_2) = fairness_constraint.Value
            let not_fair_1 =
                   polyhedra_dnf (Formula.negate(fair_1))
                |> split_disjunction
                |> List.map(fun x -> [Programs.assume x; Programs.assume (Formula.Eq(proph_old, proph))])

            Some(
                    ([ Programs.assume fair_1
                     ; Programs.assign proph_var (Term.Sub (proph,(Term.Const(bigint.One))))],

                     [ Programs.assume (Formula.Lt(proph,proph_old))
                     ; Programs.assign proph_old_var proph
                     ; Programs.assume (Formula.Gt(proph, Term.Const(bigint.MinusOne)))]
                    ),

                     not_fair_1
                    @[[ Programs.assume fair_2
                      ; Programs.assign proph_var (Term.nondet)
                      ; Programs.assign proph_old_var proph
                      ; Programs.assume (Formula.Gt(proph, Term.Const(bigint.MinusOne)))];

                      [ Programs.assume (Formula.Eq(Term.Var(Formula.fair_term_var),Term.Const(bigint.One)))
                      ; Programs.assign proph_var (Term.nondet)
                      ; Programs.assign proph_old_var proph
                      ; Programs.assume (Formula.Gt(proph, Term.Const(bigint.MinusOne)))]]
                )

        else None

    //Do the actual instrumentation, calling the right method depending on the outermost atom:
    let instrument ctl_prop =
        match ctl_prop with
        | Atom a -> instrument_Prop p a |> Either.IsAProp
        | CTL_And(_,_)
        | CTL_Or(_,_)  -> instrument_AndOr p ctl_prop propertyMap |> Either.IsNotAProp
        | AW(e1,e2) -> bottomUp_AW p e1 e2 propertyMap fairness_constraint |> Either.IsNotAProp
        | AX e -> bottomUp_AX p e propertyMap fairness_constraint |> Either.IsNotAProp
        | EX e -> bottomUp_EX p e propertyMap fairness_constraint |> Either.IsNotAProp
        | AF e -> bottomUp_AF pars p e propertyMap is_false fairness_constraint findPreconds |> Either.IsNotAProp
        | EF e -> bottomUp_EF p e propertyMap fairness_constraint |> Either.IsNotAProp
        | AG e -> bottomUp_AG p e propertyMap fairness_constraint |> Either.IsNotAProp
        | EG e -> bottomUp_EG pars p e propertyMap is_false fairness_constraint findPreconds |> Either.IsNotAProp
        | EU _ -> raise (new System.NotImplementedException "EU constraints not yet implemented")

    //Returns error location, and modifies the program to include it
    let (final_loc, error_loc, p_final, loc_copy_pair) = 
        match instrument actl_prop with
        |Either.IsAProp (p_Prop : Programs.Program, error_loc, _) ->
            Output.print_dot_program p_Prop "input__Prop_converted.dot"
            (error_loc,error_loc, p_Prop, Map.empty)
        |Either.IsNotAProp (p_final,p_ret,final_loc, _, loc_copy_pair) ->
            let error_loc = Programs.new_node p_final
            Programs.plain_add_transition p_final final_loc [(Programs.assume (Formula.Le(Term.Var(p_ret), Term.Const(bigint.Zero))))] error_loc
            (final_loc,error_loc, p_final, loc_copy_pair)

    ///Maps cutpoint to the index of the transition from it that leads to the error location (that's where the RFs will go!)
    let cp_rf = new System.Collections.Generic.Dictionary<int, int>()

    //Maps first node on the path out of an instrumented loop (to the error location) to the corresponding CP:
    let cp_rf_init = new System.Collections.Generic.Dictionary<int, int>()
    for n in !p_final.active do
        let (_, cmds, k') = p_final.transitions.[n]
        for cmd in cmds do
            match cmd with
            |   Programs.Assume(_,Formula.Ge(Term.Var(v), Term.Const(c))) when is_copied_var v && c = bigint.One ->
                let temp = v.Split '_'
                let num_cp = int(temp.[(temp.Length)-1])
                cp_rf_init.Add(k', num_cp)
            | _ -> ()
    //Maps CP to the the transition leading from the first node on the corresponding path to the error location
    for n in !p_final.active do
        let (k, cmds, _) = p_final.transitions.[n]
        if cp_rf_init.ContainsKey(k) then
            match cmds with
            | [Programs.Assume(_,Formula.Eq(Term.Const(c1), Term.Const(c2)))] when c1 = bigint.Zero && c2 = bigint.Zero ->
                cp_rf.Add(cp_rf_init.[k], n)
            | _ -> ()

    //Constants propagation
    if not(next) then
        Programs.prop_constants p_final (Analysis.constants p_final)
    Programs.symbconsts_init p_final

    // Clean up program using live variable analysis (guard variables occurring in our properties, though)

    Programs.let_convert p_final (Analysis.liveness p_final (CTL_Formula.freevars actl_prop))
    if pars.dottify_input_pgms then
        Output.print_dot_program p_final ("input__instrumented.dot")

    (p_final, final_loc, error_loc, cp_rf, loc_copy_pair)
