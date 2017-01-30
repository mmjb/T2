////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      Lasso
//
//  Abstract:
//
//      Lasso-based termination refinement a la TERMINATOR
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


module Microsoft.Research.T2.Lasso

open Utils
open Log
open Term
open Formula
open Programs
open Rankfunction
open Instrumentation
open SafetyInterface

//If we have a lex RF with a certain RF appearing more than once, then it could be simplified to be of shorter length
let simplify_lex_RF (rf_list:term list) (bnd_list:term list) =
    let old_list = ref (List.zip rf_list bnd_list)

    //Construct partitioned_list, which is old_list with chunks of the same RF grouped together
    let mutable partitioned_list = []
    while !old_list <> List.empty do
        let (head_rf,_) = List.head !old_list
        match List.tryFindIndex (fun (rf, _) -> rf <> head_rf) !old_list with
        | Some index ->
            partitioned_list <- partitioned_list@[[for i in 0..(index-1) -> (!old_list).[i]]]
            old_list := [for i in index..((!old_list).Length-1) -> (!old_list).[i] ]
        | None -> 
            partitioned_list <- partitioned_list@[!old_list]
            old_list := List.empty

    //for each chunk of the same RF, reduce to one RF with the minimum bound
    let partitioned_list = partitioned_list //rebind to use in closure
    let old_list_cleaned =
        [for partition in partitioned_list do
            let (rfs,bounds) = List.unzip partition
            for rf in rfs do assert (rf=rfs.Head)
            let min_bnd = List.min bounds
            yield (rfs.Head,min_bnd)]

    let mutable simplified_list = List.empty
    for (rf_to_add, bnd_to_add) in old_list_cleaned do
        //if the relation represented by the rf_to_add isn't already covered by the list so far...
        if not (List.exists (fun (rf,bnd) -> rf = rf_to_add && bnd <= bnd_to_add) simplified_list) then
        //then add it on
            simplified_list <- simplified_list@[(rf_to_add, bnd_to_add)]

    List.unzip simplified_list

///Takes the three formulae lists of a lex RF and gives a single formula expressing the lex RF
let make_lex_formula (lex_rf_check_formulas : (formula * formula * formula) list)=
    [
        for i in 0 .. lex_rf_check_formulas.Length - 1 do
            yield Formula.conj <| Instrumentation.make_lex_RF_ith_check_component lex_rf_check_formulas i
    ] |> Formula.disj

let check_lex_rankfunction_valid (lex_order:Relation.relation list) (rf_list:term list) (bnd_list:term list) =
    //printfn "lex_order:\n %A" lex_order
    for rf in rf_list do
        for v' in Term.freevars rf do
            let v = Var.unprime_var v'
            assert (not <| Formula.is_copied_var v)
            assert (not <| Formula.is_snapshot_var v)

    for bnd in bnd_list do
        match bnd with
        | Const _ -> ()
        | _ -> assert (false)

    //All the relations should have the same pre and postvars (as they have been through Rankfunction.lexsynthesis, which standardises the postvars)
    let prevars = Relation.prevars (List.head lex_order)
    let postvars = Relation.postvars (List.head lex_order)

    let find_post v =
        List.find (fun x -> Var.unprime_var v = Var.unprime_var x) postvars

    let post_subst v = if List.contains v prevars then Term.var (Var.var (find_post v)) else Var v
    let lex_rf_check_formulas =
        [
            for (rf, bnd) in Seq.zip rf_list bnd_list do
                let post_rf = Term.subst post_subst rf
                yield (Formula.Lt(post_rf, rf), Formula.Le(post_rf, rf), Formula.Ge(rf, bnd))
        ]
    //Check for each relation that the rf is decreasing and bounded for that relation and not increasing for all prior relations
    let lex_formula = make_lex_formula lex_rf_check_formulas

    //This little dance here is needed because some of our ranking functions are affine and use __const_1 as extra variable to achieve that.
    //We need to fix it to 1 -- otherwise z3 will do weird stuff like setting it to 14.
    let const_1_var = Formula.const_var bigint.One
    let const_1_prevar = Var.prime_var const_1_var 0
    let const_1_postvar = Var.var (const_1_var + "^post")
    let const_formula =
        Formula.And(
            Formula.Eq(Term.Var(const_1_var), Term.constant 1),
                Formula.And(
                    Formula.Eq(Term.Var(const_1_prevar), Term.constant 1),
                    Formula.Eq(Term.Var(const_1_postvar), Term.constant 1)))

    //Note we have already done simplify_lex_RF so we might have fewer RFs than rels
    for rel in lex_order do
        let check = Formula.conj [const_formula; Relation.formula rel; Formula.Not lex_formula]
        //If you are interested in a model for the failure:

        let res = Z.solve [(Formula.z3 check)]
        if res.IsSome then
            printfn "Considered relation: %A" rel
            printfn "Failing formula:\n %A" check
            printfn "Formula SAT, model is:"
            printfn "%s" (res.Value.ToString ())

        assert(check |> Formula.unsat)

let check_rankfunction_valid (pars : Parameters.parameters) cycle rf bnd =
    for v in Term.freevars rf do
        let v = Var.unprime_var v
        assert (not <| Formula.is_copied_var v)
        assert (not <| Formula.is_snapshot_var v)

    match bnd with
    | Const _ -> ()
    | _ -> assert (false)

    let prevars = Relation.prevars cycle
    let postvars = Relation.postvars cycle

    let find_post v =
        List.find (fun x -> Var.unprime_var v = Var.unprime_var x) postvars

    let post_subst v = if List.contains v prevars then Term.var (Var.var (find_post v)) else Var v

    let postrf = Term.subst post_subst rf

    let rf_not_decreases = Formula.Ge(postrf, rf)
    let rf_not_bounded = Formula.Lt(rf, bnd)

    log pars "Checking rankfunction"

    //Formula.pp rf_not_decreases |> log
    assert(Formula.conj [Relation.formula cycle; rf_not_decreases] |> Formula.unsat)

    //Formula.pp rf_not_bounded |> log
    assert(Formula.conj [Relation.formula cycle; rf_not_bounded] |> Formula.unsat)

let path_invariant stem cycle =
    let flatten_cmds = List.collect (fun (_ , cs, _) -> cs) 
    let stem_cmds = flatten_cmds stem
    let cycle_cmds = flatten_cmds cycle

    // Subst constant vars to real constants in prep for octagon-based abstract interpretation
    let stem_cmds' = List.map Programs.const_subst stem_cmds
    let cycle_cmds' = List.map Programs.const_subst cycle_cmds

    Analysis.path_invariant stem_cmds' cycle_cmds'

//WF = cutpoint,rf,bnd
//Lex_WF = cutpoint,decr_list,not_incr_list,bnd_list
//Poly_WF = the lexicographic polyranking conditions in DNF form.
type Refinement = CEX of Counterexample.cex
                | Lex_WF of int * (Formula.formula * Formula.formula * Formula.formula) list
                | Poly_WF of Formula.formula list list
                | Transition_Removal of int list

let exist_past_lex_options cp lex_info =
    let past_lex_options = lex_info.past_lex_options.[cp]
    past_lex_options.IsEmpty |> not

let print_lasso stem cycle =
    printf "LASSO----------------------------\n"
    printf "Stem:\n"
    print_path stem
    printf "Cycle:\n"
    print_path cycle
    printf "---------------------------\n"

///////////////////////////////////////////////////////////////////////////////
//////////////////// helper functions for RF construction /////////////////////
///////////////////////////////////////////////////////////////////////////////

let get_saved_term_var_for_var cutpoint (v': string) =
    let v = Var.unprime_var v'
    let snapshot_var =
        if Formula.is_const_var v then
            v
        else
            Formula.state_snapshot_var cutpoint v
    snapshot_var |> Var.var |> Term.var

let get_current_term_var_for_var (v: Var.var) =
    v |> Var.unprime_var |> Var.var |> Term.var

let rf_for_new_and_saved_vars rf cutpoint =
    (Term.subst get_current_term_var_for_var rf, Term.subst (get_saved_term_var_for_var cutpoint) rf)

///Converts the RF and bound lists to the triple formula lists
let lex_rf_to_check_formulas rf_list (bnd_list:Term.term list) cutpoint =
    let (new_rf_list, saved_rf_list) = List.unzip <| List.map (fun rf -> rf_for_new_and_saved_vars rf cutpoint) rf_list

    [
        for i in 1..rf_list.Length do
            yield (Formula.Lt(new_rf_list.[i-1], saved_rf_list.[i-1]),
                   Formula.Le(new_rf_list.[i-1], saved_rf_list.[i-1]),
                   Formula.Ge(saved_rf_list.[i-1], bnd_list.[i-1]))
    ]

///Converts the rf and bound to the "decreasing" and "bounded" formulae
let rankfunction_to_argument rf bnd cutpoint =
    let (new_rf, saved_rf) = rf_for_new_and_saved_vars rf cutpoint
    (Formula.Lt(new_rf, saved_rf), Formula.Ge(saved_rf, bnd))

///Converts a rf to the "bounded below by zero" formula
let bounded_fn_to_arg rf cutpoint =
    let saved_rf = Term.subst (get_saved_term_var_for_var cutpoint) rf
    Formula.Ge(saved_rf, Term.constant 0)

///Converts a rf to the "unaffected" formula
let unaff_fn_to_arg rf cutpoint =
    let new_rf = Term.subst get_current_term_var_for_var rf
    let saved_rf = Term.subst (get_saved_term_var_for_var cutpoint) rf
    Formula.Le(new_rf, saved_rf)

///Converts a rf and aux_rf to the "rf increases by no more than aux_rf" formula
let lim_incr_to_arg rf aux_rf cutpoint =
    let new_rf = Term.subst get_current_term_var_for_var rf
    let saved_rf = Term.subst (get_saved_term_var_for_var cutpoint) rf
    let saved_aux_rf = Term.subst (get_saved_term_var_for_var cutpoint) aux_rf
    Formula.Le(new_rf, Term.Add(saved_rf,saved_aux_rf))

///Converts a rf to the "negative" formula
let neg_fn_to_arg rf cutpoint =
    Formula.Lt(Term.subst (get_saved_term_var_for_var cutpoint) rf, Term.constant 0)

///Takes in some lexicographic solutions and puts them in past_lex_options in case we want to use them later
let store_lex_options cp more_options lex_info =
    let options = Map.find cp lex_info.past_lex_options
    lex_info.past_lex_options <- Map.add cp (more_options@options) lex_info.past_lex_options

///Tries to find a Lex_WF or Program_Simplification
let find_lex_RF (pars : Parameters.parameters) (p:Programs.Program) cutpoint cycle_rel lex_info =
    let old_partial_order = Map.find cutpoint lex_info.partial_orders
    match Rankfunction.synthesis_lex pars p cutpoint cycle_rel old_partial_order with
    | Some(Lexoptions(lexoptions)) ->
            //a function to turn a Lex_RF into a Lex_WF Refinement
            let process_lex_RF (lex_soln:Lex_RF) =
                let head = (lex_soln = lexoptions.Head)
                let (new_partial_order,rf_list,bnd_list) = List.unzip3 lex_soln

                if head && pars.print_log then
                    Log.log pars <| sprintf "Lex RF candidate before simplifying:\n %A\n with bounds:\n %A at CP %d" rf_list bnd_list cutpoint

                let (simp_rf_list,simp_bnd_list)=simplify_lex_RF rf_list bnd_list

                if head && pars.print_log then
                    Log.log pars <| sprintf "Lex RF candidate after simplifying:\n %A\n with bounds:\n %A at CP %d" simp_rf_list simp_bnd_list cutpoint
                    Log.log pars <| sprintf "Checking lexicographic RF..."

                //note we check all the lex RFs at this point, not just the one we're going to instrument
                check_lex_rankfunction_valid new_partial_order simp_rf_list simp_bnd_list

                (lex_rf_to_check_formulas simp_rf_list simp_bnd_list cutpoint, new_partial_order)

            //process all the lex options now
            let processed_lexoptions = List.map process_lex_RF lexoptions

            //choose the head to be instrumented; store the others in past_lex_options in case we want to use them later
            let (rf_checks, new_partial_order) = processed_lexoptions.Head
            lex_info.partial_orders <- Map.add cutpoint new_partial_order lex_info.partial_orders

            let other_solns = processed_lexoptions.Tail
            store_lex_options cutpoint other_solns lex_info

            Some(Lex_WF(cutpoint, rf_checks))
    | Some(Program_Simplification(toremove)) -> Some(Transition_Removal(toremove))
    | None ->
            log pars "Couldn't find a lexicographic rank function"
            None

///Tries to find a Lex_WF, when we're doing the init_cond improvement
let find_lex_RF_init_cond (pars : Parameters.parameters) (p:Programs.Program) cutpoint cycle_rel lex_info =
    let current_partial_orders = Map.find cutpoint lex_info.partial_orders_init_cond
    let old_partial_order = Map.find lex_info.current_counter current_partial_orders
    let counter = lex_info.current_counter

    match Rankfunction.synthesis_lex pars p cutpoint cycle_rel old_partial_order with
    | Some(Lexoptions(lexoptions)) ->
            let lex_soln = List.head lexoptions
            let (new_partial_order,rf_list,bnd_list) = List.unzip3 lex_soln

            let new_current_partial_orders = Map.add counter new_partial_order current_partial_orders
            lex_info.partial_orders_init_cond <- Map.add cutpoint new_current_partial_orders lex_info.partial_orders_init_cond

            if pars.print_log then
                Log.log pars <| sprintf "Lex RF candidate before simplifying:\n %A\n with bounds:\n %A at CP %d" rf_list bnd_list cutpoint

            let (simp_rf_list,simp_bnd_list)=simplify_lex_RF rf_list bnd_list

            if pars.print_log then
                Log.log pars <| sprintf "Lex RF candidate after simplifying:\n %A\n with bounds:\n %A at CP %d" simp_rf_list simp_bnd_list cutpoint

            check_lex_rankfunction_valid new_partial_order simp_rf_list simp_bnd_list

            let check_formulas = lex_rf_to_check_formulas simp_rf_list simp_bnd_list cutpoint

            Some(Lex_WF(cutpoint, check_formulas))
    | Some(Program_Simplification(toremove)) -> Some(Transition_Removal(toremove))
    | None ->
            log pars "Couldn't find a lexicographic rank function"
            None

//Make a dot file of the poly trees
let dot_poly_trees (trees:poly_tree list) (fname : string) =
    let h = new System.IO.StreamWriter(fname)
    fprintf h "digraph program {\nnode [shape=box];\n" ;

    let counter = ref 0

    //n is the label of the node at the top of the tree
    let rec print_tree (tree:poly_tree) (n:int) =
        match tree with
        | poly_tree.N(_,rf) ->
            //fprintf h "node%d [ color = red label = \"N. index: %d. fn: %A\" ];\n" n index rf
            fprintf h "node%d [ color = red label = \"N\\n %A\" ];\n" n rf
        | poly_tree.U(_)->
            //fprintf h "node%d [ color = gray label = \"U. index: %d.\" ];\n" n index
            fprintf h "node%d [ color = gray label = \"U\" ];\n" n
        | poly_tree.EN(_,rf,children) ->
            //fprintf h "node%d [ color = blue label = \"EN. index: %d. fn: %A\" ];\n" n index rf
            fprintf h "node%d [ color = blue label = \"EN\\n %A\" ];\n" n rf
            for child in children do
                incr counter
                let child_label = !counter
                let child_index =
                    match child with
                    |poly_tree.EN(index,_,_) -> index
                    |poly_tree.N(index,_) -> index
                    |poly_tree.U(index) -> index

                fprintf h "node%d -> node%d [label = %d];\n" n child_label child_index
                print_tree child child_label

    for tree in trees do
        print_tree tree !counter
        //increase counter by one between trees so that they're detached
        incr counter

    fprintf h "};\n"
    h.Dispose()
    printf "Created %s\n" fname

///Convert a lexicographic polyranking function (i.e. list of trees) and give out the formulae to be put in the checkers in DNF
let make_poly_checkers (trees:poly_tree list) cutpoint =
    //checkers is a dictionary from i to L_i, where L_i is the ith lexicographic option
    //and the lexicographic polyranking termination argument is "L_1 or L_2 or ... or L_n"
    let checkers = new System.Collections.Generic.Dictionary<int,Formula.formula list>()
    for i in 1..trees.Length do
        checkers.Add(i,[])

    //put in the bounded constraints
    for i in 1..trees.Length do
        let tree = trees.[i-1]
        match tree with
        | poly_tree.EN(_,rf,_) -> checkers.[i] <- (bounded_fn_to_arg rf cutpoint)::checkers.[i]
        | _                    -> failwith "unexpected"

    //now all the other constraints
    let rec poly_tree_to_checkers (tree:poly_tree) =
        match tree with
        | poly_tree.EN(_, rf, children) ->
            for child in children do
                match child with
                | poly_tree.U(child_index) ->
                    checkers.[child_index] <- (unaff_fn_to_arg rf cutpoint)::checkers.[child_index]
                | poly_tree.N(child_index, child_rf) ->
                    checkers.[child_index] <- (lim_incr_to_arg rf child_rf cutpoint)::checkers.[child_index]
                | poly_tree.EN(child_index, child_rf, _) ->
                    checkers.[child_index] <- (lim_incr_to_arg rf child_rf cutpoint)::checkers.[child_index]
                    poly_tree_to_checkers child
        | poly_tree.N(index,rf) ->
            checkers.[index] <- (neg_fn_to_arg rf cutpoint)::checkers.[index]
        | poly_tree.U(_) -> ()
    for tree in trees do (poly_tree_to_checkers tree)

    //now checkers should be correct. yield a list
    [for i in 1..trees.Length -> checkers.[i]]

/// counter to name the poly tree debug output dot files uniquely
let tree_counter = ref 0

let find_lex_poly_RF_with_fixed_depth (pars : Parameters.parameters) cycle_rel old_partial_order polyrank_depth =
    match Rankfunction.synthesis_poly_lex cycle_rel old_partial_order polyrank_depth with
    |Some polyoptions ->
        log pars <| sprintf "Found lexicographic polyranking function of depth %d:" polyrank_depth
        Some(polyoptions)
    |None->
        log pars <| sprintf "Couldn't find a lexicographic polyranking function of depth %d." polyrank_depth
        None

///Tries to find a Lex_Poly_RF
let find_lex_poly_RF (pars : Parameters.parameters) cutpoint cycle_rel lex_info =
    let old_partial_order = Map.find cutpoint lex_info.partial_orders
    let mutable polyrank_depth = 2
    let mutable poly_found = None
    while (poly_found = None) && (polyrank_depth <= pars.polyrank_max_depth) do
        poly_found <- find_lex_poly_RF_with_fixed_depth pars cycle_rel old_partial_order polyrank_depth
        if (poly_found).IsNone then
            if polyrank_depth < pars.polyrank_max_depth then
                polyrank_depth <- polyrank_depth+1
                log pars <| sprintf "Increasing depth of search to %d" polyrank_depth
            else
                polyrank_depth <- polyrank_depth+1
                log pars <| sprintf "Reached polyrank depth limit of %d" pars.polyrank_max_depth

    ///Takes the list of poly_trees and returns the top level RF of each
    let top_level_rfs trees =
        [for tree in trees do
            match tree with
            |poly_tree.EN(_,rf,_) -> yield rf
            |_ -> failwith "unexpected"
        ]

    match poly_found with
    | None -> None
    | Some(polyoptions) ->
        //take the first solution
        let poly_soln = polyoptions.Head
        let (new_partial_order,trees) = poly_soln
        assert (new_partial_order.Length = trees.Length)
        log pars <| sprintf "top level RFs: %A" (top_level_rfs trees)

        if pars.dottify_input_pgms then
            dot_poly_trees trees (sprintf "input_poly_tree_%d.dot" !tree_counter)
            incr tree_counter

        lex_info.partial_orders <- Map.add cutpoint new_partial_order lex_info.partial_orders

        //note we aren't storing alternative polyranking fns
        //we aren't checking validity either

        //turn the tree into lists of formulae ready to be implemented as checkers
        let poly_checkers = make_poly_checkers trees cutpoint

        Some(Poly_WF(poly_checkers))

///////////////////////////////////////////////////////////////////////////////
//// Main counterexample-guided refinement functions, searching for new RFs ///
///////////////////////////////////////////////////////////////////////////////

/// Return the appropriate type of Refinement or none
let refine_cycle (pars : Parameters.parameters) (p:Programs.Program) cutpoint cycle cycle_rel (lex_info:LexicographicInfo) =
    //are we doing the "detecting initial condition" improvement for this cutpoint?
    let init_cond = Map.find cutpoint lex_info.cp_init_cond

    let polyranking = Map.find cutpoint lex_info.cp_polyrank

    if pars.print_log then
        sprintf "Refining temporal argument for cycle:" |> log pars
        cycle |> List.concatMap (fun (_, cs, _) -> cs) |> Programs.commands2pp |> log pars

    if not polyranking then
        if not init_cond then
            find_lex_RF pars p cutpoint cycle_rel lex_info
        else
            find_lex_RF_init_cond pars p cutpoint cycle_rel lex_info
    else
        find_lex_poly_RF pars cutpoint cycle_rel lex_info

let split_path_for_cp pi cp =
    let rec split_path_for_cp' pi cp stem_acc =
        match pi with 
        //we've reached the point where we make our copies. From here on, we are in the cycle
        | (_, Programs.Assign(_, v, Term.Const c), _) :: pi' when c = bigint.One && v = Formula.took_snapshot_var cp ->
            (List.rev stem_acc, pi')
        | step :: pi' ->
            split_path_for_cp' pi' cp (step::stem_acc)
        | [] -> dieWith "Could not split counterexample into stem/cycle"
    split_path_for_cp' pi cp []

let investigate_cex_for_fixed_cp (pars : Parameters.parameters) (p:Programs.Program) (reachGraph : SafetyProver) pi cp (lex_info:LexicographicInfo) =
    Log.log pars <| sprintf "Investigating counterexample for cutpoint %d" cp

    //This code is for initial condition detection. It works out which initial condition path pi_uncut belongs to
    if (lex_info.cp_init_cond).[cp] then
        let rho = init_cond_var cp
        let mutable counter = -1
        for (_,cmd,_) in pi do
            match cmd with
            | Programs.Assume(_,Formula.Eq(Term.Var(v),Term.Const(n))) when (v=rho) -> counter <- int n
            | _ -> ()
        Log.log pars <| sprintf "Initial condition counter of this counterexample: %d" counter
        lex_info.current_counter <- counter

    let (stem_pre_clean, cycle_pre_clean) = split_path_for_cp pi cp
    let collapsed_cycle_pre = cycle_pre_clean |> collapse_path
    let stem_pre_clean = Symex.slice_path (stem_pre_clean |> collapse_path) collapsed_cycle_pre
    let cycle_pre_clean = Symex.slice_path collapsed_cycle_pre []

    let remove_instrumentation_cmds path =
        let is_instr_cmd cmd = Programs.freevars [cmd] |> Set.exists is_instr_var
        path |> List.map (fun (k, cmds, k') -> (k, List.filter (fun c -> not (is_instr_cmd c)) cmds, k'))
    let stem = remove_instrumentation_cmds stem_pre_clean
    let cycle = remove_instrumentation_cmds cycle_pre_clean
    
    let pi_commands = List.map (fun (_,x,_) -> x) pi
    let pi_vars_cleaned = pi_commands |> Programs.freevars |> Set.filter (fun v -> not (Formula.is_instr_var v))

    if pars.print_log then print_lasso stem cycle

    //Add information about the used constants to the cycle
    let strengthened_cycle = (-1, Programs.consts_cmds cycle, -1)::cycle
    let strengthened_cycle_rel = Programs.cmdPathToRelation strengthened_cycle pi_vars_cleaned

    //Try to refine the termination argument:
    let mutable ret = None
    Stats.incCounter "T2 - Counterexample investigation without path invariant"
    ret <- refine_cycle pars p cp strengthened_cycle strengthened_cycle_rel lex_info

    // If we didn't find a rank function yet, try strengthening the cycle with a path invariant...
    if ret = None then
        Stats.incCounter "T2 - Counterexample investigation without path invariant failed"
        log pars "Trying to find a path invariant..."

        let invariant = path_invariant stem strengthened_cycle
        if Formula.unsat invariant then
            Utils.dieWith "UNSAT path invariant (this is probably due to the incompleteness of the interpolation procedure on integers)"

        log pars <| sprintf "Using path invariant %A" invariant

        let strengthened_cycle = (-1, [Programs.assume invariant], -1) :: strengthened_cycle
        let strengthened_cycle_rel = Programs.cmdPathToRelation strengthened_cycle pi_vars_cleaned
        ret <- refine_cycle pars p cp strengthened_cycle strengthened_cycle_rel lex_info
        if ret.IsSome then
            Stats.incCounter "T2 - Counterexample investigation with path invariant successful"
        else
            Stats.incCounter "T2 - Counterexample investigation with path invariant failed"
    else
        Stats.incCounter "T2 - Counterexample investigation without path invariant successful"

    match ret with
    | Some(Lex_WF(_, lex_rf_check_formulas)) -> Some(Lex_WF(cp, lex_rf_check_formulas))
    | Some(Poly_WF(poly_checkers)) -> Some(Poly_WF(poly_checkers))
    | None -> Some(CEX (Counterexample.make (Some stem) (Some cycle)))
    | Some(Transition_Removal(trans)) -> Some(Transition_Removal(trans))
    | Some(CEX(_)) -> failwith "unexpected CEX at this point"

///Find the cutpoint where we failed, by walking the path backwards until we reach the the check "__copied_k >= 1". k is then the failing cutpoint
let find_failing_cp pi =
    let extract_copied_cutpoint f =
        match f with
        | Formula.Ge (Term.Var var, Term.Const c) when c = bigint.One && Formula.is_copied_var var -> 
            Some (int (var.Substring(Formula.copied_prefix.Length)))
        | _ -> None

    let is_copy_check cmd =
        match cmd with
        | Programs.Assume (_, f) -> (extract_copied_cutpoint f).IsSome
        | _ -> false

    pi 
    |> List.rev 
    |> List.tryFind (fun (_, cmd, _) -> is_copy_check cmd)
    |> (fun c -> match c with | Some (_, Programs.Assume (_, f), _) -> Some (extract_copied_cutpoint f).Value 
                              | _ -> None)

let investigate_cex (pars : Parameters.parameters) (p:Programs.Program) reachGraph pi found_lex_rfs lex_info =
    let failing_cutpoint = find_failing_cp pi

    match failing_cutpoint with
    | None -> (None, -1)
    | Some failing_cutpoint ->
        if pars.print_debug then
            Log.debug pars <| sprintf "Full counterexample we got:"
            for (k, cmd, k') in pi do
                Log.debug pars <| sprintf "  (%i, %A, %i)" k cmd k'

        let program_refinement =
            match investigate_cex_for_fixed_cp pars p reachGraph pi failing_cutpoint lex_info with
            | None -> None
            | Some(CEX(l)) -> Some(CEX(l))
            | Some(Lex_WF(cp, lex_rf_check_formulas)) ->
                //Check if we already have a RF that implies this one:
                let approx_have_lex_rf_already  =
                    //Don't carry out this check if we're doing init cond detection or unrolling (it's not supported)
                    if (lex_info.cp_init_cond).[cp] || (lex_info.cp_unrolling).[cp] then
                        false
                    else
                        match Map.tryFind cp found_lex_rfs with
                        | Some old_lex_rf_check_formulas ->  
                            let old_lex = make_lex_formula old_lex_rf_check_formulas
                            let new_lex = make_lex_formula lex_rf_check_formulas
                            Formula.entails new_lex old_lex
                        | None -> false
                if not approx_have_lex_rf_already then
                    Some(Lex_WF(cp, lex_rf_check_formulas))
                else
                    None
            | Some(Poly_WF(poly_checkers)) -> Some(Poly_WF(poly_checkers))
            | Some(Transition_Removal(trans)) -> Some(Transition_Removal(trans))
        (program_refinement, failing_cutpoint)
