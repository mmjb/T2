/////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      termination.fs
//
//  Abstract:
//
//      Refinement-based termination prover
//
//  Notes:
//
//      *  This largely follows the Terminator approach, with a few twists
//         and turns motivated by our use of lazy abstraction with interpolation.
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


module Microsoft.Research.T2.Termination
open Utils
open Programs

open System.IO
open System.Xml
type Dictionary<'Key, 'Value> = System.Collections.Generic.Dictionary<'Key, 'Value>
type HashSet<'Key> = System.Collections.Generic.HashSet<'Key>

/// Tries to remove as many transitions as possible from a SCC. Returns a list of used rank functions/bounds.
let private simplify_scc (pars : Parameters.parameters) p termination_only (cp_rf: Dictionary<int, int>) (all_cutpoints: Set<int>) scc_nodes =
    let (scc_vars, scc_trans, scc_rels) = Symex.get_scc_rels_for_lex_rf_synth_from_program pars p scc_nodes None
    let mutable cleaned_scc_rels = scc_rels

    if pars.print_debug then
        Log.debug pars <| sprintf "SCC nodes %A, vars %A" scc_nodes scc_vars
        Log.debug pars <| sprintf "SCC transitions: "
        Log.debug pars <| (scc_trans |> Seq.map (fun t -> sprintf "  %A" t) |> String.concat "\n")

    Rankfunction.synth_maximal_lex_rf pars scc_rels (Rankfunction.get_simplified_linterm_cache scc_rels)
    |> List.map
        (fun (rf, bounds, trans_to_remove) ->
            let trans_to_remove_flattened = Seq.concat trans_to_remove |> Set.ofSeq
            for trans_idx in trans_to_remove_flattened do
                if pars.print_debug then
                    let (k, _, k') = p.GetTransition trans_idx
                    Log.debug pars <| sprintf "Removing trans %i->%i" k k'
                let scc_trans_idxs = Set.unionMany (scc_trans |> Set.map fst)
                if (termination_only || (Set.isEmpty (Set.difference scc_trans_idxs trans_to_remove_flattened))) then
                    p.RemoveTransition trans_idx
                    cleaned_scc_rels <- Set.filter (fun (i, _, _, _) -> not <| Set.contains i trans_to_remove) cleaned_scc_rels
            if cleaned_scc_rels.IsEmpty then
                for terminating_cp in (Seq.filter (fun c -> Set.contains c scc_nodes) all_cutpoints) do
                    let cp_checker_trans = cp_rf.[locToOriginalLocation p terminating_cp]
                    p.RemoveTransition cp_checker_trans
            (rf, bounds, trans_to_remove_flattened))

let private generate_invariants_with_AI (pars : Parameters.parameters) (prog : Program) =
    let locToInvariant =
        Analysis.program_absint
            prog.Initial
            (match pars.ai_domain with | Parameters.Box -> IntervalIntDom.Intervals.create() :> IIntAbsDom.IIntAbsDom 
                                       | Parameters.Octagon -> Octagon2.Oct.create :> IIntAbsDom.IIntAbsDom)
            prog.Transitions
            id
    for (n, (k, c, k')) in prog.TransitionsWithIdx do
        let locInvariant = 
            match locToInvariant.TryGetValue k with
            | (true, inv) -> 
                let used_vars = freevars c
                inv.to_formula_filtered used_vars.Contains
            | (false, _) -> Formula.truec
        prog.SetTransition n (k, (assume locInvariant)::c, k')
    locToInvariant

let private output_term_proof scc_simplification_rfs found_lex_rfs (outWriter : TextWriter) =
    //Print out initial rank functions that we used to remove transitions before safety proofs:
    if not(Map.isEmpty scc_simplification_rfs) then
        let print_one_simplification _ rf_bounds_and_removed_transitions =
            let print_one_scc_rf (rf, bnds, removed_transitions) =
                let print_rf_per_loc (loc, loc_rf) =
                    loc_rf
                    |> Map.toSeq
                    |> Seq.map 
                        (fun (var, coeff) -> 
                            let var = Var.unprime_var var
                            if var.Equals(Formula.const_var bigint.One) then 
                                Term.Const(coeff) 
                            else 
                                Term.Mul(Term.Const(coeff), Term.Var(var)))
                    |> Seq.fold Term.add (Term.constant 0)
                    |> (fun rf_term -> outWriter.WriteLine("      RF for loc. {0:D}: {1}", loc, rf_term.pp))
                let print_bound_per_transs (transs, bnd) =
                    outWriter.WriteLine("      Bound for (chained) transitions {0}: {1:D}", (transs |> Seq.map string |> String.concat ", "), bnd)

                outWriter.WriteLine(" * Removed transitions {0} using the following rank function:", (removed_transitions |> Seq.map string |> String.concat ", "))
                rf |> Map.toSeq |> Seq.iter print_rf_per_loc
                bnds |> Map.toSeq |> Seq.iter print_bound_per_transs
            List.iter print_one_scc_rf rf_bounds_and_removed_transitions
        outWriter.WriteLine("Initially, performed program simplifications using lexicographic rank functions:")
        Map.iter print_one_simplification scc_simplification_rfs


    //This is rather brittle, as it depends on the formulas we generate in rankfunction.fs for this case...    
    let print_one_rf_bnd (decreasing_formula, bound_formula) =
        let rf = 
            match decreasing_formula with
            | Formula.Lt(rf_on_new_vars, _) -> rf_on_new_vars
            | _ -> dieWith "Could not retrieve rank function from internal proof structure."
        let bound =
            match bound_formula with
            | Formula.Ge(_, bnd) -> bnd
            | _ -> dieWith "Could not retrieve bound for rank function from internal proof structure."
        outWriter.WriteLine("    - RF {0}, bound {1}", rf.pp, bound.pp)

    if not(Map.isEmpty found_lex_rfs) then
        let print_lex_rf (cp, lex_rf_check_formulas) =
            outWriter.WriteLine(" * For cutpoint {0}, used the following rank functions/bounds (in descending priority order):", string cp)
            Seq.iter print_one_rf_bnd (Seq.map (fun (decr, _, bnd) -> (decr, bnd)) lex_rf_check_formulas)
        outWriter.WriteLine("Used the following cutpoint-specific lexicographic rank functions:")
        found_lex_rfs |> Map.toSeq |> Seq.iter print_lex_rf

let private output_nonterm_proof ((cp, recurrent_set) : int * Formula.formula) (outWriter : TextWriter) =
    outWriter.WriteLine("Found this recurrent set for cutpoint {0:D}: {1}", cp, recurrent_set.pp)

let private prover (pars : Parameters.parameters) (p_orig:Program) =
    Utils.timeout pars.timeout
    p_orig.RemoveUnreachableLocations()
    if pars.dottify_input_pgms then
        Output.print_dot_program p_orig "input.dot"

    //Maybe let's do some AI first:
    let locToAIInvariant =
        if pars.do_ai_threshold > p_orig.TransitionNumber then
            Log.log pars <| sprintf "Performing Abstract Interpretation with domain %A ... " pars.ai_domain
            pars.did_ai_first <- true
            let invariants = generate_invariants_with_AI pars p_orig
            Log.log pars <| sprintf "done."
            Some invariants
        else
            pars.did_ai_first <- false
            None

    ///bottomUp: propertyMap represents a map from subformulas to a set of locations/pre-conditions pairs.
    let (p_instrumented, final_loc, cp_rf, locToLoopDuplLoc, transDuplIdToTransId, cpToToCpDuplicateTransId) =
        Instrumentation.termination_instrumentation pars p_orig
    if pars.dottify_input_pgms then
        Output.print_dot_program p_instrumented ("input__instrumented.dot")
    let p_instrumented_orig = p_instrumented.Clone()

    (*** Start chaining ***)
    if pars.chaining then
        let transMap = 
            p_instrumented.ChainTransitions
                (Seq.append cp_rf.Keys (Seq.collect (function (l1,l2) -> [l1;l2]) locToLoopDuplLoc.Items))
                true
        //Rewrite cp_rf to new transition names:
        let cp_rf_serialized = cp_rf |> List.ofSeq
        for KeyValue (cp, checkerTrans) in cp_rf_serialized do
            let mappedCheckerTrans = transMap.[checkerTrans]
            cp_rf.[cp] <- mappedCheckerTrans

        if pars.print_log then
            for KeyValue(loc, duploc) in locToLoopDuplLoc do
                if not (Set.contains loc p_instrumented.Locations) then
                    Log.log pars <| sprintf "Removed duplicated location %i" loc
                if not (Set.contains duploc p_instrumented.Locations) then
                    Log.log pars <| sprintf "Removed location duplicate %i" duploc
    (*** End chaining ***)
    
    (*** Start initial transitional removal proof ***)
    let initial_lex_term_proof_RFs : Map<Set<int>, (Map<int, Map<Var.var, bigint>> * Map<Set<int>, bigint> * Set<int>) list> ref = ref Map.empty
    let cps_checked_for_term = Set.ofSeq cp_rf.Keys
    let dupl_cp_checked_for_term = cps_checked_for_term |> Set.map (fun cp -> Map.find cp locToLoopDuplLoc)
    /// The SCCs of the termination part of the cooperation graph:
    let p_instrumented_SCCs =
        p_instrumented.GetSCCSGs false
        |> List.filter (fun scc_locs -> not <| Set.isEmpty (Set.intersect scc_locs dupl_cp_checked_for_term))
    if pars.lex_term_proof_first then
        //First, try to remove/simplify loops by searching for lexicographic arguments that don't need invariants:
        for scc_locs in p_instrumented_SCCs do
            Log.debug pars <| sprintf "Trying initial term proof for SCC [%s]" (String.concat ", " (Seq.map string scc_locs))
            Stats.startTimer "T2 - Initial lex. termination proof"
            match simplify_scc pars p_instrumented true cp_rf dupl_cp_checked_for_term scc_locs with
            | [] -> ()
            | rfs_bounds_and_removed_transIdxs ->
                let removed_transitions = Set.unionMany (List.map (fun (_, _, removed) -> removed) rfs_bounds_and_removed_transIdxs)
                initial_lex_term_proof_RFs := Map.add scc_locs rfs_bounds_and_removed_transIdxs !initial_lex_term_proof_RFs
                if pars.print_log then
                    Log.log pars <| sprintf "Initial lex proof removed transitions %A" removed_transitions
            Stats.endTimer "T2 - Initial lex. termination proof"

        if pars.dottify_input_pgms then
            Output.print_dot_program p_instrumented "input__instrumented_after_init_LexRF.dot"
    (*** End initial transitional removal proof ***)

    ///holds, for each cutpoint, a list of (the index of) the transitions that are lexicographic checkers
    let cp_rf_lex = new Dictionary<int, int list>()
    for entry in cp_rf do
        cp_rf_lex.Add(entry.Key, [entry.Value])

    let lex_info = Instrumentation.init_lex_info pars cps_checked_for_term

    //BottomUp changes the instrumentation, so make a copy for that purpose here, as we do not want the pre-conditions to persist in other runs
    let safety = Safety.GetProver pars p_instrumented final_loc

    ///////////////////////////////////////////////////////////////////////////
    /// Main safety loop, instrumenting in termination arguments when needed //
    ///////////////////////////////////////////////////////////////////////////
    let mutable finished = false
    let mutable terminating = None
    let unhandled_counterexample = ref None
    let mutable cex_found = false
    let found_lex_rfs = ref Map.empty
    let mutable recurrent_set = None
    let mutable cex = Counterexample.make None None
    let outputCexAsDefect cex =
        if pars.print_log then
            Counterexample.print_defect pars [cex] "defect.tt"
            Counterexample.print_program pars [cex] "defect.t2"
    let noteUnhandledCex cex =
        outputCexAsDefect cex
        unhandled_counterexample := Some cex

    while not finished && terminating.IsNone do
        match safety.ErrorLocationReachable() with
        | None ->
            terminating <- Some true
        | Some pi ->
            Stats.startTimer "T2 - Counterexample analysis"
            cex <- (Counterexample.make (Some (List.map (fun (x,y,z) -> (x,[y],z)) pi)) None)
            outputCexAsDefect cex
            //Investigate counterexample. Hopefully returns a solution:
            match Lasso.investigate_cex pars p_instrumented safety pi !found_lex_rfs lex_info with
            | (None, _) ->
                //We hit this case when the counterexample is not due to a cycle (i.e., we
                //investigated the counterexample, but it wasn't a lasso at all, but just a
                //straight-line path to the error loc)
                dieWith "Obtained counterexample to termination without a cycle!"

            /////////// Lexicographic termination argument:
            | (Some(Lasso.Lex_WF(cp, lex_rf_check_formulas)),_) ->
                Instrumentation.instrument_lex_RF pars cp lex_rf_check_formulas found_lex_rfs cp_rf_lex p_instrumented safety lex_info

            /////////// Lexicographic polyranking termination argument:
            | (Some(Lasso.Poly_WF(poly_checkers)),cp) ->
                Instrumentation.instrument_poly_RF pars cp poly_checkers cp_rf_lex p_instrumented safety

            /////////// Program simplification:
            | (Some(Lasso.Transition_Removal(trans_to_remove)), _) ->
                //Remove the transitions from the program, remove them from the reachability graph:
                for trans_idx in trans_to_remove do
                    let (k,cmds,k') = p_instrumented.GetTransition trans_idx
                    p_instrumented.RemoveTransition trans_idx
                    safety.DeleteProgramTransition (trans_idx, (k, cmds, k'))
                    safety.ResetFrom k

            /////////// Counterexample for which we couldn't find a program refinement:
            | (Some(Lasso.CEX(cex)), failure_cp) ->
                Log.log pars <| sprintf "Could not find termination argument for counterexample on cutpoint %i" failure_cp
                //If we're doing lexicographic method, try finding a recurrent set at this point (before trying anything else)
                if pars.prove_nonterm then
                    match RecurrentSets.synthesize pars cex.stem.Value cex.cycle.Value true with
                    | Some set ->
                        terminating <- Some false
                        recurrent_set <- Some (failure_cp, set)
                    | None   -> ()

                //if we found a recurrent set, exit
                if (terminating).IsSome then
                    noteUnhandledCex cex
                else
                    //We might haven chosen the wrong order of lexicographic RFs. Try backtracking to another option:
                    let exist_past_lex = (Lasso.exist_past_lex_options failure_cp lex_info)
                    if exist_past_lex then
                        Log.log pars "Trying to backtrack to other order for lexicographic RF."
                        let lex_rf_check_formulas = Instrumentation.switch_to_past_lex_RF pars lex_info failure_cp
                        Instrumentation.instrument_lex_RF pars failure_cp lex_rf_check_formulas found_lex_rfs cp_rf_lex p_instrumented safety lex_info
                    else
                        //If we are trying lexicographic termination arguments, try switching to lexicographic polyranking arguments:
                        let already_polyrank = (lex_info.cp_polyrank).[failure_cp]
                        if pars.polyrank && not(already_polyrank) then
                            Log.log pars "Switching to polyrank."
                            Instrumentation.switch_to_polyrank pars lex_info failure_cp cp_rf_lex p_instrumented safety
                        else
                            //Try the "unrolling" technique
                            if pars.unrolling && Instrumentation.can_unroll pars lex_info failure_cp then
                                Log.log pars "Trying the unrolling technique."
                                Instrumentation.do_unrolling pars lex_info failure_cp cp_rf_lex p_instrumented safety true
                            else
                                //Try the "detect initial condition" technique
                                let already_doing_init_cond = ((lex_info.cp_init_cond).[failure_cp])
                                if pars.init_cond && not(already_doing_init_cond) && not(pars.polyrank) then
                                    Log.log pars "Trying initial condition detection."
                                    Instrumentation.do_init_cond pars lex_info failure_cp p_instrumented cp_rf_lex safety

                                // That's it, no tricks left. Return the counterexample and give up
                                else
                                    Log.log pars "Giving up."
                                    noteUnhandledCex cex
                                    cex_found <- true

                                    finished <- true

                if (recurrent_set).IsSome then
                    cex_found <- true

            Stats.endTimer "T2 - Counterexample analysis"
        Utils.run_clear()
    done

    Utils.reset_timeout()

    match pars.export_cert with
    | None -> ()
    | Some cert_file ->
        match terminating with
        | Some true -> 
            let impactArg = safety :?> Impact.ImpactARG
            use streamWriter = new StreamWriter (cert_file)
            use xmlWriter = new XmlTextWriter (streamWriter)
            xmlWriter.Formatting <- Formatting.Indented
            Certification.exportProofCertificate pars p_orig p_instrumented_orig cpToToCpDuplicateTransId transDuplIdToTransId locToAIInvariant p_instrumented_SCCs !initial_lex_term_proof_RFs impactArg !found_lex_rfs xmlWriter
        | _ -> ()

    match terminating with
    | Some true ->
        Some (true, output_term_proof !initial_lex_term_proof_RFs !found_lex_rfs)
    | Some false ->
        if not(p_instrumented.IncompleteAbstraction) then
            assert (!unhandled_counterexample <> None)
            Some (false, output_nonterm_proof (recurrent_set).Value)
        else
            None
    | None ->
        None

let bottomUpProver (pars : Parameters.parameters) (p:Program) =
    Z.refreshZ3Context()
    Utils.timeout pars.timeout

    if pars.elim_temp_vars then
        p.ConstantAssignmentPropagation Set.empty
        p.LetConvert (Analysis.liveness p Set.empty)

    let result = 
        try
            prover pars p
        with
        | :? System.ArgumentException as ex -> 
            printfn "Exception! %s " (ex.Message)
            None

    Utils.reset_timeout()
    result