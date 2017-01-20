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
open SafetyInterface
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
                    let cp_checker_trans = cp_rf.[terminating_cp]
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

let private output_term_proof scc_simplification_rfs found_lex_rfs found_disj_rfs (outWriter : TextWriter) =
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
    let print_one_rf_bnd decreasing_formula bound_formula =
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
        let print_lex_rf (cp, (decr_list, _, bnd_list)) =
            outWriter.WriteLine(" * For cutpoint {0}, used the following rank functions/bounds (in descending priority order):", string cp)
            List.iter2 print_one_rf_bnd decr_list bnd_list
        outWriter.WriteLine("Used the following cutpoint-specific lexicographic rank functions:")
        found_lex_rfs |> Map.toSeq |> Seq.iter print_lex_rf

    if not(Map.isEmpty found_disj_rfs) then
        let print_disj_rf (cp, rf_bnd_list) =
            outWriter.WriteLine(" * For cutpoint {0}, used the following rank functions/bounds:", string cp)
            List.iter (fun (rf_formula, bnd_formula) -> print_one_rf_bnd rf_formula bnd_formula) rf_bnd_list
        outWriter.WriteLine("Used the following cutpoint-specific disjunctive rank functions:")
        found_disj_rfs |> Map.toSeq |> Seq.iter print_disj_rf

let private output_nonterm_proof ((cp, recurrent_set) : int * Formula.formula) (outWriter : TextWriter) =
    outWriter.WriteLine("Found this recurrent set for cutpoint {0:D}: {1}", cp, recurrent_set.pp)

///Produce a mapping from program locations to an (int option), where
///map.[a] = InstrumentationLocation means that a is not to be exported in a certificate (it's an internal location),
///map.[a] = DuplicatedLocation b means that a is a copy of location b, and
///map.[a] = OriginalLocation means that a is a location of the input program
let private getLocToCertLocRepr (progOrig : Program) (progCoopInstrumented : Program) locToLoopDuplLoc =
    let locToCertLocRepr = Dictionary()
    let locsOrig = progOrig.Locations
    let duplLocToOrigLoc = locToLoopDuplLoc |> Map.toSeq |> Seq.map (fun (x, y) -> (y, x)) |> Map.ofSeq
    for (idx, (sourceLoc, _, targetLoc)) in progCoopInstrumented.TransitionsWithIdx |> Seq.sortBy (fun (_, (s, _, _)) -> s) do
        let sourceLocLabel = defaultArg (progCoopInstrumented.GetLocationLabel sourceLoc) ""
        let targetLocLabel = defaultArg (progCoopInstrumented.GetLocationLabel targetLoc) ""
        let isRFCheck =
            let sourceIsRFCheck = sourceLocLabel.StartsWith Instrumentation.PRERF_CHECK_LOC_LABEL 
                                  || sourceLocLabel.StartsWith Instrumentation.POSTRF_CHECK_LOC_LABEL
                                  || sourceLocLabel.StartsWith Instrumentation.FINAL_LOC_LABEL
            let targetIsRFCheck = targetLocLabel.StartsWith Instrumentation.PRERF_CHECK_LOC_LABEL 
                                  || targetLocLabel.StartsWith Instrumentation.POSTRF_CHECK_LOC_LABEL
                                  || targetLocLabel.StartsWith Instrumentation.FINAL_LOC_LABEL
            sourceIsRFCheck || targetIsRFCheck

        let sourceLocOrig = duplLocToOrigLoc.TryFind sourceLoc
        let targetLocOrig = duplLocToOrigLoc.TryFind targetLoc
        if isRFCheck then
            //printfn "Check trans %i: %i (copy of %A)->%i (copy of %A)" idx sourceLoc sourceLocOrig targetLoc targetLocOrig
            locToCertLocRepr.[targetLoc] <- InstrumentationLocation targetLoc
        else
            if locsOrig.Contains sourceLoc then
                locToCertLocRepr.[sourceLoc] <- OriginalLocation sourceLoc
                if locsOrig.Contains targetLoc then
                    //printfn "Orig trans %i: %i->%i" idx sourceLoc targetLoc
                    locToCertLocRepr.[targetLoc] <- OriginalLocation targetLoc
                else
                    //printfn "Switch trans %i: %i->%i (copy of %A)" idx sourceLoc targetLoc targetLocOrig
                    locToCertLocRepr.[targetLoc] <- DuplicatedLocation targetLocOrig.Value
            else
                if locsOrig.Contains targetLoc then
                    //printfn "Strange trans %i: %i (copy of %A)->%i" idx sourceLoc sourceLocOrig targetLoc
                    assert false
                    ()
                else
                    let isCopyTrans = targetLocLabel.StartsWith Instrumentation.AFTER_VARCOPY_LOC_LABEL
                    let isAfterCopyTrans = sourceLocLabel.StartsWith Instrumentation.AFTER_VARCOPY_LOC_LABEL
                    if isCopyTrans then
                        //printfn "Var copy trans %i: %i (copy of %A)->%i (copy of %A)" idx sourceLoc sourceLocOrig targetLoc targetLocOrig
                        locToCertLocRepr.[sourceLoc] <- DuplicatedLocation sourceLocOrig.Value
                        locToCertLocRepr.[targetLoc] <- InstrumentationLocation targetLoc
                    elif isAfterCopyTrans then
                        //printfn "Copied trans after var copy %i: %i (copy of %A)->%i (copy of %A)" idx sourceLoc sourceLocOrig targetLoc targetLocOrig
                        let copiedLoc = int (sourceLocLabel.Substring Instrumentation.AFTER_VARCOPY_LOC_LABEL.Length)
                        locToCertLocRepr.[sourceLoc] <- InstrumentationLocation copiedLoc
                        locToCertLocRepr.[targetLoc] <- DuplicatedLocation targetLocOrig.Value
                    else
                        //printfn "Copied trans %i: %i (copy of %A)->%i (copy of %A)" idx sourceLoc sourceLocOrig targetLoc targetLocOrig
                        locToCertLocRepr.[sourceLoc] <- DuplicatedLocation sourceLocOrig.Value
                        locToCertLocRepr.[targetLoc] <- DuplicatedLocation targetLocOrig.Value
    locToCertLocRepr

let private writeTransitionId (transDuplIdToTransId : Dictionary<int, int>) (xmlWriter : XmlWriter) transId =
    match transDuplIdToTransId.TryGetValue transId with
    | (true, duplicatedTransId) ->
        xmlWriter.WriteElementString ("transitionDuplicate", string duplicatedTransId)
    | _ ->
        xmlWriter.WriteElementString ("transitionId", string transId)

type private ProgramSCC = Set<ProgramLocation>
type private CertificateExportInformation =
    {
        /// Original program, as returned from the parser.
        progOrig : Programs.Program
        /// Program with T2 instrumentation inserted.
        progCoopInstrumented : Programs.Program

        /// SCCs of the cooperation program, restricted to those in the termination copy.
        progCoopSCCs : ProgramSCC list

        /// Maps original program locations to their duplicates created in the instrumentation.
        locToLoopDuplLoc : Map<ProgramLocation, ProgramLocation>
        /// Maps program locations to their representation in certificate (original, duplicate, or instrumented, which gets filtered out)
        locToCertLocRepr : Dictionary<ProgramLocation, CoopProgramLocation>
        /// Maps program locations to the result of abstract interpretation of the program.
        locToAIInvariant : Dictionary<ProgramLocation, IIntAbsDom.IIntAbsDom> option
        /// Maps cutpoints in original program to the transition that connects them to their copy.
        cpToToCpDuplicateTransId : Dictionary<ProgramLocation, TransitionId>

        /// Maps transitions in the termination part of the cooperation graph to their originals.
        transDuplIdToTransId : Dictionary<TransitionId, TransitionId>

        /// Impact graph, containing all invariants required for the proof.
        impactArg : Impact.ImpactARG
        /// Maps program SCCs to a list of (rank function, bound, transitions that could be removed) triples.
        foundInitialLexRankFunctions : Map<ProgramSCC, (Map<ProgramLocation, Map<Var.var, bigint>> * Map<Set<TransitionId>, bigint> * Set<TransitionId>) list>
        /// Maps cutpoints in the termination part of the program to a list of (rank function strict decrease check, rank function weak decrease check, bound check) triples.
        foundLexRankFunctions : Map<ProgramLocation, Formula.formula list * Formula.formula list * Formula.formula list>
    }

let private exportSwitchToCooperationTerminationProof
        (exportInfo : CertificateExportInformation)
        (nextProofStep : XmlWriter -> unit)
        (xmlWriter : XmlWriter) =
    xmlWriter.WriteStartElement "switchToCooperationTermination"

    xmlWriter.WriteStartElement "cutPoints"
    for KeyValue(cp, cpToCoopDupTrans) in exportInfo.cpToToCpDuplicateTransId do
        xmlWriter.WriteStartElement "cutPoint"
        Programs.exportLocation xmlWriter (OriginalLocation cp)
        xmlWriter.WriteElementString ("skipId", string cpToCoopDupTrans)

        let (_, cmds, _) = exportInfo.progCoopInstrumented.GetTransition cpToCoopDupTrans
        let (transFormula, varToMaxSSAIdx) = cmdsToCetaFormula exportInfo.progCoopInstrumented.Variables cmds
        let transLinearTerms =
            Formula.formula.FormulasToLinearTerms (transFormula :> _)
            |> Formula.maybe_filter_instr_vars true
        xmlWriter.WriteStartElement "skipFormula"
        Formula.linear_terms_to_ceta xmlWriter (Var.toCeta varToMaxSSAIdx) transLinearTerms true
        xmlWriter.WriteEndElement () //skipFormula end

        xmlWriter.WriteEndElement () //end cutPoint
    xmlWriter.WriteEndElement () //end cutPoints

    nextProofStep xmlWriter
    xmlWriter.WriteEndElement () //end switchToCooperationTermination

let private exportNonSCCRemovalProof
        (exportInfo : CertificateExportInformation)
        (nextProofStep : XmlWriter -> unit)
        (xmlWriter : XmlWriter) =
    //Invent a "full" cooperation program here, by taking the one we have, and extend it by additional locations/transitions:
    let progFullCoop = exportInfo.progCoopInstrumented.Clone()
    let locToCoopDupl = Dictionary()
    let progFullExtraTrans = HashSet()
    let getCoopLocDupl loc =
        match exportInfo.locToLoopDuplLoc.TryFind loc with
        | Some dup -> dup
        | None ->
            match locToCoopDupl.TryGetValue loc with
            | (true, dup) -> dup
            | (false, _) ->
                let dup = progFullCoop.NewNode()
                locToCoopDupl.[loc] <- dup
                exportInfo.locToCertLocRepr.[dup] <- DuplicatedLocation loc
                // We will need to compute SCCs, and our SCC computation only considers things reachable from init.
                // Thus, add faked transitions from there..
                progFullCoop.AddTransition progFullCoop.Initial [] dup |> ignore
                dup
    for loc in exportInfo.progOrig.Locations do
        for (transIdx, (_, cmds, targetLoc)) in exportInfo.progOrig.TransitionsFrom loc do
            let needToAddCopiedTransition =
                match Map.tryFind loc exportInfo.locToLoopDuplLoc with
                | None -> true
                | Some duplLoc ->
                    //Check if we created a copy, of if this is one of those transitions that leave the SCC:
                    exportInfo.progCoopInstrumented.TransitionsFrom duplLoc
                    |> Seq.exists (fun (copiedTransIdx, _) -> exportInfo.transDuplIdToTransId.ContainsKey copiedTransIdx &&
                                                              exportInfo.transDuplIdToTransId.[copiedTransIdx] = transIdx)
                    |> not
            if needToAddCopiedTransition then
                let coopLocDupl = getCoopLocDupl loc
                let targetLocDupl = getCoopLocDupl targetLoc
                let copiedTransIdx = progFullCoop.AddTransition coopLocDupl cmds targetLocDupl
                exportInfo.transDuplIdToTransId.Add(copiedTransIdx, transIdx)
                progFullExtraTrans.Add copiedTransIdx |> ignore

    //Now remove all the extra invented transitions again, by doing a trivial termination argument encoding
    //simple SCC structure, assigning a constant rank to each location
    xmlWriter.WriteStartElement "transitionRemoval"
    xmlWriter.WriteStartElement "rankingFunctions"
    let progFullCoopSCCs = progFullCoop.GetSCCSGs true
    progFullCoopSCCs
    |> List.iteri
        (fun idx scc ->
            //This is one of the SCC on the non-duplicated side, leave as they are:
            let rank =
                if Set.exists exportInfo.progOrig.Locations.Contains scc then
                    0
                else
                    -idx - 1
            for loc in scc do
                let locRepr = exportInfo.locToCertLocRepr.[loc]
                match locRepr with
                | DuplicatedLocation _ ->
                    xmlWriter.WriteStartElement "rankingFunction"
                    xmlWriter.WriteStartElement "location"
                    Programs.exportLocation xmlWriter locRepr
                    xmlWriter.WriteEndElement () //end location
                    xmlWriter.WriteStartElement "expression"
                    xmlWriter.WriteElementString ("constant", string rank)
                    xmlWriter.WriteEndElement () //end expression
                    xmlWriter.WriteEndElement () //end rankingFunction
                | _ -> ())
    xmlWriter.WriteEndElement () //end rankingFunctions
    xmlWriter.WriteStartElement "bound"
    xmlWriter.WriteElementString ("constant", string (-(List.length progFullCoopSCCs) - 1))
    xmlWriter.WriteEndElement () //end bound

    xmlWriter.WriteStartElement "remove"
    progFullExtraTrans |> Seq.iter (writeTransitionId exportInfo.transDuplIdToTransId xmlWriter)
    xmlWriter.WriteEndElement () //end remove

    // Write out the hints, which are trivially 0 for everything, as all rank functions are
    // just constants. However, getting the numbers of hints right is a bit of a song and dance...
    xmlWriter.WriteStartElement "hints"
    for (transIdx, (source, _, target)) in progFullCoop.TransitionsWithIdx do
        match (exportInfo.locToCertLocRepr.[source], exportInfo.locToCertLocRepr.[target]) with
        | (InstrumentationLocation _, _)
        | (OriginalLocation _, _)
        | (_, InstrumentationLocation _) ->
            ()
        | _ ->
            // We need more trivial hints for those transitions that we want to delete, but all require decreaseHints:
            if progFullExtraTrans.Contains transIdx then
                xmlWriter.WriteStartElement "strictDecrease"
                writeTransitionId exportInfo.transDuplIdToTransId xmlWriter transIdx

                xmlWriter.WriteStartElement "boundHints"
                xmlWriter.WriteStartElement "linearImplicationHint"
                xmlWriter.WriteElementString ("simplex", "")
                xmlWriter.WriteEndElement () //linearImplicationHint end
                xmlWriter.WriteEndElement () //end boundHints
            else
                xmlWriter.WriteStartElement "weakDecrease"
                writeTransitionId exportInfo.transDuplIdToTransId xmlWriter transIdx

            xmlWriter.WriteStartElement "decreaseHints"
            xmlWriter.WriteStartElement "linearImplicationHint"
            xmlWriter.WriteElementString ("simplex", "")
            xmlWriter.WriteEndElement () //linearImplicationHint end
            xmlWriter.WriteEndElement () //end decreaseHints

            xmlWriter.WriteEndElement () //end strictDecrease / weakDecrease
    xmlWriter.WriteEndElement () //end hints

    nextProofStep xmlWriter
    xmlWriter.WriteEndElement () //end transitionRemoval (trivial SCC argument)

/// Export per-node invariants generated by abstract interpretation into proof.
// Note: We re-use the existing definition of Impact-style proofs here, as the
// certifier does not enforce the tree property on the generated ARG. Thus, each
// program location corresponds to exactly one node in the generated ARG, and
// program transitions are "child" edges in the ARG.
let private exportAIInvariantsProof
        (exportInfo : CertificateExportInformation)
        (nextProofStep : XmlWriter -> unit)
        (xmlWriter : XmlWriter) =
    match exportInfo.locToAIInvariant with
    | Some locToAIInvariant ->
        xmlWriter.WriteStartElement "newInvariants"

        (*** Start of declaring new invariants ***)
        xmlWriter.WriteStartElement "invariants"
        for KeyValue(_, locRepr) in exportInfo.locToCertLocRepr do
            match locRepr with
            | DuplicatedLocation origLoc
            | OriginalLocation origLoc ->
                let invariant = locToAIInvariant.[origLoc].to_formula ()
                let invariantLinearTerms = invariant.ToLinearTerms ()
                xmlWriter.WriteStartElement "invariant"

                xmlWriter.WriteStartElement "location"
                Programs.exportLocation xmlWriter locRepr
                xmlWriter.WriteEndElement () //end location

                xmlWriter.WriteStartElement "formula"
                Formula.linear_terms_to_ceta xmlWriter Var.plainToCeta invariantLinearTerms true
                xmlWriter.WriteEndElement () //end formula
                xmlWriter.WriteEndElement () //end invariant
            | _ -> ()
        xmlWriter.WriteEndElement () //end invariants
        (*** End of declaring new invariants ***)

        (*** Start of proving soundness of new invariants ***)
        xmlWriter.WriteStartElement "impact"
        xmlWriter.WriteElementString ("initial", string exportInfo.progCoopInstrumented.Initial)
        xmlWriter.WriteStartElement "nodes"
        for KeyValue(loc, locRepr) in exportInfo.locToCertLocRepr do
            match locRepr with
            | InstrumentationLocation _ ->
                () //Do not export
            | OriginalLocation origLoc
            | DuplicatedLocation origLoc ->
                let invariant = locToAIInvariant.[origLoc].to_formula ()
                let invariantLinearTerms = invariant.ToLinearTerms ()
                xmlWriter.WriteStartElement "node"

                xmlWriter.WriteElementString ("nodeId", string loc)

                xmlWriter.WriteStartElement "invariant"
                Formula.linear_terms_to_ceta xmlWriter Var.plainToCeta invariantLinearTerms true
                xmlWriter.WriteEndElement () // invariant end

                xmlWriter.WriteStartElement "location"
                Programs.exportLocation xmlWriter locRepr
                xmlWriter.WriteEndElement () //end location

                xmlWriter.WriteStartElement "children"
                for (transIdx, (_, cmds, childLoc)) in exportInfo.progCoopInstrumented.TransitionsFrom loc do
                    let certChildLocRepr = exportInfo.locToCertLocRepr.[childLoc]
                    match certChildLocRepr with
                    | InstrumentationLocation _ ->
                        () //Do not export
                    | OriginalLocation origChildLoc
                    | DuplicatedLocation origChildLoc ->
                        let childInvariant = locToAIInvariant.[origChildLoc].to_formula ()
                        let childLocInvariantLinearTerms = childInvariant.ToLinearTerms ()
                        let (transFormula, varToMaxSSAIdx) = Programs.cmdsToCetaFormula exportInfo.progCoopInstrumented.Variables cmds
                        let varToPre var = Var.prime_var var 0
                        let varToPost var =
                            match Map.tryFind var varToMaxSSAIdx with
                            | Some idx -> Var.prime_var var idx
                            | None -> var
                        let transLinearTerms =
                            Formula.formula.FormulasToLinearTerms (transFormula :> _)
                            |> Formula.maybe_filter_instr_vars true
                        let locInvariantAndTransLinearTerms = List.append (List.map (SparseLinear.alpha varToPre) invariantLinearTerms) transLinearTerms
                        xmlWriter.WriteStartElement "child"
                        writeTransitionId exportInfo.transDuplIdToTransId xmlWriter transIdx
                        xmlWriter.WriteElementString ("nodeId", string childLoc)
                        xmlWriter.WriteStartElement "hints"
                        for lt in childLocInvariantLinearTerms do
                            SparseLinear.writeCeTALinearImplicationHints xmlWriter locInvariantAndTransLinearTerms (SparseLinear.alpha varToPost lt)
                        xmlWriter.WriteEndElement () //hints end
                        xmlWriter.WriteEndElement () // child end
                xmlWriter.WriteEndElement () // children end
                xmlWriter.WriteEndElement () // node end
        xmlWriter.WriteEndElement () // nodes end
        xmlWriter.WriteEndElement () // impact end
        (*** End of proving soundness of new invariants ***)

        xmlWriter.WriteStartElement "fixInvariants"
        nextProofStep xmlWriter
        xmlWriter.WriteEndElement () //end fixInvariants
        xmlWriter.WriteEndElement () //end newInvariants
    | None ->
        nextProofStep xmlWriter

let private exportNewImpactInvariantsProof
        (exportInfo : CertificateExportInformation)
        (nextProofStep : XmlWriter -> unit)
        (xmlWriter : XmlWriter) =
    let argIsTrivial = exportInfo.impactArg.IsTrivial true

    if not argIsTrivial then
        xmlWriter.WriteStartElement "newInvariants"
        xmlWriter.WriteStartElement "invariants"
        for KeyValue(loc, locRepr) in exportInfo.locToCertLocRepr do
            match locRepr with
            | DuplicatedLocation _
            | OriginalLocation _ ->
                let locInvariants = exportInfo.impactArg.GetLocationInvariant (Some exportInfo.locToCertLocRepr) loc
                xmlWriter.WriteStartElement "invariant"

                xmlWriter.WriteStartElement "location"
                Programs.exportLocation xmlWriter locRepr
                xmlWriter.WriteEndElement () //end location

                xmlWriter.WriteStartElement "formula"
                xmlWriter.WriteStartElement "disjunction"
                for locInvariant in locInvariants do
                    Formula.linear_terms_to_ceta xmlWriter Var.plainToCeta (Formula.formula.FormulasToLinearTerms (locInvariant :> _)) true
                xmlWriter.WriteEndElement () //end disjunction
                xmlWriter.WriteEndElement () //end formula
                xmlWriter.WriteEndElement () //end invariant
            | _ -> ()

        xmlWriter.WriteEndElement () //end invariants

        exportInfo.impactArg.ToCeta xmlWriter (Some exportInfo.locToCertLocRepr) (Some (writeTransitionId exportInfo.transDuplIdToTransId)) true

    nextProofStep xmlWriter

    if not argIsTrivial then
        xmlWriter.WriteEndElement () //end newInvariants

let private exportSccDecompositionProof
        (exportInfo : CertificateExportInformation)
        (nextProofStep : Set<int> -> XmlWriter -> unit)
        (xmlWriter : XmlWriter) =
    xmlWriter.WriteStartElement "sccDecomposition"
    for scc in exportInfo.progCoopSCCs do
        xmlWriter.WriteStartElement "sccWithProof"
        xmlWriter.WriteStartElement "scc"
        for loc in scc do
            let certLocRepr = exportInfo.locToCertLocRepr.[loc]
            match certLocRepr with
            | DuplicatedLocation _ -> Programs.exportLocation xmlWriter certLocRepr
            | _ -> ()
        xmlWriter.WriteEndElement () //end scc
        nextProofStep scc xmlWriter
        xmlWriter.WriteEndElement () //end sccWithProof
    xmlWriter.WriteEndElement () //end sccDecomposition

let private exportInitialLexRFTransRemovalProof
        (exportInfo : CertificateExportInformation)
        (nextProofStep : Set<int> -> XmlWriter -> unit)
        (scc : Set<int>)
        (xmlWriter : XmlWriter) =
    let thisSCCRankFunctions =
        exportInfo.foundInitialLexRankFunctions
        |> Map.toSeq
        |> Seq.filter (fun (sccLocs, _) -> not <| Set.isEmpty (Set.intersect sccLocs scc))
    for (_, rfs_bounds_and_removed_transitions) in thisSCCRankFunctions do
        for (locToRF, trans_to_bnds, removed_transitions) in rfs_bounds_and_removed_transitions do
            //Compute minimal bound:
            let bound = trans_to_bnds |> Map.toSeq |> Seq.map snd |> Seq.fold min (bigint System.Int32.MaxValue)
            (* //Code to compute bound per location:
            let locToBound = DefaultDictionary(fun _ -> bigint System.Int32.MaxValue)
            for KeyValue(transitions, bnd) in bnds do
                for transIdx in transitions do
                    let (sourceLoc, _, _) = progCoopInstrumented.GetTransition transIdx
                    locToBound.[sourceLoc] <- min bnd locToBound.[sourceLoc]
            *)

            xmlWriter.WriteStartElement "transitionRemoval"

            (** Step 1: Define rank functions and bound. *)
            xmlWriter.WriteStartElement "rankingFunctions"
            let locToRFTerm = Dictionary()
            for KeyValue(loc, locRF) in locToRF do
                let locRepr = exportInfo.locToCertLocRepr.[loc]
                match locRepr with
                | DuplicatedLocation _ ->
                    let rfTerm =
                        locRF
                        |> Map.toSeq
                        |> Seq.map
                            (fun (var, coeff) ->
                                let var = Var.unprime_var var
                                if var.Equals(Formula.const_var bigint.One) then
                                    Term.Const(coeff)
                                else
                                    Term.Mul(Term.Const(coeff), Term.Var(var)))
                        |> Seq.fold Term.add (Term.constant 0)
                    locToRFTerm.[loc] <- rfTerm
                    let rfLinearTerm = SparseLinear.term_to_linear_term rfTerm

                    xmlWriter.WriteStartElement "rankingFunction"
                    xmlWriter.WriteStartElement "location"
                    Programs.exportLocation xmlWriter locRepr
                    xmlWriter.WriteEndElement () //end location

                    xmlWriter.WriteStartElement "expression"
                    SparseLinear.toCeta xmlWriter Var.plainToCeta rfLinearTerm
                    xmlWriter.WriteEndElement () //end expression
                    xmlWriter.WriteEndElement () //end rankingFunction
                | _ -> () //Ignore original program and instrumentation nodes
            xmlWriter.WriteEndElement () //end rankingFunctions
            xmlWriter.WriteStartElement "bound"
            xmlWriter.WriteElementString ("constant", string (bound - bigint.One))
            xmlWriter.WriteEndElement () //end bound

            (** Step 2: Compute decreasing transitions and hints *)
            let mutable strictDecreaseHintInfo = []
            let mutable weakDecreaseHintInfo = []
            for (transIdx, (sourceLoc, cmds, targetLoc)) in exportInfo.progCoopInstrumented.TransitionsWithIdx do
                let sourceLocRepr = exportInfo.locToCertLocRepr.[sourceLoc]
                let targetLocRepr = exportInfo.locToCertLocRepr.[targetLoc]
                match (sourceLocRepr, targetLocRepr) with
                | (DuplicatedLocation origSourceLoc, DuplicatedLocation _) when locToRFTerm.ContainsKey sourceLoc && locToRFTerm.ContainsKey targetLoc ->
                    let sourceRFTerm = locToRFTerm.[sourceLoc]
                    let targetRFTerm = locToRFTerm.[targetLoc]
                    //Get transition encoding
                    let (transFormula, varToMaxSSAIdx) = Programs.cmdsToCetaFormula exportInfo.progCoopInstrumented.Variables cmds
                    let varToPre var = Var.prime_var var 0
                    let varToPost var =
                        match Map.tryFind var varToMaxSSAIdx with
                        | Some idx -> Var.prime_var var idx
                        | None -> var
                    let transLinearTerms =
                        Formula.formula.FormulasToLinearTerms (transFormula :> _)
                        |> Formula.maybe_filter_instr_vars true

                    //Now do the hinting for every disjunct of the invariant:
                    let locInvariant =
                        match exportInfo.locToAIInvariant with
                        | Some locToAIInvariant -> locToAIInvariant.[origSourceLoc].to_formula ()
                        | _ -> Formula.truec
                    let mutable decreaseHintTerms = []
                    let mutable boundHintTerms = []
                    let mutable isStrict = true
                    let locInvariantTerms = locInvariant.ToLinearTerms()
                    let locInvariantAndTransLinearTerms =
                        List.append (List.map (SparseLinear.alpha varToPre) locInvariantTerms)
                                    transLinearTerms
                    let rankFunctionOnPreVars = Term.alpha varToPre sourceRFTerm
                    let rankFunctionOnPostVars = Term.alpha varToPost targetRFTerm
                    let strictDecreaseZ3 = Formula.z3 <| Formula.formula.Gt (rankFunctionOnPreVars, rankFunctionOnPostVars)
                    let boundZ3 = Formula.z3 <| Formula.formula.Ge (rankFunctionOnPreVars, Term.Const bound)
                    let locInvariantAndTransZ3 = SparseLinear.le_linear_terms_to_z3 locInvariantAndTransLinearTerms
                    if Set.contains transIdx removed_transitions && not <| Z.valid (Z.implies locInvariantAndTransZ3 strictDecreaseZ3) then
                        printfn "Could not prove strict decrease for removed transition %i" transIdx
                    if Set.contains transIdx removed_transitions && not <| Z.valid (Z.implies locInvariantAndTransZ3 boundZ3) then
                        printfn "Could not prove boundedness for removed transition %i" transIdx
                    if Z.valid (Z.implies locInvariantAndTransZ3 (Z.conj2 strictDecreaseZ3 boundZ3)) then
                        let strictDecreaseTerms = (Formula.formula.Gt (rankFunctionOnPreVars, rankFunctionOnPostVars)).ToLinearTerms()
                        let boundTerms = (Formula.formula.Ge (rankFunctionOnPreVars, Term.Const bound)).ToLinearTerms()
                        assert (1 = List.length strictDecreaseTerms)
                        assert (1 = List.length boundTerms)
                        decreaseHintTerms <- (locInvariantAndTransLinearTerms, List.head strictDecreaseTerms) :: decreaseHintTerms
                        boundHintTerms <- (locInvariantAndTransLinearTerms, List.head boundTerms) :: boundHintTerms
                    else
                        let weakDecreaseTerms = (Formula.formula.Ge (rankFunctionOnPreVars, rankFunctionOnPostVars)).ToLinearTerms()
                        assert (1 = List.length weakDecreaseTerms)
                        decreaseHintTerms <- (locInvariantAndTransLinearTerms, List.head weakDecreaseTerms)::decreaseHintTerms
                        isStrict <- false

                    if isStrict then
                        strictDecreaseHintInfo <- (transIdx, decreaseHintTerms, boundHintTerms)::strictDecreaseHintInfo
                    else
                        weakDecreaseHintInfo <- (transIdx, decreaseHintTerms)::weakDecreaseHintInfo
                | _ -> ()

            let strictTransitions = strictDecreaseHintInfo |> List.map (fun (transIdx, _, _) -> transIdx) |> Set.ofList
            assert(removed_transitions = strictTransitions)
            xmlWriter.WriteStartElement "remove"
            for (transIdx, _, _) in strictDecreaseHintInfo do
                writeTransitionId exportInfo.transDuplIdToTransId xmlWriter transIdx
            xmlWriter.WriteEndElement () //end remove

            xmlWriter.WriteStartElement "hints"
            for (transIdx, decreaseHintTerms, boundHintTerms) in strictDecreaseHintInfo do
                xmlWriter.WriteStartElement "strictDecrease"
                writeTransitionId exportInfo.transDuplIdToTransId xmlWriter transIdx
                xmlWriter.WriteStartElement "boundHints"
                for (invAndTransLinearTerms, boundTerm) in boundHintTerms do
                    SparseLinear.writeCeTALinearImplicationHints xmlWriter invAndTransLinearTerms boundTerm
                xmlWriter.WriteEndElement () //end boundHints
                xmlWriter.WriteStartElement "decreaseHints"
                for (invAndTransLinearTerms, strictDecreaseTerm) in decreaseHintTerms do
                    SparseLinear.writeCeTALinearImplicationHints xmlWriter invAndTransLinearTerms strictDecreaseTerm
                xmlWriter.WriteEndElement () //end decreaseHints
                xmlWriter.WriteEndElement () //end strictDecrease
            for (transIdx, decreaseHintTerms) in weakDecreaseHintInfo do
                xmlWriter.WriteStartElement "weakDecrease"
                writeTransitionId exportInfo.transDuplIdToTransId xmlWriter transIdx
                xmlWriter.WriteStartElement "decreaseHints"
                for (invAndTransLinearTerms, weakDecreaseTerm) in decreaseHintTerms do
                    SparseLinear.writeCeTALinearImplicationHints xmlWriter invAndTransLinearTerms weakDecreaseTerm
                xmlWriter.WriteEndElement () //end decreaseHints
                xmlWriter.WriteEndElement () //end weakDecrease
            xmlWriter.WriteEndElement () //end hints

    nextProofStep scc xmlWriter

    for (_, rfs) in thisSCCRankFunctions do
        for _ in rfs do
            xmlWriter.WriteEndElement () //end transitionRemoval

let private exportSafetyTransitionRemovalProof
        (exportInfo : CertificateExportInformation)
        (nextProofStep : Set<int> -> XmlWriter -> unit)
        (scc : Set<int>)
        (xmlWriter : XmlWriter) =
    let thisSccLexRankFunctions = exportInfo.foundLexRankFunctions |> Map.filter (fun cp _ -> Set.contains cp scc)

    if Map.isEmpty thisSccLexRankFunctions then
        nextProofStep scc xmlWriter
    else
        let rfTermAndBounds =
            thisSccLexRankFunctions.Items
            |> Seq.collect
                (fun (_, (decreasingCheckFormulas, _, boundCheckFormulas)) ->
                    //This is rather brittle, as it depends on the formulas we generate in rankfunction.fs for this case...
                    let rfExprs =
                        decreasingCheckFormulas
                        |> Seq.map
                            (function
                             | Formula.Lt(rankFunctionOnNewVars, _) -> rankFunctionOnNewVars
                             | _ -> dieWith "Could not retrieve rank function from internal proof structure.")
                    let bounds =
                        boundCheckFormulas
                        |> Seq.map
                            (function
                             | Formula.Ge(_, Term.Const c) -> -1 + int c
                             | _ -> dieWith "Could not retrieve bound for rank function from internal proof structure.")
                    Seq.zip rfExprs bounds)
            |> List.ofSeq

        let mutable removedTransitions = Set.empty
        for (rfTerm, bound) in rfTermAndBounds do
            xmlWriter.WriteStartElement "transitionRemoval"
            xmlWriter.WriteStartElement "rankingFunctions"

            for loc in scc do
                let locRepr = exportInfo.locToCertLocRepr.[loc]
                match locRepr with
                | DuplicatedLocation _ ->
                    xmlWriter.WriteStartElement "rankingFunction"

                    xmlWriter.WriteStartElement "location"
                    Programs.exportLocation xmlWriter locRepr
                    xmlWriter.WriteEndElement () //end location

                    xmlWriter.WriteStartElement "expression"
                    SparseLinear.toCeta xmlWriter Var.plainToCeta (SparseLinear.term_to_linear_term rfTerm)
                    xmlWriter.WriteEndElement () //end expression

                    xmlWriter.WriteEndElement () //end rankingFunction
                | OriginalLocation _ -> failwith "Have termination argument for an original program location!"
                | _ -> ()

            xmlWriter.WriteEndElement () //end rankingFunctions
            xmlWriter.WriteStartElement "bound"
            xmlWriter.WriteElementString ("constant", string bound)
            xmlWriter.WriteEndElement () //end bound

            let mutable strictDecreaseHintInfo = []
            let mutable weakDecreaseHintInfo = []
            let sccTransitions =
                exportInfo.progCoopInstrumented.TransitionsWithIdx
                |> Seq.filter (fun (_, (source, _, target)) -> Set.contains source scc && Set.contains target scc)
                |> Seq.filter (fun (transIdx, _) -> not <| Set.contains transIdx removedTransitions)
            for (transIdx, (source, cmds, target)) in sccTransitions do
                let sourceRepr = exportInfo.locToCertLocRepr.[source]
                let targetRepr = exportInfo.locToCertLocRepr.[target]
                match (sourceRepr, targetRepr) with
                | (InstrumentationLocation _, _)
                | (OriginalLocation _, _)
                | (_, InstrumentationLocation _) ->
                    ()
                | _ ->
                    printfn "Looking at transition removal step for %i (%i #)" transIdx exportInfo.transDuplIdToTransId.[transIdx]
                    //Get transition encoding
                    let (transFormula, varToMaxSSAIdx) = Programs.cmdsToCetaFormula exportInfo.progCoopInstrumented.Variables cmds
                    let varToPre var = Var.prime_var var 0
                    let varToPost var =
                        match Map.tryFind var varToMaxSSAIdx with
                        | Some idx -> Var.prime_var var idx
                        | None -> var
                    let transLinearTerms =
                        Formula.formula.FormulasToLinearTerms (transFormula :> _)
                        |> Formula.maybe_filter_instr_vars true

                    //Now do the hinting for every disjunct of the invariant:
                    let locInvariants =
                        if exportInfo.impactArg.IsTrivial true then
                            [[Formula.truec]]
                        else
                            exportInfo.impactArg.GetLocationInvariant (Some exportInfo.locToCertLocRepr) source
                    let mutable decreaseHintTerms = []
                    let mutable boundHintTerms = []
                    let mutable isStrict = true
                    let rankFunctionOnPreVars = Term.alpha varToPre rfTerm
                    let rankFunctionOnPostVars = Term.alpha varToPost rfTerm
                    let strictDecreaseZ3 = Formula.z3 <| Formula.formula.Gt (rankFunctionOnPreVars, rankFunctionOnPostVars)
                    let boundZ3 = Formula.z3 <| Formula.formula.Ge (rankFunctionOnPreVars, Term.constant bound)
                    for locInvariant in locInvariants do
                        let locInvariantTerms =
                            Formula.formula.FormulasToLinearTerms (locInvariant :> _)
                            |> Formula.maybe_filter_instr_vars true
                        let locInvariantAndTransLinearTerms =
                            List.append (List.map (SparseLinear.alpha varToPre) locInvariantTerms)
                                        transLinearTerms
                        let locInvariantAndTransZ3 = SparseLinear.le_linear_terms_to_z3 locInvariantAndTransLinearTerms
                        if Z.valid (Z.implies locInvariantAndTransZ3 (Z.conj2 strictDecreaseZ3 boundZ3)) then
                            let strictDecreaseTerms = (Formula.formula.Gt (rankFunctionOnPreVars, rankFunctionOnPostVars)).ToLinearTerms()
                            let boundTerms = (Formula.formula.Ge (rankFunctionOnPreVars, Term.constant bound)).ToLinearTerms()
                            assert (1 = List.length strictDecreaseTerms)
                            assert (1 = List.length boundTerms)
                            decreaseHintTerms <- (locInvariantAndTransLinearTerms, List.head strictDecreaseTerms) :: decreaseHintTerms
                            boundHintTerms <- (locInvariantAndTransLinearTerms, List.head boundTerms) :: boundHintTerms
                        else
                            let weakDecreaseTerms = (Formula.formula.Ge (rankFunctionOnPreVars, rankFunctionOnPostVars)).ToLinearTerms()
                            assert (1 = List.length weakDecreaseTerms)
                            decreaseHintTerms <- (locInvariantAndTransLinearTerms, List.head weakDecreaseTerms)::decreaseHintTerms
                            isStrict <- false

                    if isStrict then
                        printfn " Removing transition %i (%i #)" transIdx exportInfo.transDuplIdToTransId.[transIdx]
                        removedTransitions <- Set.add transIdx removedTransitions
                        strictDecreaseHintInfo <- (transIdx, decreaseHintTerms, boundHintTerms)::strictDecreaseHintInfo
                    else
                        weakDecreaseHintInfo <- (transIdx, decreaseHintTerms)::weakDecreaseHintInfo

            xmlWriter.WriteStartElement "remove"
            for (transIdx, _, _) in strictDecreaseHintInfo do
                writeTransitionId exportInfo.transDuplIdToTransId xmlWriter transIdx
            xmlWriter.WriteEndElement () //end remove

            xmlWriter.WriteStartElement "hints"
            for (transIdx, decreaseHintTerms, boundHintTerms) in strictDecreaseHintInfo do
                xmlWriter.WriteStartElement "strictDecrease"
                writeTransitionId exportInfo.transDuplIdToTransId xmlWriter transIdx
                xmlWriter.WriteStartElement "boundHints"
                for (invAndTransLinearTerms, boundTerm) in boundHintTerms do
                    SparseLinear.writeCeTALinearImplicationHints xmlWriter invAndTransLinearTerms boundTerm
                xmlWriter.WriteEndElement () //end boundHints
                xmlWriter.WriteStartElement "decreaseHints"
                for (invAndTransLinearTerms, strictDecreaseTerm) in decreaseHintTerms do
                    SparseLinear.writeCeTALinearImplicationHints xmlWriter invAndTransLinearTerms strictDecreaseTerm
                xmlWriter.WriteEndElement () //end decreaseHints
                xmlWriter.WriteEndElement () //end strictDecrease
            for (transIdx, decreaseHintTerms) in weakDecreaseHintInfo do
                xmlWriter.WriteStartElement "weakDecrease"
                writeTransitionId exportInfo.transDuplIdToTransId xmlWriter transIdx
                xmlWriter.WriteStartElement "decreaseHints"
                for (invAndTransLinearTerms, weakDecreaseTerm) in decreaseHintTerms do
                    SparseLinear.writeCeTALinearImplicationHints xmlWriter invAndTransLinearTerms weakDecreaseTerm
                xmlWriter.WriteEndElement () //end decreaseHints
                xmlWriter.WriteEndElement () //end weakDecrease
            xmlWriter.WriteEndElement () //end hints

        nextProofStep scc xmlWriter

        for _ in rfTermAndBounds do
            xmlWriter.WriteEndElement () //end transitionRemoval

let private exportTrivialProof _ (xmlWriter : XmlWriter) =
    xmlWriter.WriteElementString ("trivial", "")

let private exportTerminationProofToCeta
        (progOrig : Programs.Program)
        (progCoopInstrumented : Programs.Program)
        locToLoopDuplLoc
        (cpToToCpDuplicateTransId : Dictionary<int, int>)
        (transDuplIdToTransId : Dictionary<int, int>)
        (locToAIInvariant : Dictionary<int, IIntAbsDom.IIntAbsDom> option)
        (progCoopSCCs : Set<int> list)
        (foundInitialLexRankFunctions : Map<Set<int>, (Map<int, Map<Var.var, bigint>> * Map<Set<int>, bigint> * Set<int>) list>)
        (impactArg : Impact.ImpactARG)
        foundLexRankFunctions
        (xmlWriter : XmlWriter) =
    let locToCertLocRepr = getLocToCertLocRepr progOrig progCoopInstrumented locToLoopDuplLoc

    let exportInfo =
        {
            progOrig = progOrig
            progCoopInstrumented = progCoopInstrumented
            progCoopSCCs = progCoopSCCs
            locToLoopDuplLoc = locToLoopDuplLoc
            locToCertLocRepr = locToCertLocRepr
            locToAIInvariant = locToAIInvariant
            cpToToCpDuplicateTransId = cpToToCpDuplicateTransId
            transDuplIdToTransId = transDuplIdToTransId
            impactArg = impactArg
            foundInitialLexRankFunctions = foundInitialLexRankFunctions
            foundLexRankFunctions = foundLexRankFunctions
        }

    xmlWriter.WriteStartElement "certificate"
    progOrig.ToCeta xmlWriter "inputProgram" None false

    xmlWriter
    |> exportSwitchToCooperationTerminationProof exportInfo (
        exportNonSCCRemovalProof exportInfo (
         exportAIInvariantsProof exportInfo (
          exportNewImpactInvariantsProof exportInfo (
           exportSccDecompositionProof exportInfo (
            exportInitialLexRFTransRemovalProof exportInfo (
             exportSafetyTransitionRemovalProof exportInfo (
              exportTrivialProof)))))))

    xmlWriter.WriteEndElement () //end certificate


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
    let cps = cps_checked_for_term |> Set.ofSeq
    /// The SCCs of the termination part of the cooperation graph:
    let p_instrumented_SCCs =
        p_instrumented.GetSCCSGs false
        |> List.filter (fun scc_locs -> not <| Set.isEmpty (Set.intersect scc_locs cps))
    if pars.lex_term_proof_first then
        //First, try to remove/simplify loops by searching for lexicographic arguments that don't need invariants:
        for scc_locs in p_instrumented_SCCs do
            Log.debug pars <| sprintf "Trying initial term proof for SCC [%s]" (String.concat ", " (Seq.map string scc_locs))
            Stats.startTimer "T2 - Initial lex. termination proof"
            match simplify_scc pars p_instrumented true cp_rf cps_checked_for_term scc_locs with
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
    let (p_orig_loops, _) = p_orig.FindLoops()
    let safety = Safety.GetProver pars p_instrumented final_loc

    ///////////////////////////////////////////////////////////////////////////
    /// Main safety loop, instrumenting in termination arguments when needed //
    ///////////////////////////////////////////////////////////////////////////
    let mutable finished = false
    let mutable terminating = None
    let unhandled_counterexample = ref None
    let mutable cex_found = false
    let found_disj_rfs = ref Map.empty
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
            match Lasso.investigate_cex pars p_instrumented safety pi !found_disj_rfs !found_lex_rfs lex_info with
            | (None, _) ->
                //We hit this case when the counterexample is not due to a cycle (i.e., we
                //investigated the counterexample, but it wasn't a lasso at all, but just a
                //straight-line path to the error loc)
                dieWith "Obtained counterexample to termination without a cycle!"

            /////////// Disjunctive (transition invariant) argument:
            | (Some(Lasso.Disj_WF(cp, rf, bnd)),_) ->
                Instrumentation.instrument_disj_RF pars cp rf bnd found_disj_rfs cp_rf p_instrumented safety

            /////////// Lexicographic termination argument:
            | (Some(Lasso.Lex_WF(cp, decr_list, not_incr_list, bnd_list)),_) ->
                Instrumentation.instrument_lex_RF pars cp decr_list not_incr_list bnd_list found_lex_rfs cp_rf_lex p_instrumented safety lex_info

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
                let attempting_lex = ((lex_info.cp_attempt_lex).[failure_cp])
                if attempting_lex && pars.prove_nonterm then
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
                    if attempting_lex && exist_past_lex then
                        Log.log pars "Trying to backtrack to other order for lexicographic RF."
                        let (decr_list,not_incr_list,bnd_list) = Instrumentation.switch_to_past_lex_RF pars lex_info failure_cp
                        Instrumentation.instrument_lex_RF pars failure_cp decr_list not_incr_list bnd_list found_lex_rfs cp_rf_lex p_instrumented safety lex_info
                    else
                        //If we are trying lexicographic termination arguments, try switching to lexicographic polyranking arguments:
                        let already_polyrank = (lex_info.cp_polyrank).[failure_cp]
                        if pars.polyrank && not(already_polyrank) && attempting_lex then
                            Log.log pars "Switching to polyrank."
                            Instrumentation.switch_to_polyrank pars lex_info failure_cp cp_rf_lex p_instrumented safety
                        else
                            //Try the "unrolling" technique
                            if attempting_lex && pars.unrolling && Instrumentation.can_unroll pars lex_info failure_cp then
                                Log.log pars "Trying the unrolling technique."
                                Instrumentation.do_unrolling pars lex_info failure_cp cp_rf_lex p_instrumented safety true
                            else
                                //Try the "detect initial condition" technique
                                let already_doing_init_cond = ((lex_info.cp_init_cond).[failure_cp])
                                if pars.init_cond && attempting_lex && not(already_doing_init_cond) && not(pars.polyrank) then
                                    Log.log pars "Trying initial condition detection."
                                    Instrumentation.do_init_cond pars lex_info failure_cp p_instrumented cp_rf_lex safety

                                // That's it, no tricks left. Return the counterexample and give up
                                else
                                    Log.log pars "Giving up."
                                    noteUnhandledCex cex
                                    cex_found <- true

                                    //If we are doing lexicographic proving, we already tried nonterm further up:
                                    if not(attempting_lex) && (terminating).IsNone && pars.prove_nonterm && ((!unhandled_counterexample).IsSome) then
                                        match RecurrentSets.synthesize pars cex.stem.Value cex.cycle.Value true with
                                        | Some set ->
                                            terminating <- Some false
                                            recurrent_set <- Some (failure_cp, set)
                                        | None   -> ()

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
            exportTerminationProofToCeta p_orig p_instrumented_orig locToLoopDuplLoc cpToToCpDuplicateTransId transDuplIdToTransId locToAIInvariant p_instrumented_SCCs !initial_lex_term_proof_RFs impactArg !found_lex_rfs xmlWriter
        | _ -> ()

    match terminating with
    | Some true ->
        Some (true, output_term_proof !initial_lex_term_proof_RFs !found_lex_rfs !found_disj_rfs)
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