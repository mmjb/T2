/////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      Certification.fs
//
//  Abstract:
//
//      Utilities for exporting a certificate for computed proof of termination.
//
//  Notes:
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


module Microsoft.Research.T2.Certification
open Utils
open Programs

open System.Xml
type Dictionary<'Key, 'Value> = System.Collections.Generic.Dictionary<'Key, 'Value>
type HashSet<'Key> = System.Collections.Generic.HashSet<'Key>

let private getTransitionId (transDuplIdToTransId : Dictionary<int, (int * bool)>) transId =
    match transDuplIdToTransId.TryGetValue transId with
    | (true, (duplicatedTransId, wasOriginal)) ->
        if wasOriginal then
            ("transitionDuplicate", string duplicatedTransId)
        else
            ("transitionId", string duplicatedTransId)
    | _ ->
        ("transitionId", string transId)

let private writeTransitionId (transDuplIdToTransId : Dictionary<int, (int * bool)>) (xmlWriter : XmlWriter) transId =
    let (transType, transName) = (getTransitionId transDuplIdToTransId transId)
    xmlWriter.WriteElementString (transType, transName)

type private ProgramSCC = Set<ProgramLocation>
type private CertificateExportInformation =
    {
        /// Parameters for termination proof.
        parameters : Parameters.parameters

        /// Original program, as returned from the parser.
        progOrig : Programs.Program
        /// Program with T2 instrumentation inserted.
        progCoopInstrumented : Programs.Program

        /// SCCs of the cooperation program, restricted to those in the termination copy.
        progCoopSCCs : ProgramSCC list

        /// Maps program locations to the result of abstract interpretation of the program.
        locToAIInvariant : Dictionary<ProgramLocation, IIntAbsDom.IIntAbsDom> option
        /// Maps cutpoints in original program to the transition that connects them to their copy.
        cpToToCpDuplicateTransId : Dictionary<ProgramLocation, TransitionId>

        /// Maps transitions in the termination part of the cooperation graph to their originals.
        transDuplIdToTransId : Dictionary<TransitionId, TransitionId * bool>

        /// Impact graph, containing all invariants required for the proof.
        impactArg : Impact.ImpactARG
        /// Maps program SCCs to a list of (rank function, bound, transitions that could be removed) triples.
        foundInitialLexRankFunctions : Map<ProgramSCC, (Map<ProgramLocation, Map<Var.var, bigint>> * Map<Set<TransitionId>, bigint> * Set<TransitionId>) list>
        /// Maps cutpoints in the termination part of the program to a list of (rank function strict decrease check, rank function weak decrease check, bound check) triples.
        foundLexRankFunctions : Map<ProgramLocation, (Formula.formula * Formula.formula * Formula.formula) list>
    }

let private getCoopLocDupl exportInfo loc =
    match exportInfo.progCoopInstrumented.GetLocationLabel loc with
    | OriginalLocation origLoc ->
        if exportInfo.progCoopInstrumented.HasLabelledLocation (DuplicatedCutpointLocation origLoc) then
            exportInfo.progCoopInstrumented.GetLabelledLocation (DuplicatedCutpointLocation origLoc)
        else
            exportInfo.progCoopInstrumented.GetLabelledLocation (DuplicatedLocation origLoc)
    | label -> failwithf "Trying to find cooperation graph duplicate of non-original location %i (%A)" loc label

let private shouldExportLocation (prog : Programs.Program) scc exportOriginalLocation loc =
    match prog.GetLocationLabel loc with
    | OriginalLocation _ -> exportOriginalLocation
    | CutpointRFCheckLocation _ -> false
    | _ -> Set.contains loc scc

let private shouldExportTransition (prog : Programs.Program) shouldExportLocation (cpToFocusOn : int option) (removedTransitions : Set<TransitionId>) transitionId source target =
    if Set.contains transitionId removedTransitions || not (shouldExportLocation source && shouldExportLocation target) then
        false
    else
        match cpToFocusOn with
        | None ->
            match (prog.GetLocationLabel source, prog.GetLocationLabel target) with
            // Ignore transition from cutpoint copy that don't copy variables:
            | (DuplicatedCutpointLocation _, CutpointVarSnapshotLocation _) ->
                let (_, cmds, _) = prog.GetTransition transitionId
                let makesAnySnapshot =
                    cmds
                    |> List.exists
                        (function | Assume _ -> false
                                  | Assign (_, v, _) -> Formula.is_copied_var v)
                makesAnySnapshot
            | _ -> true
        | Some cpToFocusOn ->
            let cpLabel = Programs.getBaseLabel (prog.GetLocationLabel cpToFocusOn)
            match (prog.GetLocationLabel source, prog.GetLocationLabel target) with
            // Use the non-copying transition for all cutpoint but the one we are focusing one:
            | (DuplicatedCutpointLocation label, CutpointVarSnapshotLocation _) ->
                let (_, cmds, _) = prog.GetTransition transitionId
                let makesAnySnapshot =
                    cmds
                    |> List.exists
                        (function | Assume _ -> false
                                  | Assign (_, v, _) -> Formula.is_copied_var v)
                if label = cpLabel then
                    makesAnySnapshot
                else
                    not makesAnySnapshot
            | (DuplicatedCutpointLocation _, DuplicatedCutpointLocation _)
            | (DuplicatedCutpointLocation _, CutpointDummyEntryLocation _) -> false
            // Only export the "skip" to the duplicated cutpoint we are focusing on:
            | (OriginalLocation _, DuplicatedCutpointLocation _) when source <> cpToFocusOn -> false
            | _ -> true

let private shouldExportVariable cp var =
    if    Formula.is_copied_var var || Formula.is_init_cond_var var
       || Formula.is_iter_var var || Formula.is_subcheck_return var then
        false
    else if Formula.is_snapshot_var var then
        Formula.extract_snapshot_cp var = cp
    else
        true

let private lexRFStrictlyDecreasesInIthPositionTerms sourceRFs targetRFs bounds i =
    [
        let mutable j = 0
        for (sourceRF, targetRF, bound) in Seq.zip3 sourceRFs targetRFs bounds do
            if i = j then
                yield List.head <| (Formula.Gt(sourceRF, targetRF)).ToLinearTerms() // i-th RF actually decreases
            if j <= i then
                yield List.head <| (Formula.Ge(sourceRF, Term.Const bound)).ToLinearTerms() // current and all earlier RFs are bounded from below
            if j < i then
                yield List.head <| (Formula.Ge(sourceRF, targetRF)).ToLinearTerms() // all earlier RFs are not increasing
            j <- j + 1
    ]

let private lexRFWeaklyDecreasesTerms sourceRFs targetRFs =
    [
        for (sourceRF, targetRF) in Seq.zip sourceRFs targetRFs do
            yield List.head <| (Formula.Ge(sourceRF, targetRF)).ToLinearTerms() // RFs are not increasing
    ]

let private getImpactInvariantsForLocs
        (exportInfo: CertificateExportInformation)
        (scc : ProgramSCC)
        (removedTransitions : Set<TransitionId>)
        (cp : ProgramLocation) =
    let shouldExportLocation = shouldExportLocation exportInfo.progCoopInstrumented scc true
    let shouldExportTransition = shouldExportTransition exportInfo.progCoopInstrumented shouldExportLocation (Some cp) removedTransitions
    let shouldExportVariable = shouldExportVariable cp

    let argNodesToReport = exportInfo.impactArg.GetCetaFilteredARGNodes shouldExportLocation shouldExportTransition
    let (snapshotFixupLocsToIgnore, _) = exportInfo.impactArg.GetCutpointSnapshotExportFixup cp argNodesToReport shouldExportVariable
    argNodesToReport.RemoveAll snapshotFixupLocsToIgnore

    let locToInvariants = Dictionary()

    let argIsTrivial = exportInfo.impactArg.IsTrivial argNodesToReport shouldExportVariable
    for loc in exportInfo.progCoopInstrumented.Locations do
        if shouldExportLocation loc then
            let locInvariants =
                if argIsTrivial then
                    [[Formula.formula.True]]
                else
                    exportInfo.impactArg.GetLocationInvariantForNodes argNodesToReport loc
            locToInvariants.[loc] <- locInvariants
    (argIsTrivial, locToInvariants)

let private exportTransitionRemovalProof
        (exportInfo : CertificateExportInformation)
        (locToInvariant: Dictionary<ProgramLocation, Formula.formula list list>)
        (locToRFTerms : Dictionary<ProgramLocation, Term.term list>)
        (bounds : bigint list)
        (transitionsToExport : (TransitionId * Transition) seq)
        (transitionsToRemove : Set<TransitionId> option)
        (shouldExportVariable : Var.var -> bool)
        (removedTransitions : Set<TransitionId>)
        (nextProofStep : Set<TransitionId> -> XmlWriter -> unit)
        (xmlWriter : XmlWriter) =
    (** Step 1: Compute which transitions decrease, and hints *)
    let mutable strictDecreaseHintInfo = []
    let mutable weakDecreaseHintInfo = []

    for (transIdx, (sourceLoc, cmds, targetLoc)) in transitionsToExport do
        let sourceRFTerms = locToRFTerms.[sourceLoc]
        let targetRFTerms = locToRFTerms.[targetLoc]
        //Get transition encoding
        let (transFormula, varToMaxSSAIdx) = Programs.cmdsToCetaFormula exportInfo.progCoopInstrumented.Variables cmds
        let varToPre var = Var.prime_var var 0
        let varToPost var =
            match Map.tryFind var varToMaxSSAIdx with
            | Some idx -> Var.prime_var var idx
            | None -> var
        let transLinearTerms =
            Formula.formula.FormulasToLinearTerms (transFormula :> _)
            |> Formula.filter_instr_vars shouldExportVariable

        let rankFunctionsOnPreVars = List.map (Term.alpha varToPre) sourceRFTerms
        let rankFunctionsOnPostVars = List.map (Term.alpha varToPost) targetRFTerms

        if exportInfo.parameters.print_debug then
            Log.debug exportInfo.parameters
                (sprintf " Looking at trans %i: %i (%A) -> %i (%A)"
                    transIdx
                    sourceLoc (exportInfo.progCoopInstrumented.GetLocationLabel sourceLoc)
                    targetLoc (exportInfo.progCoopInstrumented.GetLocationLabel targetLoc))
            Log.debug exportInfo.parameters (sprintf "   RF on source: (%s)" (String.concat ", " (List.map string sourceRFTerms)))
            Log.debug exportInfo.parameters (sprintf "   Bounds: (%s)" (String.concat ", " (List.map string bounds)))
            Log.debug exportInfo.parameters (sprintf "   RF on target: (%s)" (String.concat ", " (List.map string targetRFTerms)))

        //Now try to find one element of the lexicographic RF that actually decreases (which we need to check on all invariant disjuncts):
        let locInvariants = locToInvariant.GetWithDefault sourceLoc [[Formula.truec]]
        let weakDecreaseTerms = lexRFWeaklyDecreasesTerms rankFunctionsOnPreVars rankFunctionsOnPostVars
        let mutable decreaseHints = []
        let mutable boundHints = []
        let mutable allDisjunctsStrict = true
        for locInvariant in locInvariants do
            Log.debug exportInfo.parameters (sprintf "   Invariant disjunct on source: %s" (String.concat " && " (List.map string locInvariant)))
            let locInvariantTerms =
                Formula.formula.FormulasToLinearTerms (locInvariant :> _)
                |> Formula.filter_instr_vars shouldExportVariable
            let locInvariantAndTransLinearTerms =
                List.append (List.map (SparseLinear.alpha varToPre) locInvariantTerms)
                            transLinearTerms

            let mutable thisDisjunctStrict = false
            if Formula.unsat (Formula.conj locInvariant) then
                Log.debug exportInfo.parameters (sprintf "    Source invariant UNSAT and transition thus trivially marked as strictly decreasing for this disjunct.")
                thisDisjunctStrict <- true
            else
                for i in 0 .. sourceRFTerms.Length - 1 do
                    if not thisDisjunctStrict then
                        Log.debug exportInfo.parameters (sprintf "    Checking %i-th component of rank function." i)
                        let strictDecreaseTerms = lexRFStrictlyDecreasesInIthPositionTerms rankFunctionsOnPreVars rankFunctionsOnPostVars bounds i

                        let mutable allTermsHold = true
                        for strictDecreaseTerm in strictDecreaseTerms do
                            if allTermsHold then
                                match SparseLinear.tryGetFarkasCoefficients locInvariantAndTransLinearTerms strictDecreaseTerm with
                                | Some strictDecreaseCoefficients -> ()
                                | None -> allTermsHold <- false

                        if allTermsHold then
                            thisDisjunctStrict <- true
                            Log.debug exportInfo.parameters "    Strict decrease for this disjunct."
                        else
                            for weakDecreaseTerm in weakDecreaseTerms do
                                let weakDecreaseCoefficients = SparseLinear.getFarkasCoefficients locInvariantAndTransLinearTerms weakDecreaseTerm
                                ()
                            Log.debug exportInfo.parameters "    Weak decrease for this disjunct."
            if not thisDisjunctStrict then
                allDisjunctsStrict <- false

        if allDisjunctsStrict then
            Log.debug exportInfo.parameters "  Is strictly decreasing and bounded."
            strictDecreaseHintInfo <- (transIdx, decreaseHints, boundHints)::strictDecreaseHintInfo
        else
            Log.debug exportInfo.parameters "  Is weakly decreasing."
            weakDecreaseHintInfo <- (transIdx, decreaseHints)::weakDecreaseHintInfo

    let strictTransitions = strictDecreaseHintInfo |> List.map (fun (transIdx, _, _) -> transIdx) |> Set.ofList
    let transitionsRemovedInThisStep =
        match transitionsToRemove with
        | None -> strictTransitions
        | Some transitionsToRemove ->
            if Set.isSubset transitionsToRemove strictTransitions then
                transitionsToRemove
            else
                raise (System.ArgumentException "Cannot prove transitions to remove as strictly decreasing") 
    let newRemovedTransitions = Set.union removedTransitions transitionsRemovedInThisStep

    (** Step 2: Write out the actual XML. *)
    if Set.isEmpty transitionsRemovedInThisStep then
        Log.log exportInfo.parameters " Skipping transition removal step because no transition was strictly decreasing."
        nextProofStep newRemovedTransitions xmlWriter
    else
        Log.log
            exportInfo.parameters
            (sprintf
                " Removing transitions [%s] (internally known as [%s])."
                (String.concat ", " (Seq.map (fun t -> string (getTransitionId exportInfo.transDuplIdToTransId t)) transitionsRemovedInThisStep))
                (String.concat ", " (Seq.map string transitionsRemovedInThisStep)))
        xmlWriter.WriteStartElement "transitionRemoval"
        xmlWriter.WriteStartElement "rankingFunctions"

        for KeyValue (loc, locRFTerms) in locToRFTerms do
            let locLabel = exportInfo.progCoopInstrumented.GetLocationLabel loc
            let rfLinearTerms = locRFTerms |> List.map SparseLinear.term_to_linear_term

            xmlWriter.WriteStartElement "rankingFunction"
            Programs.exportLocation xmlWriter locLabel

            xmlWriter.WriteStartElement "expression"
            for rfLinearTerm in rfLinearTerms do
                SparseLinear.toCeta xmlWriter Var.plainToCeta rfLinearTerm
            xmlWriter.WriteEndElement () //end expression
            xmlWriter.WriteEndElement () //end rankingFunction
        xmlWriter.WriteEndElement () //end rankingFunctions
        xmlWriter.WriteStartElement "bound"
        for bound in bounds do
            xmlWriter.WriteElementString ("constant", string (bound - bigint.One))
        xmlWriter.WriteEndElement () //end bound

        xmlWriter.WriteStartElement "remove"
        for transIdx in transitionsRemovedInThisStep do
            writeTransitionId exportInfo.transDuplIdToTransId xmlWriter transIdx
        xmlWriter.WriteEndElement () //end remove

        xmlWriter.WriteElementString ("hints", "")
        (* //TODO: Figure out hint format for lexicographic RFs
        xmlWriter.WriteStartElement "hints"
        for (transIdx, decreaseHints, boundHints) in strictDecreaseHintInfo do
            xmlWriter.WriteStartElement "strictDecrease"
            writeTransitionId exportInfo.transDuplIdToTransId xmlWriter transIdx
            xmlWriter.WriteStartElement "boundHints"
            for boundHint in boundHints do
                SparseLinear.writeCeTAFarkasCoefficientHints xmlWriter boundHint
            xmlWriter.WriteEndElement () //end boundHints
            xmlWriter.WriteStartElement "decreaseHints"
            for strictDecreaseHint in decreaseHints do
                SparseLinear.writeCeTAFarkasCoefficientHints xmlWriter strictDecreaseHint
            xmlWriter.WriteEndElement () //end decreaseHints
            xmlWriter.WriteEndElement () //end strictDecrease
        for (transIdx, decreaseHints) in weakDecreaseHintInfo do
            xmlWriter.WriteStartElement "weakDecrease"
            writeTransitionId exportInfo.transDuplIdToTransId xmlWriter transIdx
            xmlWriter.WriteStartElement "decreaseHints"
            for weakDecreaseHints in decreaseHints do
                SparseLinear.writeCeTAFarkasCoefficientHints xmlWriter weakDecreaseHints
            xmlWriter.WriteEndElement () //end decreaseHints
            xmlWriter.WriteEndElement () //end weakDecrease
        xmlWriter.WriteEndElement () //end hints
        *)

        nextProofStep newRemovedTransitions xmlWriter

        xmlWriter.WriteEndElement () //end transitionRemoval

let private exportNonSCCRemovalProof
        (exportInfo : CertificateExportInformation)
        (nextProofStep : XmlWriter -> unit)
        (xmlWriter : XmlWriter) =
    Log.log exportInfo.parameters "Exporting transitionRemoval step to remove non-SCC components."
    //Invent a "full" cooperation program here, by taking the one we have, and extend it by additional locations/transitions:
    let progFullCoop = exportInfo.progCoopInstrumented.Clone()

    //All those locations that haven't been duplicated yet need to be duplicated now:
    let locToExtraDuplLoc = Dictionary()
    for loc in exportInfo.progOrig.Locations do
        match progFullCoop.GetLocationLabel loc with
        | OriginalLocation origLocLabel ->
            if not <| (   progFullCoop.HasLabelledLocation (DuplicatedLocation origLocLabel)
                       || progFullCoop.HasLabelledLocation (DuplicatedCutpointLocation origLocLabel)) then
                let dupLoc = progFullCoop.GetLabelledLocation (DuplicatedLocation origLocLabel)
                // We will need to compute SCCs, and our SCC computation only considers things reachable from init.
                // Thus, add faked transitions from there...
                progFullCoop.AddTransition progFullCoop.Initial [] dupLoc |> ignore
                locToExtraDuplLoc.[loc] <- dupLoc
        | label -> failwithf "Original program contains non-original location %i (%A)" loc label

    //For all the newly copied locations, we now need to add newly copied transitions:
    let progFullExtraTrans = HashSet()
    for (transIdx, (sourceLoc, cmds, targetLoc)) in exportInfo.progOrig.TransitionsWithIdx do
        let mutable needToAddCopiedTransition = false
        let sourceLocDupl =
            match locToExtraDuplLoc.TryGetValue sourceLoc with
            | (true, sourceLocDupl) ->
                needToAddCopiedTransition <- true
                sourceLocDupl
            | _ -> getCoopLocDupl exportInfo sourceLoc
        let targetLocDupl =
            match locToExtraDuplLoc.TryGetValue targetLoc with
            | (true, targetLocDupl) ->
                needToAddCopiedTransition <- true
                targetLocDupl
            | _ -> getCoopLocDupl exportInfo targetLoc

        //We are leaving out cross-SCC edges in instrumentation, so need to re-add those here:
        match exportInfo.progCoopSCCs |> Seq.tryFind (Set.contains sourceLocDupl) with
        | Some sourceLocSCC ->
            if not <| Set.contains targetLocDupl sourceLocSCC then
                needToAddCopiedTransition <- true
        | None -> ()

        if needToAddCopiedTransition then
            let copiedTransIdx = progFullCoop.AddTransition sourceLocDupl cmds targetLocDupl
            exportInfo.transDuplIdToTransId.Add(copiedTransIdx, (transIdx, true))
            progFullExtraTrans.Add copiedTransIdx |> ignore

    //Now remove all the extra invented transitions again, by doing a trivial termination argument encoding
    //simple SCC structure, assigning a constant rank to each location
    let locToRFTerm = Dictionary()
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
                let locRepr = progFullCoop.GetLocationLabel loc
                match locRepr with
                | CutpointRFCheckLocation _ -> ()
                | _ -> locToRFTerm.[loc] <- [Term.constant rank])
    let bound = [bigint (-(List.length progFullCoopSCCs) - 1)]

    let transToExport =
        progFullCoop.TransitionsWithIdx
        |> Seq.filter (fun (transIdx, _) -> progFullExtraTrans.Contains transIdx || exportInfo.transDuplIdToTransId.ContainsKey transIdx)

    exportTransitionRemovalProof
        {exportInfo with progCoopInstrumented = progFullCoop}
        (Dictionary())
        locToRFTerm
        bound
        transToExport 
        (Some (Set.ofSeq progFullExtraTrans))
        Formula.is_noninstr_var
        Set.empty
        (fun _ xmlWriter -> nextProofStep xmlWriter)
        xmlWriter

let private getBeforeTransitionId (exportInfo: CertificateExportInformation) cp =
    exportInfo.progCoopInstrumented.TransitionsTo cp
    |> Seq.find
        (fun (_, (source, _, _)) ->
               match exportInfo.progCoopInstrumented.GetLocationLabel source with
               | CutpointDummyEntryLocation _ -> true
               | _ -> false)
    |> fst

let private getAfterTransitionId (exportInfo: CertificateExportInformation) cp =
    exportInfo.progCoopInstrumented.TransitionsFrom cp
    |> Seq.find
        (fun (_, (_, _, target)) ->
               match exportInfo.progCoopInstrumented.GetLocationLabel target with
               | CutpointVarSnapshotLocation _ -> true
               | _ -> false)
    |> fst

let private exportAuxLocationAdditionProof
        (exportInfo: CertificateExportInformation)
        (nextProofStep: XmlWriter -> unit)
        (xmlWriter : XmlWriter) =
    for cp in exportInfo.cpToToCpDuplicateTransId.Keys do
        let cpLabel =
            match exportInfo.progOrig.GetLocationLabel cp with
            | Programs.OriginalLocation label -> label
            | label -> failwithf "Exporting program with non-original location %i (label %A)" cp label
        let cpDuplLabel = DuplicatedCutpointLocation cpLabel
        let cpDupl = exportInfo.progCoopInstrumented.GetLabelledLocation cpDuplLabel

        Log.log exportInfo.parameters (sprintf "Exporting locationAddition proof step for cutpoint %i (%A)" cpDupl cpDuplLabel)

        //Make up two new locations, around the considered cutpoint:
        let beforeTransitionId = getBeforeTransitionId exportInfo cpDupl
        let afterTransitionId = getAfterTransitionId exportInfo cpDupl

        // Now add the two locations:
        xmlWriter.WriteStartElement "locationAddition" // "before" location
        exportTransition
            xmlWriter exportInfo.progOrig.Variables beforeTransitionId
            (Programs.CutpointDummyEntryLocation cpLabel) [] cpDuplLabel
            Formula.is_noninstr_var

        xmlWriter.WriteStartElement "locationAddition" // "after" location
        exportTransition
            xmlWriter exportInfo.progOrig.Variables afterTransitionId
            cpDuplLabel [] (Programs.CutpointVarSnapshotLocation cpLabel)
            Formula.is_noninstr_var

    nextProofStep xmlWriter

    for _ in exportInfo.cpToToCpDuplicateTransId.Keys do
        xmlWriter.WriteEndElement () //end locationAddition ("after" location)
        xmlWriter.WriteEndElement () //end locationAddition ("before" location)

/// Export per-node invariants generated by abstract interpretation into proof.
// Note: We re-use the existing definition of Impact-style proofs here, as the
// certifier does not enforce the tree property on the generated ARG. Thus, each
// program location corresponds to exactly one node in the generated ARG, and
// program transitions are "child" edges in the ARG.
let private exportAIInvariantsProof
        (exportInfo : CertificateExportInformation)
        (nextProofStep : XmlWriter -> unit)
        (xmlWriter : XmlWriter) =
    let isNonTrivial (locToAIInvariant : Dictionary<ProgramLocation, IIntAbsDom.IIntAbsDom>) =
        locToAIInvariant.Values
        |> Seq.exists (fun absDomElement -> absDomElement.to_formula() <> Formula.formula.True)

    match exportInfo.locToAIInvariant with
    | Some locToAIInvariant when isNonTrivial locToAIInvariant ->
        Log.log exportInfo.parameters "Exporting newInvariants proof step encoding invariants obtained by abstract interpretation."
        xmlWriter.WriteStartElement "newInvariants"

        let shouldExportLocation = shouldExportLocation exportInfo.progCoopInstrumented exportInfo.progCoopInstrumented.Locations true
        let shouldExportTransition = shouldExportTransition exportInfo.progCoopInstrumented shouldExportLocation None Set.empty

        (*** Start of declaring new invariants ***)
        let locToInvariantTerms = Dictionary()
        xmlWriter.WriteStartElement "invariants"
        for loc in exportInfo.progCoopInstrumented.Locations do
            if shouldExportLocation loc then
                let origLoc = locToOriginalLocation exportInfo.progCoopInstrumented loc
                let locLabel = exportInfo.progCoopInstrumented.GetLocationLabel loc
                let invariant = locToAIInvariant.[origLoc].to_formula()
                Log.debug exportInfo.parameters (sprintf "  Added invariant for location %i (%A): %s" loc locLabel (string invariant))
                let invariantLinearTerms = invariant.ToLinearTerms ()
                locToInvariantTerms.Add(loc, invariantLinearTerms)
                xmlWriter.WriteStartElement "invariant"

                Programs.exportLocation xmlWriter locLabel

                xmlWriter.WriteStartElement "formula"
                Formula.linear_terms_to_ceta xmlWriter Var.plainToCeta invariantLinearTerms Formula.is_noninstr_var
                xmlWriter.WriteEndElement () //end formula
                xmlWriter.WriteEndElement () //end invariant
        xmlWriter.WriteEndElement () //end invariants
        (*** End of declaring new invariants ***)

        (*** Start of proving soundness of new invariants ***)
        xmlWriter.WriteStartElement "impact"
        xmlWriter.WriteElementString ("initial", string exportInfo.progCoopInstrumented.Initial)
        xmlWriter.WriteStartElement "nodes"
        for loc in exportInfo.progCoopInstrumented.Locations do
            if shouldExportLocation loc then
                let invariantLinearTerms = locToInvariantTerms.[loc]
                xmlWriter.WriteStartElement "node"

                xmlWriter.WriteElementString ("nodeId", string loc)

                xmlWriter.WriteStartElement "invariant"
                Formula.linear_terms_to_ceta xmlWriter Var.plainToCeta invariantLinearTerms Formula.is_noninstr_var
                xmlWriter.WriteEndElement () // invariant end

                Programs.exportLocation xmlWriter (exportInfo.progCoopInstrumented.GetLocationLabel loc)

                xmlWriter.WriteStartElement "children"
                for (transIdx, (_, cmds, childLoc)) in exportInfo.progCoopInstrumented.TransitionsFrom loc do
                    if shouldExportTransition transIdx loc childLoc then
                        let childLocInvariantLinearTerms = locToInvariantTerms.[childLoc]
                        let (transFormula, varToMaxSSAIdx) = Programs.cmdsToCetaFormula exportInfo.progCoopInstrumented.Variables cmds
                        let varToPre var = Var.prime_var var 0
                        let varToPost var =
                            match Map.tryFind var varToMaxSSAIdx with
                            | Some idx -> Var.prime_var var idx
                            | None -> var
                        let transLinearTerms =
                            Formula.formula.FormulasToLinearTerms (transFormula :> _)
                            |> Formula.filter_instr_vars Formula.is_noninstr_var
                        let locInvariantAndTransLinearTerms = List.append (List.map (SparseLinear.alpha varToPre) invariantLinearTerms) transLinearTerms
                        xmlWriter.WriteStartElement "child"
                        writeTransitionId exportInfo.transDuplIdToTransId xmlWriter transIdx
                        xmlWriter.WriteElementString ("nodeId", string childLoc)
                        xmlWriter.WriteStartElement "hints"
                        for lt in childLocInvariantLinearTerms do
                            SparseLinear.writeCeTALinearImplicationHints xmlWriter locInvariantAndTransLinearTerms (SparseLinear.alpha varToPost lt)
                        xmlWriter.WriteEndElement () // hints end
                        xmlWriter.WriteEndElement () // child end
                xmlWriter.WriteEndElement () // children end
                xmlWriter.WriteEndElement () // node end
        xmlWriter.WriteEndElement () // nodes end
        xmlWriter.WriteEndElement () // impact end
        (*** End of proving soundness of new invariants ***)

        nextProofStep xmlWriter
        xmlWriter.WriteEndElement () //end newInvariants
    | _ -> nextProofStep xmlWriter

let private exportSccDecompositionProof
        (exportInfo : CertificateExportInformation)
        (nextProofStep : ProgramSCC -> XmlWriter -> unit)
        (xmlWriter : XmlWriter) =
    Log.log exportInfo.parameters "Exporting SCCDecomposition proof step."
    xmlWriter.WriteStartElement "sccDecomposition"
    let shouldExportLocation = shouldExportLocation exportInfo.progCoopInstrumented exportInfo.progCoopInstrumented.Locations false
    for scc in exportInfo.progCoopSCCs do
        Log.log exportInfo.parameters (sprintf " Considering SCC of locations {%s}" (String.concat ", " (Seq.map string scc)))
        xmlWriter.WriteStartElement "sccWithProof"
        xmlWriter.WriteStartElement "scc"
        for loc in scc do
            if shouldExportLocation loc then
                Programs.exportLocationLabel xmlWriter (exportInfo.progCoopInstrumented.GetLocationLabel loc)
        xmlWriter.WriteEndElement () //end scc
        nextProofStep scc xmlWriter
        xmlWriter.WriteEndElement () //end sccWithProof
    xmlWriter.WriteEndElement () //end sccDecomposition

let private exportInitialLexRFTransRemovalProof
        (exportInfo : CertificateExportInformation)
        (nextProofStep : ProgramSCC -> Set<TransitionId> -> XmlWriter -> unit)
        (scc : ProgramSCC)
        (xmlWriter : XmlWriter) =
    let thisSCCRankFunctions =
        exportInfo.foundInitialLexRankFunctions
        |> Map.toSeq
        |> Seq.filter (fun (sccLocs, _) -> not <| Set.isEmpty (Set.intersect sccLocs scc))
        |> Seq.map snd
        |> List.concat

    let shouldExportLocation = shouldExportLocation exportInfo.progCoopInstrumented scc false
    let rec exportNextRF (rankFunctions : (Map<ProgramLocation, SparseLinear.LinearTerm> * Map<Set<TransitionId>, bigint> * Set<TransitionId>) list) removedTransitions xmlWriter =
        match rankFunctions with
        | [] -> nextProofStep scc removedTransitions xmlWriter
        | (locToRF, transToBounds, _) :: remainingRankFunctions ->
            Log.log exportInfo.parameters "Exporting transitionRemoval proof step based on lexicographic rank functions synthesised without safety loop."
            //Extract the actual per-location rank functions and overall bound:
            let shouldExportTransition = shouldExportTransition exportInfo.progCoopInstrumented shouldExportLocation None removedTransitions
            let bound = [transToBounds |> Map.toSeq |> Seq.map snd |> Seq.fold min (bigint System.Int32.MaxValue)]
            let locToRFTerm = Dictionary()
            for loc in scc do
                if shouldExportLocation loc then
                    let locLabel = exportInfo.progCoopInstrumented.GetLocationLabel loc
                    // We filter the CutpointVarSnapshotLocation nodes in the synth process, so look for something else here:
                    let locWithRF =
                        match locLabel with
                        | CutpointVarSnapshotLocation baseLabel ->
                            exportInfo.progCoopInstrumented.GetLabelledLocation (DuplicatedCutpointLocation baseLabel)
                        | _ -> loc
                    let locRF = defaultArg (locToRF.TryFind locWithRF) Map.empty
                    let rfTerm = SparseLinear.linear_term_to_term locRF
                    locToRFTerm.[loc] <- [Term.subst (Var.unprime_var >> Formula.eval_const_var) rfTerm]

            let transToExport =
                exportInfo.progCoopInstrumented.TransitionsWithIdx
                |> Seq.filter (fun (transIdx, (source, _, target)) -> shouldExportTransition transIdx source target)

            exportTransitionRemovalProof exportInfo (Dictionary()) locToRFTerm bound transToExport None Formula.is_noninstr_var removedTransitions (exportNextRF remainingRankFunctions) xmlWriter
    exportNextRF thisSCCRankFunctions Set.empty xmlWriter

let private findSCCsInTransitions
        (exportInfo: CertificateExportInformation)
        (scc : ProgramSCC)
        (removedTransitions : Set<TransitionId>)
        (entryLoc : ProgramLocation)
        (returnTrivialComponents : bool) =
    let shouldExportLocation = shouldExportLocation exportInfo.progCoopInstrumented scc false
    let shouldExportTransition = shouldExportTransition exportInfo.progCoopInstrumented shouldExportLocation None removedTransitions
    let graphEdges = ListDictionary()
    for (transIdx, (source, _, target)) in exportInfo.progCoopInstrumented.TransitionsWithIdx do
        if shouldExportTransition transIdx source target then
            graphEdges.Add(source, (transIdx, (source, 0, target)))
            graphEdges.Add(entryLoc, (0, (entryLoc, 0, source)))
    SCC.find_sccs graphEdges entryLoc  returnTrivialComponents

let private exportFinalProof
        (exportInfo: CertificateExportInformation)
        (scc : ProgramSCC)
        ((cp, _) : (ProgramLocation * ProgramLocation))
        (removedTransitions : Set<TransitionId>)
        (xmlWriter : XmlWriter) =
    Log.log exportInfo.parameters "Exporting transitionRemoval proof step that removes all remaining trivial SCCs."
    let shouldExportLocation = shouldExportLocation exportInfo.progCoopInstrumented scc false
    let shouldExportTransition = shouldExportTransition exportInfo.progCoopInstrumented shouldExportLocation None removedTransitions
    let shouldExportVariable = shouldExportVariable cp

    //We assume that at this point, no more _feasible_ cycles are left. Thus, we just need to eliminate all remaining
    //transitions going into our target cutpoint as in the initial SCC decomposition.
    //Feasible cycles means that either we removed some crucial transitions, or that we've proved that the
    //cutpoint entry location has invariant FALSE.
    //
    //To remove the remaining transitions in the former case, we just look at the trivial components, in order,
    //starting with something that has nothing incoming. First, find such a node, then use standard SCC numbering
    //we get from Tarjan. If we can't find such a node, assume that we are in the infeasible case, and use a
    //constant rank function eliminating the cutpoint entry transition.
    let entryLoc =
        scc
        |> Seq.tryFind
             (fun loc ->
                if shouldExportLocation loc then
                    let inDeg =
                        exportInfo.progCoopInstrumented.TransitionsTo loc
                        |> Seq.filter (fun (transIdx, (source, _, target)) -> shouldExportTransition transIdx source target)
                        |> Seq.length
                    inDeg = 0
                else
                    false)

    let (locToRFTerms, bounds, locToInvariants) =
        match entryLoc with
        | Some entryLoc ->
            let locToRFTerm = Dictionary()
            let sccs = findSCCsInTransitions exportInfo scc removedTransitions entryLoc true
            sccs
            |> List.iteri
                (fun idx scc ->
                    scc |> Seq.filter shouldExportLocation |> Seq.iter (fun loc -> locToRFTerm.[loc] <- [Term.constant (-idx - 1)]))
            (locToRFTerm, [bigint (-(List.length sccs) - 1)], Dictionary())
        | None ->
            let locToRFTerm = Dictionary()
            for loc in scc do
                if shouldExportLocation loc then
                    locToRFTerm.[loc] <- [Term.constant -1]
            locToRFTerm.[exportInfo.progCoopInstrumented.GetLabelledLocation (CutpointDummyEntryLocation (string cp))] <- [Term.constant 1]
            locToRFTerm.[exportInfo.progCoopInstrumented.GetLabelledLocation (DuplicatedCutpointLocation (string cp))] <- [Term.constant 0]
            let (_, locToInvariants) = getImpactInvariantsForLocs exportInfo scc removedTransitions cp
            (locToRFTerm, [bigint.Zero], locToInvariants)

    let exportTrivialProof _ _ =
        xmlWriter.WriteStartElement "cutTransitionSplit"
        xmlWriter.WriteEndElement () //end cutTransitionSplit

    let transToExport =
        exportInfo.progCoopInstrumented.TransitionsWithIdx
        |> Seq.filter (fun (transIdx, (source, _, target)) -> shouldExportTransition transIdx source target)
    exportTransitionRemovalProof exportInfo locToInvariants locToRFTerms bounds transToExport None shouldExportVariable removedTransitions exportTrivialProof xmlWriter

let private exportCutTransitionSplitProof
        (exportInfo: CertificateExportInformation)
        (nextProofStep: ProgramSCC -> Set<TransitionId> -> ProgramLocation * ProgramLocation -> XmlWriter -> unit)
        (scc : ProgramSCC)
        (removedTransitions : Set<TransitionId>)
        (xmlWriter : XmlWriter) =
    Log.log exportInfo.parameters "Exporting cutTransitionSplit proof step to focus remaining proof on individual cutpoints."
    let cutpointsInSCC =
        scc
        |> Set.filterMap
            (fun loc ->
                match exportInfo.progCoopInstrumented.GetLocationLabel loc with
                | DuplicatedCutpointLocation locLabel -> Some <| (exportInfo.progCoopInstrumented.GetLabelledLocation (OriginalLocation locLabel), loc)
                | _ -> None)

    xmlWriter.WriteStartElement "cutTransitionSplit"
    for (cp, cpDupl) in cutpointsInSCC do
        Log.log exportInfo.parameters (sprintf " Considering cutpoint %i %A" cpDupl (exportInfo.progCoopInstrumented.GetLocationLabel cpDupl))
        let cpSwitchToCoopTrans = exportInfo.cpToToCpDuplicateTransId.[cp]
        xmlWriter.WriteStartElement "cutTransitionsWithProof"

        xmlWriter.WriteStartElement "cutTransitions"
        xmlWriter.WriteElementString ("transitionId", string cpSwitchToCoopTrans)
        xmlWriter.WriteEndElement () //end cutTransitions

        nextProofStep scc removedTransitions (cp, cpDupl) xmlWriter

        xmlWriter.WriteEndElement () //end cutTransitionsWithProof

    xmlWriter.WriteEndElement () //end cutTransitionSplit

let private exportCopyVariableAdditionProof
        (exportInfo: CertificateExportInformation)
        (nextProofStep: ProgramSCC -> Set<TransitionId> -> ProgramLocation * ProgramLocation -> XmlWriter -> unit)
        (scc : ProgramSCC)
        (removedTransitions : Set<TransitionId>)
        ((cp, cpDupl) : ProgramLocation * ProgramLocation)
        (xmlWriter : XmlWriter) =
    Log.log exportInfo.parameters "Exporting freshVariableAddition proof step to introduce variable snapshots."

    let afterTransitionId = getAfterTransitionId exportInfo cpDupl
    let shouldExportLocation = shouldExportLocation exportInfo.progCoopInstrumented scc false
    let shouldExportTransition = shouldExportTransition exportInfo.progCoopInstrumented shouldExportLocation (Some cp) removedTransitions

    for variable in exportInfo.progOrig.Variables do
        let snaphottedVar = Formula.state_snapshot_var cp variable
        let setSnapshottedVarTerms =
            (Formula.Eq (Term.var (Var.prime_var variable 0),
                         Term.var (Var.prime_var snaphottedVar 1))).ToLinearTerms()
        let prePostMap = Map.ofList [ (variable, 0) ; (snaphottedVar, 1) ]

        xmlWriter.WriteStartElement "freshVariableAddition"
        xmlWriter.WriteElementString ("variableId", snaphottedVar)
        xmlWriter.WriteElementString ("int", "")

        xmlWriter.WriteStartElement "additionalFormulas"
        for (transIdx, (source, _, target)) in exportInfo.progCoopInstrumented.TransitionsWithIdx do
            if shouldExportTransition transIdx source target then
                xmlWriter.WriteStartElement "additionalFormula"
                writeTransitionId exportInfo.transDuplIdToTransId xmlWriter transIdx
                (* BAND-AID *)
                //TODO: ceta should accept -x_copy + x <= 0 && x_copy -x <= 0, as generated by
                //Formula.linear_terms_to_ceta xmlWriter (Var.toCeta prePostMap) setSnapshottedVarTerms (fun _ -> true)
                xmlWriter.WriteStartElement "conjunction"
                xmlWriter.WriteStartElement "leq"
                if transIdx = afterTransitionId then
                    xmlWriter.WriteElementString ("variableId", variable)
                else
                    xmlWriter.WriteElementString ("variableId", snaphottedVar)
                xmlWriter.WriteStartElement "post"
                xmlWriter.WriteElementString ("variableId", snaphottedVar)
                xmlWriter.WriteEndElement() //end post
                xmlWriter.WriteEndElement() //end leq
                xmlWriter.WriteStartElement "leq"
                xmlWriter.WriteStartElement "post"
                xmlWriter.WriteElementString ("variableId", snaphottedVar)
                xmlWriter.WriteEndElement() //end post
                if transIdx = afterTransitionId then
                    xmlWriter.WriteElementString ("variableId", variable)
                else
                    xmlWriter.WriteElementString ("variableId", snaphottedVar)
                xmlWriter.WriteEndElement() //end leq
                xmlWriter.WriteEndElement() //end conjunction
                (* BAND-AID *)
                xmlWriter.WriteEndElement () //end additionalFormula

        xmlWriter.WriteEndElement () //end additionalFormulas

    nextProofStep scc removedTransitions (cp, cpDupl) xmlWriter

    for _ in exportInfo.progOrig.Variables do
        xmlWriter.WriteEndElement () //end freshVariableAddition

let private exportNewImpactInvariantsProof
        (exportInfo: CertificateExportInformation)
        (nextProofStep: ProgramSCC -> Set<TransitionId> -> ProgramLocation * ProgramLocation -> XmlWriter -> unit)
        (scc : ProgramSCC)
        (removedTransitions : Set<TransitionId>)
        ((cp, cpDupl) : ProgramLocation * ProgramLocation)
        (xmlWriter : XmlWriter) =
    Log.log exportInfo.parameters "Exporting newInvariants proof step encoding invariants obtained by safety proving."

    let shouldExportLocation = shouldExportLocation exportInfo.progCoopInstrumented scc true
    let shouldExportTransition = shouldExportTransition exportInfo.progCoopInstrumented shouldExportLocation (Some cp) removedTransitions
    let shouldExportVariable = shouldExportVariable cp

    let (argIsTrivial, locToInvariants) = getImpactInvariantsForLocs exportInfo scc removedTransitions cp

    if not argIsTrivial then
        xmlWriter.WriteStartElement "newInvariants"
        xmlWriter.WriteStartElement "invariants"
        for KeyValue(loc, locInvariants) in locToInvariants do
            let locLabel = exportInfo.progCoopInstrumented.GetLocationLabel loc
            Log.debug exportInfo.parameters
                (sprintf "  Added invariant for location %i (%A): (%s)"
                    loc locLabel
                    (String.concat
                        ") || ("
                        (Seq.map (fun locInvariant -> String.concat " && " (Seq.map string locInvariant)) locInvariants)))
            xmlWriter.WriteStartElement "invariant"

            Programs.exportLocation xmlWriter locLabel

            xmlWriter.WriteStartElement "formula"
            xmlWriter.WriteStartElement "disjunction"
            for locInvariant in locInvariants do
                Formula.linear_terms_to_ceta xmlWriter Var.plainToCeta (Formula.formula.FormulasToLinearTerms (locInvariant :> _)) shouldExportVariable
            xmlWriter.WriteEndElement () //end disjunction
            xmlWriter.WriteEndElement () //end formula
            xmlWriter.WriteEndElement () //end invariant

        xmlWriter.WriteEndElement () //end invariants

        exportInfo.impactArg.ToCeta xmlWriter (writeTransitionId exportInfo.transDuplIdToTransId) shouldExportLocation shouldExportTransition shouldExportVariable (Some cpDupl)

    nextProofStep scc removedTransitions (cp, cpDupl) xmlWriter

    if not argIsTrivial then
        xmlWriter.WriteEndElement () //end newInvariants

let private exportSafetyTransitionRemovalProof
        (exportInfo: CertificateExportInformation)
        (nextProofStep: ProgramSCC -> ProgramLocation * ProgramLocation -> Set<TransitionId> -> XmlWriter -> unit)
        (scc : ProgramSCC)
        (removedTransitions : Set<TransitionId>)
        ((cp, cpDupl) : ProgramLocation * ProgramLocation)
        (xmlWriter : XmlWriter) =
    let lexRfCheckFormulas =
        match exportInfo.foundLexRankFunctions.TryFind cp with
        | Some res -> res
        | None -> []

    if List.isEmpty lexRfCheckFormulas then
        nextProofStep scc (cp, cpDupl) removedTransitions xmlWriter
    else
        Log.log exportInfo.parameters "Exporting transitionRemoval proof step based on Terminator-style lexicographic rank functions."
        (* Step 1: Extract rank functions. *)
        let rfTerms =
            lexRfCheckFormulas
            |> List.map
                (fun (decreasingCheckFormula, _, _) ->
                    //This is rather brittle, as it depends on the formulas we generate in rankfunction.fs for this case...
                    match decreasingCheckFormula with
                    | Formula.Lt(rankFunctionOnNewVars, _) -> rankFunctionOnNewVars
                    | _ -> dieWith "Could not retrieve rank function from internal proof structure.")
        let rfBounds =
            lexRfCheckFormulas
            |> List.map
                (fun (_, _, boundCheckFormula) ->
                    match boundCheckFormula with
                    | Formula.Ge(_, Term.Const c) -> -1 + int c
                    | _ -> dieWith "Could not retrieve bound for rank function from internal proof structure.")

        //We map every location in the SCC to the chosen RF at the cutpoint, with the exception of
        //the "dummy" location we inserted before the cutpoint, which we map to the RF on the
        //copy of variable we made. Then, every incoming transition to the dummy location should
        //decrease.
        let locToRFTerm = Dictionary()
        let cpLabel = getBaseLabel (exportInfo.progCoopInstrumented.GetLocationLabel cpDupl)
        for loc in scc do
            match exportInfo.progCoopInstrumented.GetLocationLabel loc with
            | DuplicatedCutpointLocation baseLabel when baseLabel = cpLabel ->
                locToRFTerm.[loc] <- rfTerms
            | DuplicatedLocation _
            | DuplicatedCutpointLocation _
            | CutpointVarSnapshotLocation _
            | CutpointDummyEntryLocation _ ->
                locToRFTerm.[loc] <- List.map (Term.alpha (Formula.state_snapshot_var cp)) rfTerms
            | OriginalLocation _
            | CutpointRFCheckLocation _ -> () //Do not export those (shouldn't be in an SCC here anyway)
        let rfBound = List.map (fun (b : int) -> bigint b) rfBounds

        (* Step 2: Extract invariants *)
        let shouldExportLocationForTerm = shouldExportLocation exportInfo.progCoopInstrumented scc false
        let shouldExportTransitionForTerm = shouldExportTransition exportInfo.progCoopInstrumented shouldExportLocationForTerm (Some cp) removedTransitions
        let shouldExportVariable = shouldExportVariable cp

        let transToExport =
            exportInfo.progCoopInstrumented.TransitionsWithIdx
            |> Seq.filter (fun (transIdx, (source, _, target)) -> shouldExportTransitionForTerm transIdx source target)

        let (_, locToInvariants) = getImpactInvariantsForLocs exportInfo scc removedTransitions cp
        exportTransitionRemovalProof exportInfo locToInvariants locToRFTerm rfBound transToExport None shouldExportVariable removedTransitions (nextProofStep scc (cp, cpDupl)) xmlWriter

let private exportSwitchToCooperationTerminationProof
        (exportInfo : CertificateExportInformation)
        (nextProofStep : XmlWriter -> unit)
        (xmlWriter : XmlWriter) =
    Log.log exportInfo.parameters "Exporting switchToCooperationTermination proof step."
    xmlWriter.WriteStartElement "switchToCooperationTermination"

    xmlWriter.WriteStartElement "cutPoints"
    for KeyValue(cp, cpToCoopDupTrans) in exportInfo.cpToToCpDuplicateTransId do
        xmlWriter.WriteStartElement "cutPoint"
        Programs.exportLocationLabel xmlWriter (exportInfo.progOrig.GetLocationLabel cp)
        xmlWriter.WriteElementString ("skipId", string cpToCoopDupTrans)

        let (_, cmds, _) = exportInfo.progCoopInstrumented.GetTransition cpToCoopDupTrans
        let (transFormula, varToMaxSSAIdx) = cmdsToCetaFormula exportInfo.progCoopInstrumented.Variables cmds
        let transLinearTerms =
            Formula.formula.FormulasToLinearTerms (transFormula :> _)
            |> Formula.filter_instr_vars Formula.is_noninstr_var
        xmlWriter.WriteStartElement "skipFormula"
        Formula.linear_terms_to_ceta xmlWriter (Var.toCeta varToMaxSSAIdx) transLinearTerms Formula.is_noninstr_var
        xmlWriter.WriteEndElement () //skipFormula end

        xmlWriter.WriteEndElement () //end cutPoint
    xmlWriter.WriteEndElement () //end cutPoints

    xmlWriter
    |> exportNonSCCRemovalProof exportInfo (
        exportAuxLocationAdditionProof exportInfo nextProofStep)

    xmlWriter.WriteEndElement () //end switchToCooperationTermination

let private exportPerSCCSafetyTerminationProof exportInfo (nextProofStep: ProgramSCC -> ProgramLocation * ProgramLocation -> Set<TransitionId> -> XmlWriter -> unit) scc removedTransitions (cp, cpDupl) =
    match exportInfo.foundLexRankFunctions.TryFind cp with
    | Some (_ :: _) ->
        exportCopyVariableAdditionProof exportInfo (
         exportNewImpactInvariantsProof exportInfo (
          exportSafetyTransitionRemovalProof exportInfo (
           nextProofStep))) scc removedTransitions (cp, cpDupl)
    | _ ->
        let (_, locToInvariants) = getImpactInvariantsForLocs exportInfo scc removedTransitions cp
        let hasDisabledLocation = locToInvariants.Values |> Seq.exists ((=) [[Formula.formula.False]])
        let hasRemainingIncomingCPEdge =
            let cpEntryLoc = exportInfo.progCoopInstrumented.GetLabelledLocation (CutpointDummyEntryLocation (string cp))
            let cpEntryTrans = exportInfo.progCoopInstrumented.TransitionsFrom cpEntryLoc |> List.head |> fst
            not <| Set.contains cpEntryTrans removedTransitions
        if hasDisabledLocation && hasRemainingIncomingCPEdge then
            exportNewImpactInvariantsProof exportInfo (
             fun scc removed cp -> nextProofStep scc cp removed)
              scc removedTransitions (cp, cpDupl)
        else
            nextProofStep scc (cp, cpDupl) removedTransitions

let private exportSafetyTerminationProof exportInfo (nextProofStep: ProgramSCC -> ProgramLocation * ProgramLocation -> Set<TransitionId> -> XmlWriter -> unit) scc removedTransitions =
    let hasRemainingCycles = not <| List.isEmpty (findSCCsInTransitions exportInfo scc removedTransitions -42 false)
    if hasRemainingCycles then
        exportCutTransitionSplitProof exportInfo (
         exportPerSCCSafetyTerminationProof exportInfo nextProofStep) scc removedTransitions
    else
        nextProofStep scc (-42, -42) removedTransitions

let exportProofCertificate
        (pars : Parameters.parameters)
        (progOrig : Programs.Program)
        (progCoopInstrumented : Programs.Program)
        (cpToToCpDuplicateTransId : Dictionary<int, int>)
        (transDuplIdToTransId : Dictionary<int, int * bool>)
        (locToAIInvariant : Dictionary<int, IIntAbsDom.IIntAbsDom> option)
        (progCoopSCCs : Set<int> list)
        (foundInitialLexRankFunctions : Map<Set<int>, (Map<int, Map<Var.var, bigint>> * Map<Set<int>, bigint> * Set<int>) list>)
        (impactArg : Impact.ImpactARG)
        (foundLexRankFunctions : Map<ProgramLocation, (Formula.formula * Formula.formula * Formula.formula) list>)
        (xmlWriter : XmlWriter) =
    let exportInfo =
        {
            parameters = pars
            progOrig = progOrig
            progCoopInstrumented = progCoopInstrumented
            progCoopSCCs = progCoopSCCs
            locToAIInvariant = locToAIInvariant
            cpToToCpDuplicateTransId = cpToToCpDuplicateTransId
            transDuplIdToTransId = transDuplIdToTransId
            impactArg = impactArg
            foundInitialLexRankFunctions = foundInitialLexRankFunctions
            foundLexRankFunctions = foundLexRankFunctions
        }

    xmlWriter.WriteStartElement "certificationProblem"
    xmlWriter.WriteStartElement "input"
    progOrig.ToCeta xmlWriter "lts" (fun _ -> true)
    xmlWriter.WriteEndElement () //end input

    xmlWriter.WriteElementString("cpfVersion", "2.4")

    xmlWriter.WriteStartElement "proof"
    xmlWriter.WriteStartElement "ltsTerminationProof"
    xmlWriter
    |> exportSwitchToCooperationTerminationProof exportInfo (
        exportAIInvariantsProof exportInfo (
         exportSccDecompositionProof exportInfo (
          exportInitialLexRFTransRemovalProof exportInfo (
           exportSafetyTerminationProof exportInfo (
            exportFinalProof exportInfo)))))
    xmlWriter.WriteEndElement () //end proof
    xmlWriter.WriteEndElement () //end ltsTerminationProof

    xmlWriter.WriteStartElement "origin"
    xmlWriter.WriteStartElement "proofOrigin"
    xmlWriter.WriteStartElement "tool"
    xmlWriter.WriteElementString ("name", "T2Cert")
    xmlWriter.WriteElementString ("version", "1.0")
    xmlWriter.WriteEndElement () //end tool 
    xmlWriter.WriteEndElement () //end proofOrigin
    xmlWriter.WriteEndElement () //end origin
    xmlWriter.WriteEndElement () //end certificationProblem
