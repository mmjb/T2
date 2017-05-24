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
        /// Invariants extracted from Impact graph, filled in when we compute them the first time.
        /// If the Impact graph was trivial, we don't have any invariants, but don't need to check that again.
        mutable impactInvariants : Map<ProgramSCC * ProgramLocation, Dictionary<ProgramLocation, Formula.formula list list> option>

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

let private getImpactInvariantsForLocs
        (exportInfo: CertificateExportInformation)
        (scc : ProgramSCC)
        (removedTransitions : Set<TransitionId>)
        (cp : ProgramLocation) =
    match exportInfo.impactInvariants.TryFind (scc, cp) with
    | None ->
        let shouldExportLocation = shouldExportLocation exportInfo.progCoopInstrumented scc true
        let shouldExportTransition = shouldExportTransition exportInfo.progCoopInstrumented shouldExportLocation (Some cp) removedTransitions
        let shouldExportVariable = shouldExportVariable cp

        let argNodesToReport = exportInfo.impactArg.GetCetaFilteredARGNodes shouldExportLocation shouldExportTransition
        let shouldExportVariableForLocation locLabel =
            match locLabel with
            | OriginalLocation _ -> Formula.is_noninstr_var
            | _ -> shouldExportVariable
        let (snapshotFixupLocsToIgnore, _) = exportInfo.impactArg.GetCutpointSnapshotExportFixup cp argNodesToReport shouldExportVariableForLocation
        argNodesToReport.RemoveAll snapshotFixupLocsToIgnore

        let locToInvariants = Dictionary()

        let res =
            if exportInfo.impactArg.IsTrivial argNodesToReport shouldExportVariable then
                None
            else
                for loc in exportInfo.progCoopInstrumented.Locations do
                    if shouldExportLocation loc then
                        let locInvariants =
                            exportInfo.impactArg.GetLocationInvariantForNodes argNodesToReport loc
                        locToInvariants.[loc] <- locInvariants
                Some locToInvariants
        exportInfo.impactInvariants <- Map.add (scc, cp) res exportInfo.impactInvariants
        res
    | Some cachedResult ->
        cachedResult

let private exportTransitionRemovalProof
        (exportInfo : CertificateExportInformation)
        (locToInvariant: Dictionary<ProgramLocation, Formula.formula list list>)
        (locToRFTerms : Dictionary<ProgramLocation, Term.term list>)
        (bounds : bigint list)
        (transitionsToExport : (TransitionId * Transition) seq)
        (transitionsToRemove : Set<TransitionId>)
        (shouldExportVariable : Var.var -> bool)
        (removedTransitions : Set<TransitionId>)
        (nextProofStep : Set<TransitionId> -> XmlWriter -> unit)
        (xmlWriter : XmlWriter) =
    (** Step 1: Compute hints, if needed *)
    let mutable strictlyDecreasingTransitions = Set.empty

    /// Maps transitions to hints for RF application.
    /// Given R rank functions in our lexicographic RF f, we use the following encoding:
    /// Assume hints = transitionToHints.[transIdx] for some transIdx.
    /// If the invariant on the source of transIdx may be a disjunction inv_1 ... inv_n, 
    /// then hints has n elements, with element j corresponding to disjunct inv_j.
    ///  If we have proven strict decrease (i.e., transIdx in strictlyDecreasingTransitions), then
    ///    (weakDecreaseHints, boundedHints, strictDecreaseHints, strictDecreaseAtRfIndex) = hints.[j] such that:
    ///    weakDecreaseHints.[i] provides hints for inv_j && transition => f_source.[i] >= f_target.[i] for 0 <= i < strictDecreaseAtRfIndex,
    ///    boundedHints provides hints for          inv_j && transition => f_source.[List.length weakDecreaseHints] > bound.[List.length weakDecreaseHints],
    ///    strictDecreaseHints provides hints for   inv_j && transition => f_source.[List.length weakDecreaseHints] > f_target.[List.length weakDecreaseHints],
    ///  If we have proven weak decrease (i.e., transIdx not in strictlyDecreasingTransitions), then
    ///    (weakDecreaseHints, _, _, _) = hints.[j] such that:
    ///    weakDecreaseHints.[i] provides hints for inv_j && transition => f_source.[i] >= f_target.[i] for 0 <= i < R
    let mutable transitionToHints = Map.empty

    if exportInfo.parameters.export_cert_hints then
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
                    (sprintf " Looking at trans %i (cert ID: %s): %i (%A) -> %i (%A)"
                        transIdx
                        (string (getTransitionId exportInfo.transDuplIdToTransId transIdx))
                        sourceLoc (exportInfo.progCoopInstrumented.GetLocationLabel sourceLoc)
                        targetLoc (exportInfo.progCoopInstrumented.GetLocationLabel targetLoc))
                Log.debug exportInfo.parameters (sprintf "   Transition formula: %s" (String.concat " && " (List.map (fun (f : Formula.formula) -> f.pp) transFormula)))
                Log.debug exportInfo.parameters (sprintf "   Transition formula term: %s" (String.concat ", " (List.map (fun (t : SparseLinear.LinearTerm) -> sprintf "%s <= 0" (SparseLinear.linearTermToString t)) transLinearTerms)))
                Log.debug exportInfo.parameters (sprintf "   RF on source: (%s)" (String.concat ", " (List.map string sourceRFTerms)))
                Log.debug exportInfo.parameters (sprintf "   Bounds: (%s)" (String.concat ", " (List.map string bounds)))
                Log.debug exportInfo.parameters (sprintf "   RF on target: (%s)" (String.concat ", " (List.map string targetRFTerms)))

            let mutable isStrictlyDecreasing = true
            let mutable weakDecreaseHints = []
            let mutable isDecreasingAt = []
            let mutable strictDecreaseHints = []
            let mutable boundedHints = []
            for sourceLocInvariant in locToInvariant.GetWithDefault sourceLoc [[Formula.truec]] do
                Log.debug exportInfo.parameters (sprintf "  Invariant disjunct on source: %s" (String.concat " && " (List.map string sourceLocInvariant)))
                let sourceLocInvariantLinearTerms =
                    Formula.formula.FormulasToLinearTerms (sourceLocInvariant :> _)
                    |> Formula.filter_instr_vars shouldExportVariable
                    |> List.map (SparseLinear.alpha varToPre)

                let mutable disjunctIsStrictlyDecreasingAt = None
                let mutable disjunctIsBoundedHints = None
                let mutable disjunctIsStrictlyDecreasingHints = None
                let mutable disjunctIsWeaklyDecreasingHints = []
                for (rfIndex, (sourceRFTerm, sourceBound, targetRFTerm)) in List.mapi (fun idx rf -> idx + 1, rf) (List.zip3 rankFunctionsOnPreVars bounds rankFunctionsOnPostVars) do
                    Log.debug exportInfo.parameters (sprintf "   Checking component %i of rank function." rfIndex)

                    //Once we've ensured that something is strictly decreasing, we can stop:
                    if disjunctIsStrictlyDecreasingHints = None then
                        let weakDecreaseLinearTerm = List.head <| (Formula.Ge(sourceRFTerm, targetRFTerm)).ToLinearTerms()
                        let strictDecreaseLinearTerm = List.head <| (Formula.Gt(sourceRFTerm, targetRFTerm)).ToLinearTerms()
                        let boundedLinearTerm = List.head <| (Formula.Ge(sourceRFTerm, Term.Const sourceBound)).ToLinearTerms() 
                       
                        if Formula.unsat (Formula.conj sourceLocInvariant) then
                            Log.debug exportInfo.parameters (sprintf "    Source invariant UNSAT and transition thus trivially marked as strictly decreasing for this disjunct.")
                            disjunctIsBoundedHints <- Some [] //Empty will be interpreted as <auto />
                            disjunctIsStrictlyDecreasingHints <- Some [] //Empty will be interpreted as <auto />
                            disjunctIsWeaklyDecreasingHints <- [] :: disjunctIsWeaklyDecreasingHints //Empty will be interpreted as <auto />
                        else
                            let locInvariantAndTransLinearTerms = List.append sourceLocInvariantLinearTerms transLinearTerms
                            
                            let isStrictlyDecreasing =
                                match SparseLinear.tryGetFarkasCoefficients locInvariantAndTransLinearTerms strictDecreaseLinearTerm with
                                | Some strictDecreaseHints ->
                                    match SparseLinear.tryGetFarkasCoefficients locInvariantAndTransLinearTerms boundedLinearTerm with
                                    | Some boundedHints ->
                                        Log.debug exportInfo.parameters (sprintf "    Strict decrease for this disjunct at component %i of rank function." rfIndex)
                                        disjunctIsStrictlyDecreasingHints <- Some strictDecreaseHints
                                        disjunctIsBoundedHints <- Some boundedHints
                                        disjunctIsWeaklyDecreasingHints <- strictDecreaseHints :: disjunctIsWeaklyDecreasingHints
                                        disjunctIsStrictlyDecreasingAt <- Some rfIndex
                                        true
                                    | None ->
                                        false
                                | None ->
                                    false

                            if not isStrictlyDecreasing then
                                match SparseLinear.tryGetFarkasCoefficients locInvariantAndTransLinearTerms weakDecreaseLinearTerm with
                                | Some weakDecreaseHints ->
                                    Log.debug exportInfo.parameters (sprintf "    Weak decrease for this disjunct at component %i of rank function." rfIndex)
                                    disjunctIsWeaklyDecreasingHints <- weakDecreaseHints :: disjunctIsWeaklyDecreasingHints
                                | None ->
                                    raise <| System.ArgumentException "Provided rank functions do not decrease weakly on transition."

                match disjunctIsStrictlyDecreasingHints with
                | Some disjunctIsStrictlyDecreasingHints ->
                    isDecreasingAt <- disjunctIsStrictlyDecreasingAt.Value :: isDecreasingAt
                    strictDecreaseHints <- disjunctIsStrictlyDecreasingHints :: strictDecreaseHints
                    boundedHints <- disjunctIsBoundedHints.Value :: boundedHints
                    weakDecreaseHints <- disjunctIsWeaklyDecreasingHints :: weakDecreaseHints
                | None ->
                    isDecreasingAt <- System.Int32.MaxValue :: isDecreasingAt
                    strictDecreaseHints <- [] :: strictDecreaseHints
                    boundedHints <- [] :: boundedHints
                    weakDecreaseHints <- disjunctIsWeaklyDecreasingHints :: weakDecreaseHints
                    isStrictlyDecreasing <- false

            if isStrictlyDecreasing then
                strictlyDecreasingTransitions <- Set.add transIdx strictlyDecreasingTransitions
                Log.debug exportInfo.parameters "  Is strictly decreasing and bounded."
            else
                Log.debug exportInfo.parameters "  Is weakly decreasing."

            transitionToHints <- Map.add transIdx (List.rev (List.zip4 weakDecreaseHints boundedHints strictDecreaseHints isDecreasingAt)) transitionToHints
                 
        if not (Set.isSubset transitionsToRemove strictlyDecreasingTransitions) then
            raise (System.ArgumentException
                    (sprintf
                        "Cannot prove transitions to remove as strictly decreasing (to remove: [%s]; proven to decrease: [%s])"
                        (String.concat ", " (Seq.map string transitionsToRemove)) 
                        (String.concat ", " (Seq.map string strictlyDecreasingTransitions))))
    let newRemovedTransitions = Set.union removedTransitions transitionsToRemove

    (** Step 2: Write out the actual XML. *)
    if Set.isEmpty transitionsToRemove then
        Log.log exportInfo.parameters " Skipping transition removal step because no transition was strictly decreasing."
        nextProofStep newRemovedTransitions xmlWriter
    else
        Log.log
            exportInfo.parameters
            (sprintf
                " Removing transitions [%s] (internally known as [%s])."
                (String.concat ", " (Seq.map (fun t -> string (getTransitionId exportInfo.transDuplIdToTransId t)) transitionsToRemove))
                (String.concat ", " (Seq.map string transitionsToRemove)))
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
        for transIdx in transitionsToRemove do
            writeTransitionId exportInfo.transDuplIdToTransId xmlWriter transIdx
        xmlWriter.WriteEndElement () //end remove

        if exportInfo.parameters.export_cert_hints then
            xmlWriter.WriteStartElement "hints"

            let writeImplicationHint linearCombinationHint =
                match linearCombinationHint with
                | [] -> xmlWriter.WriteElementString ("auto", "")
                | _  -> SparseLinear.writeCPFLinearCombinationHint xmlWriter linearCombinationHint

            for (transIdx, _) in transitionsToExport do
                let disjunctiveHints = transitionToHints.[transIdx]
                xmlWriter.WriteStartElement "hint"
                writeTransitionId exportInfo.transDuplIdToTransId xmlWriter transIdx
                let isDisjunction = List.length disjunctiveHints > 1

                if isDisjunction then
                    xmlWriter.WriteStartElement "distribute"
                    xmlWriter.WriteElementString ("assertion", "")

                for (weakHints, boundedHint, strictHint, isDecreasingAt) in disjunctiveHints do
                    if Set.contains transIdx transitionsToRemove then
                        xmlWriter.WriteStartElement "lexStrict"
                        weakHints |> List.rev |> List.take (isDecreasingAt - 1) |> List.iter writeImplicationHint
                        writeImplicationHint strictHint
                        writeImplicationHint boundedHint
                        xmlWriter.WriteEndElement () //end lexStrict
                    else
                        xmlWriter.WriteStartElement "lexWeak"
                        weakHints |> List.rev |> List.iter writeImplicationHint
                        xmlWriter.WriteEndElement () //end lexWeak
                if isDisjunction then
                    xmlWriter.WriteEndElement () //end distribute
                xmlWriter.WriteEndElement () //end hint
            xmlWriter.WriteEndElement () //end hints

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

    let aiInvariantsNonTrivial =
        match exportInfo.locToAIInvariant with 
        | Some locToAIInvariant ->
            locToAIInvariant.Values
            |> Seq.exists (fun absDomElement -> absDomElement.to_formula() <> Formula.formula.True)
        | _ -> false

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
            let cmds =
                match exportInfo.locToAIInvariant with  
                | Some locToAIInvariant when aiInvariantsNonTrivial ->
                    (Programs.assume (locToAIInvariant.[sourceLoc].to_formula())) :: cmds
                | _ -> cmds
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
        (Set.ofSeq progFullExtraTrans)
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

        let shouldExportLocation loc =
            match exportInfo.progCoopInstrumented.GetLocationLabel loc with
            | OriginalLocation _ -> true
            | _ -> false
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
                for (transIdx, (_, _, childLoc)) in exportInfo.progCoopInstrumented.TransitionsFrom loc do
                    if shouldExportTransition transIdx loc childLoc then
                        xmlWriter.WriteStartElement "child"
                        writeTransitionId exportInfo.transDuplIdToTransId xmlWriter transIdx
                        xmlWriter.WriteElementString ("nodeId", string childLoc)
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
        | (locToRF, transToBounds, transToRemove) :: remainingRankFunctions ->
            Log.log exportInfo.parameters "Exporting transitionRemoval proof step based on lexicographic rank functions synthesised without safety loop."
            //Extract the actual per-location rank functions and overall bound:
            let shouldExportTransition = shouldExportTransition exportInfo.progCoopInstrumented shouldExportLocation None removedTransitions
            let bound = [transToBounds |> Map.toSeq |> Seq.map snd |> Seq.fold min (bigint System.Int32.MaxValue)]
            let locToRFTerm = Dictionary()
            for loc in scc do
                if shouldExportLocation loc then
                    let locRF = defaultArg (locToRF.TryFind loc) Map.empty
                    let rfTerm = SparseLinear.linear_term_to_term locRF
                    locToRFTerm.[loc] <- [Term.subst (Var.unprime_var >> Formula.eval_const_var) rfTerm]

            let transToExport =
                exportInfo.progCoopInstrumented.TransitionsWithIdx
                |> Seq.filter (fun (transIdx, (source, _, target)) -> shouldExportTransition transIdx source target)
            let transToRemove = Set.intersect (transToExport |> Seq.map fst |> Set.ofSeq) transToRemove

            exportTransitionRemovalProof exportInfo (Dictionary()) locToRFTerm bound transToExport transToRemove Formula.is_noninstr_var removedTransitions (exportNextRF remainingRankFunctions) xmlWriter
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
    for loc in scc do
        graphEdges.Add(entryLoc, (0, (entryLoc, 0, loc)))
    SCC.find_sccs graphEdges entryLoc returnTrivialComponents

let private exportFinalProof
        (exportInfo: CertificateExportInformation)
        (exportedInvariants: bool)
        (scc : ProgramSCC)
        ((cp, cpDupl) : (ProgramLocation * ProgramLocation))
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
    let locToInvariants =
        match getImpactInvariantsForLocs exportInfo scc removedTransitions cp with
        | None -> Dictionary()
        | Some invariants -> invariants
    let infeasibleTransitions =
        exportInfo.progCoopInstrumented.TransitionsWithIdx
        |> Seq.filter (fun (transIdx, (source, _, target)) ->
            shouldExportTransition transIdx source target &&
                (match locToInvariants.TryGetValue source with
                | (true, locInv) -> locInv = [[Formula.formula.False]]
                | _ -> false))
        |> Seq.map fst
        |> Set.ofSeq

    Log.debug exportInfo.parameters (sprintf " Transitions [%s] are disabled because their source locations have invariant FALSE" (String.concat ", " (Seq.map string infeasibleTransitions)))

    let entryLoc =
        scc
        |> Seq.tryFind
             (fun loc ->
                if shouldExportLocation loc then
                    let inDeg =
                        exportInfo.progCoopInstrumented.TransitionsTo loc
                        |> Seq.filter (fun (transIdx, (source, _, target)) -> shouldExportTransition transIdx source target && (not <| Set.contains transIdx infeasibleTransitions))
                        |> Seq.length
                    inDeg = 0
                else
                    false)

    let (locToRFTerms, bounds) =
        match entryLoc with
        | Some entryLoc ->
            let locToRFTerm = Dictionary()
            let sccs = findSCCsInTransitions exportInfo scc (Set.union removedTransitions infeasibleTransitions) entryLoc true
            sccs
            |> List.iteri
                (fun idx scc ->
                    scc |> Seq.filter shouldExportLocation |> Seq.iter (fun loc -> locToRFTerm.[loc] <- [Term.constant (-idx - 1)]))
            (locToRFTerm, [bigint (-(List.length sccs) - 1)])
        | None ->
            let locToRFTerm = Dictionary()
            for loc in scc do
                if shouldExportLocation loc then
                    locToRFTerm.[loc] <- [Term.constant -1]
            locToRFTerm.[exportInfo.progCoopInstrumented.GetLabelledLocation (CutpointDummyEntryLocation (string cp))] <- [Term.constant 1]
            locToRFTerm.[exportInfo.progCoopInstrumented.GetLabelledLocation (DuplicatedCutpointLocation (string cp))] <- [Term.constant 0]
            (locToRFTerm, [bigint.Zero])

    let exportTrivialProof _ _ =
        xmlWriter.WriteStartElement "cutTransitionSplit"
        xmlWriter.WriteEndElement () //end cutTransitionSplit

    let transToExport =
        exportInfo.progCoopInstrumented.TransitionsWithIdx
        |> Seq.filter (fun (transIdx, (source, _, target)) -> shouldExportTransition transIdx source target)
    let transToRemove = transToExport |> Seq.filter (fun (_, (source, _, _)) -> source = cpDupl) |> Seq.map fst |> Set.ofSeq
    exportTransitionRemovalProof exportInfo locToInvariants locToRFTerms bounds transToExport transToRemove shouldExportVariable removedTransitions exportTrivialProof xmlWriter

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

    let afterCutpointTransitionId = getAfterTransitionId exportInfo cpDupl
    let shouldExportLocation = shouldExportLocation exportInfo.progCoopInstrumented scc false
    let shouldExportTransition = shouldExportTransition exportInfo.progCoopInstrumented shouldExportLocation (Some cp) removedTransitions

    for variable in exportInfo.progOrig.Variables |> List.ofSeq |> List.rev do
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
                xmlWriter.WriteStartElement "conjunction"
                xmlWriter.WriteStartElement "leq"
                if transIdx = afterCutpointTransitionId then
                    xmlWriter.WriteStartElement "post"
                    xmlWriter.WriteElementString ("variableId", snaphottedVar)
                    xmlWriter.WriteEndElement() //end post
                    xmlWriter.WriteStartElement "post"
                    xmlWriter.WriteElementString ("variableId", variable)
                    xmlWriter.WriteEndElement() //end post
                else
                    xmlWriter.WriteStartElement "post"
                    xmlWriter.WriteElementString ("variableId", snaphottedVar)
                    xmlWriter.WriteEndElement() //end post
                    xmlWriter.WriteElementString ("variableId", snaphottedVar)
                xmlWriter.WriteEndElement() //end leq
                xmlWriter.WriteStartElement "leq"
                if transIdx = afterCutpointTransitionId then
                    xmlWriter.WriteStartElement "post"
                    xmlWriter.WriteElementString ("variableId", variable)
                    xmlWriter.WriteEndElement() //end post
                    xmlWriter.WriteStartElement "post"
                    xmlWriter.WriteElementString ("variableId", snaphottedVar)
                    xmlWriter.WriteEndElement() //end post
                else
                    xmlWriter.WriteElementString ("variableId", snaphottedVar)
                    xmlWriter.WriteStartElement "post"
                    xmlWriter.WriteElementString ("variableId", snaphottedVar)
                    xmlWriter.WriteEndElement() //end post
                xmlWriter.WriteEndElement() //end leq
                xmlWriter.WriteEndElement() //end conjunction
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
    let shouldExportVariable =shouldExportVariable cp

    let locToOldInvariantTerms =
        let isNonTrivial (locToAIInvariant : Dictionary<ProgramLocation, IIntAbsDom.IIntAbsDom>) =
            locToAIInvariant.Values
            |> Seq.exists (fun absDomElement -> absDomElement.to_formula() <> Formula.formula.True)
        match exportInfo.locToAIInvariant with
        | Some locToAIInvariant when isNonTrivial locToAIInvariant ->
            fun loc ->
                let origLoc = locToOriginalLocation exportInfo.progCoopInstrumented loc
                locToAIInvariant.[origLoc].to_formula().ToLinearTerms()
        | _ ->
            fun _ -> []

    match getImpactInvariantsForLocs exportInfo scc removedTransitions cp with
    | None ->
        nextProofStep scc removedTransitions (cp, cpDupl) xmlWriter
    | Some locToInvariants ->
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
            let oldInvariantTerms = locToOldInvariantTerms loc
            for locInvariant in locInvariants do
                Formula.linear_terms_to_ceta xmlWriter Var.plainToCeta ((Formula.formula.FormulasToLinearTerms (locInvariant :> _)) @ oldInvariantTerms) shouldExportVariable
            xmlWriter.WriteEndElement () //end disjunction
            xmlWriter.WriteEndElement () //end formula
            xmlWriter.WriteEndElement () //end invariant

        xmlWriter.WriteEndElement () //end invariants

        let shouldExportVariable locLabel =
            match locLabel with
            | OriginalLocation _ -> Formula.is_noninstr_var
            | _ -> shouldExportVariable
            
        exportInfo.impactArg.ToCeta xmlWriter (writeTransitionId exportInfo.transDuplIdToTransId) locToOldInvariantTerms shouldExportLocation shouldExportTransition shouldExportVariable (Some cpDupl)
        
        nextProofStep scc removedTransitions (cp, cpDupl) xmlWriter

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

        let locToInvariants =
            match getImpactInvariantsForLocs exportInfo scc removedTransitions cp with
            | None -> Dictionary()
            | Some locToInvariants -> locToInvariants
        let transToRemove = transToExport |> Seq.filter (fun (_, (_, _, target)) -> target = cpDupl) |> Seq.map fst |> Set.ofSeq
        exportTransitionRemovalProof exportInfo locToInvariants locToRFTerm rfBound transToExport transToRemove shouldExportVariable removedTransitions (nextProofStep scc (cp, cpDupl)) xmlWriter

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

let private exportSafetyTerminationProof exportInfo scc removedTransitions (cp, cpDupl) =
    match exportInfo.foundLexRankFunctions.TryFind cp with
    | Some (_ :: _) ->
        exportCopyVariableAdditionProof exportInfo (
         exportNewImpactInvariantsProof exportInfo (
          exportSafetyTransitionRemovalProof exportInfo (
           exportFinalProof exportInfo true))) scc removedTransitions (cp, cpDupl)
    | _ ->
        let locToInvariants =
            match getImpactInvariantsForLocs exportInfo scc removedTransitions cp with
            | None -> Dictionary()
            | Some locToInvariants -> locToInvariants
        let hasDisabledLocation = locToInvariants.Values |> Seq.exists ((=) [[Formula.formula.False]])
        let hasRemainingIncomingCPEdge =
            let cpEntryLoc = exportInfo.progCoopInstrumented.GetLabelledLocation (CutpointDummyEntryLocation (string cp))
            let cpEntryTrans = exportInfo.progCoopInstrumented.TransitionsFrom cpEntryLoc |> List.head |> fst
            not <| Set.contains cpEntryTrans removedTransitions
        if hasDisabledLocation && hasRemainingIncomingCPEdge then
            exportNewImpactInvariantsProof exportInfo (
             fun scc removed cp -> exportFinalProof exportInfo true scc cp removed)
              scc removedTransitions (cp, cpDupl)
        else
            exportFinalProof exportInfo false scc (cp, cpDupl) removedTransitions

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
            impactInvariants = Map.empty
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
    |> exportAIInvariantsProof exportInfo (
        exportSwitchToCooperationTerminationProof exportInfo (
         exportSccDecompositionProof exportInfo (
          exportInitialLexRFTransRemovalProof exportInfo (
           exportCutTransitionSplitProof exportInfo (
            exportSafetyTerminationProof exportInfo)))))
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
