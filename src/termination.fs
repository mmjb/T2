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

/// Tries to remove as many transitions as possible from a SCC. Returns a list of used rank functions/bounds.
let simplify_scc (pars : Parameters.parameters) p termination_only (cp_rf: System.Collections.Generic.Dictionary<int, int>) (all_cutpoints: Set<int>) cp scc_nodes =
    let (scc_vars, scc_trans, scc_rels) = Symex.get_scc_rels_for_lex_rf_synth_from_program pars p scc_nodes cp
    let cleaned_scc_rels = ref scc_rels

    if pars.print_debug then
        Log.debug pars <| sprintf "CP %A has scc nodes %A, vars %A" cp scc_nodes scc_vars
        Log.debug pars <| sprintf "SCC transitions: "
        Log.debug pars <| (scc_trans |> Seq.map (fun t -> sprintf "  %A" t) |> String.concat "\n")

    match Rankfunction.synth_maximal_lex_rf pars scc_rels (Rankfunction.get_simplified_linterm_cache scc_rels) with
    | None -> None
    | Some (rfs, trans_to_remove') ->
        let trans_to_remove = Seq.concat trans_to_remove' |> Set.ofSeq
        for trans_idx in trans_to_remove do
            if pars.print_debug then
                let (k,_,k') = p.transitions.[trans_idx]
                Log.debug pars <| sprintf "Removing trans %i->%i" k k'
            let scc_trans_num = Seq.concat (scc_trans |> Set.map(fun (x,y) -> x )) |> Set.ofSeq
            if (termination_only || (Set.isEmpty (Set.difference scc_trans_num trans_to_remove))) && pars.lex_term_proof_first then
                Programs.remove_transition p trans_idx
                cleaned_scc_rels := Set.filter (fun (i, _, _, _) -> not <| Set.contains i trans_to_remove') !cleaned_scc_rels
        if (!cleaned_scc_rels).IsEmpty then
            for terminating_cp in (Seq.filter (fun c -> Set.contains c scc_nodes) all_cutpoints) do
                let cp_checker_trans = cp_rf.[terminating_cp]
                Programs.remove_transition p cp_checker_trans
        Some (rfs, trans_to_remove)

let do_interval_AI_on_program (pars : Parameters.parameters) (p:Programs.Program) =
    let pp_to_interval =
        Analysis.program_absint
            !p.initial
            (match pars.ai_domain with | Parameters.Box -> IntervalIntDom.Intervals.create :> IIntAbsDom.IIntAbsDom
                                       | Parameters.Octagon -> Octagon2.Oct.create :> IIntAbsDom.IIntAbsDom)
            (p.transitions |> Seq.map (fun (k,c,k') -> (k, (k,c,k'))))
            id

    (* //This computes variables used in SCCs and can be used to guide the invariant generation.
    let node_to_scc_nodes =
            p_sccs.Items
        |> Seq.map (fun (_, scc_nodes) -> scc_nodes |> Seq.map (fun n -> (n, scc_nodes)))
        |> Seq.concat
        |> Map.ofSeq

    let scc_to_scc_trans = ref Map.empty
    for n in !p.active do
        let (k,c,k') = p.transitions.[n]
        if node_to_scc_nodes.ContainsKey k then
            let k_scc = node_to_scc_nodes.[k]
            if Set.contains k' k_scc then
                let scc_trans =
                    if Map.containsKey k_scc !scc_to_scc_trans then
                        (!scc_to_scc_trans).[k_scc]
                    else
                        let n = new System.Collections.Generic.HashSet<int * Programs.command list * int>()
                        scc_to_scc_trans := Map.add k_scc n !scc_to_scc_trans
                        n
                scc_trans.Add(k,c,k') |> ignore

    let scc_to_scc_vars = !scc_to_scc_trans |> Map.map (fun _ ts -> [ for (_,c,_) in ts do yield c ] |> Seq.concat |> Programs.freevars)
    *)
    if pars.do_ai_threshold > (!p.active).Count then
        for n in !p.active do
            let (k,c,k') = p.transitions.[n]
            if pp_to_interval.ContainsKey k then
                //if(node_to_scc_nodes.ContainsKey k then
                    //let used_vars = scc_to_scc_vars.[node_to_scc_nodes.[k]]
                    let used_vars = Programs.freevars c
                    let inv = pp_to_interval.[k].to_formula_filtered (fun v -> used_vars.Contains v)
                    p.transitions.[n] <- (k,(Programs.assume inv)::c,k')

let output_term_proof scc_simplification_rfs found_lex_rfs found_disj_rfs (outWriter : System.IO.TextWriter) =
    //Print out initial rank functions that we used to remove transitions before safety proofs:
    if not(List.isEmpty scc_simplification_rfs) then
        let print_one_simplification (rfs, removed_transitions) =
            outWriter.WriteLine(" * Removed transitions {0} using the following rank functions:", (removed_transitions |> Seq.map string |> String.concat ", "))
            let print_one_scc_rf i (rf, bnds) =
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

                outWriter.WriteLine("    - Rank function {0:D}:", (i + 1))
                rf |> Map.toSeq |> Seq.iter print_rf_per_loc
                bnds |> Map.toSeq |> Seq.iter print_bound_per_transs
            List.iteri print_one_scc_rf rfs
            ()
        outWriter.WriteLine("Initially, performed program simplifications using lexicographic rank functions:")
        List.iter print_one_simplification scc_simplification_rfs


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

let output_nonterm_proof ((cp, recurrent_set) : int * Formula.formula) (outWriter : System.IO.TextWriter) =
    outWriter.WriteLine("Found this recurrent set for cutpoint {0:D}: {1}", cp, recurrent_set.pp)

let output_cex (cex : Counterexample.cex) existential (outWriter : System.IO.TextWriter) =
    if existential then
        outWriter.WriteLine("Found existential witness:")
    else
        outWriter.WriteLine("Found counterexample:")
    cex.ToString outWriter

let output_nocex existential (outWriter : System.IO.TextWriter) =
    if existential then
        outWriter.WriteLine("No existential witness found, property false!")
    else
        outWriter.WriteLine("Property true!")

//Generating precondition using Fourier-Motzkin
let findPreconditionForPath (cex : (int * Programs.command * int) list) =
    //Instantiate constants:
    let cex = cex |> List.map (fun (x, y, z) -> (x, [Programs.const_subst y], z))

    //Fourier-Motzkin elimination done here, removing all non-pre-variables:
    let (cex, var_map) = Symex.path_to_transitions_and_var_map cex Map.empty
    let cex = Symex.project_transitions_to_formulae cex |> List.filter (fun f -> not(Formula.contains_instr_var f)) |> Formula.conj
    let ts = ref (cex |> SparseLinear.formula_to_linear_terms)

    for (var, var_index) in var_map.Items do
        for i in 1..var_index do
            let var_prime = (Var.prime_var var i)
            ts := SparseLinear.eliminate_var var_prime !ts
            ts := SparseLinear.simplify_as_inequalities !ts

    let precondition = List.map SparseLinear.linear_term_to_formula !ts |> Formula.conj
    //This formula has an SSA tag, must strip off before returning
    let strip_ssa f = Formula.subst (fun v -> Term.var (Var.unprime_var v)) f
    let precondition = Formula.negate (strip_ssa precondition)
    //If disjunction, we also must split in order to properly instrument in graph.
    (precondition, Formula.polyhedra_dnf precondition |> Formula.split_disjunction)

//Now we must either universally or existentially quantify out the prophecy variables
//from the preconditions.
//For each location, apply quantifier elimination.
let quantify_proph_var (e : CTL.CTL_Formula) F formulaMap =
    let propertyMap_temp = SetDictionary<CTL.CTL_Formula, (int*Formula.formula)>()
    for n in formulaMap do
        let (loc,loc_form) = n
        let loc_form = if e.IsExistential then loc_form else Formula.negate(loc_form)
        let proph_var = loc_form |> Formula.freevars |> Set.filter (fun x -> Formula.is_fair_var x)//x.Contains proph_string __proph_var_det")
        if not(Set.isEmpty proph_var) then
            let disj_fmla = ref Set.empty
            let split_disj = Formula.split_disjunction (Formula.polyhedra_dnf loc_form)
            //When doing QE for universal versus existential
            //\forall X.phi(X) === \neg \exists \neg phi(X)
            for var in split_disj do
                let ts = ref (var |> SparseLinear.formula_to_linear_terms)
                for var in proph_var do
                        ts := SparseLinear.eliminate_var var !ts
                        ts := SparseLinear.simplify_as_inequalities !ts
                disj_fmla := Set.add (List.map SparseLinear.linear_term_to_formula !ts |> Formula.conj) !disj_fmla
            //printfn "Before %A" disj_fmla
            //disj_fmla := Set.remove (Formula.Le(Term.Const(bigint.Zero),Term.Const(bigint.Zero))) !disj_fmla
            //printfn "After %A" disj_fmla
            let strength_f = if e.IsExistential then Formula.disj !disj_fmla else Formula.negate(Formula.disj !disj_fmla)
            propertyMap_temp.Add(F,(loc,strength_f))
        else
            propertyMap_temp.Add(F,n)

    propertyMap_temp

let findCP (p_loops : Map<int, Set<int>>) (all_cutpoints : Set<int>) (copy_pair : Map<int, int>) pi =
    let cutp = ref -1
    let pi_rev = ref (List.rev pi)
    let loops = Set.ofSeq p_loops.Keys
    while !cutp = -1 && !pi_rev <> [] do
        let (z,_,_) = (!pi_rev).Head
        if (Set.contains z all_cutpoints || Set.contains z loops) && !cutp = -1 then
            if Set.contains z all_cutpoints then
                cutp := z
            else
                if copy_pair.ContainsKey z then
                    cutp := copy_pair.[z]
                else
                    cutp := z
            pi_rev := []
        else
            pi_rev := (!pi_rev).Tail
    let pi_mod = ref pi
    let copy = ref true
    while !pi_mod <> [] && !copy do
        let (x,y,z) = (!pi_mod).Head
        if z = !cutp then
            pi_mod := (x,y,z)::!pi_mod
            copy := false
        else
            pi_mod := (!pi_mod).Tail
    (!cutp, !pi_mod)

let isorigNodeNum x p_BU =
    match Programs.findLabel p_BU x with
    | Some(nodeLabel) -> if nodeLabel.Contains "loc_" then true
                                 else false
    | None -> false

///Takes a loc->formula list as second arg, groups the formulas by loc and connects them using the first argument
let fold_by_loc collector (formulas : Set<int * Formula.formula>) =
    let preCond_map = new System.Collections.Generic.Dictionary<int, Formula.formula>()
    for (x, y) in formulas do
        if preCond_map.ContainsKey x then
            preCond_map.[x] <- collector (preCond_map.[x], y)
        else
            preCond_map.Add (x,y)
    preCond_map

let findErrorNode p pi =
    let errorNode = ref -1
    let endOfPropertyCheckNode = ref -1

    let pi_rev = ref (List.rev pi)
    while !errorNode = -1 && !pi_rev <> [] do
        let (x,_,z) = (!pi_rev).Head

        match Programs.findLabel p z with
        | Some nodeLabel when nodeLabel.Contains "start_of_subproperty_node" ->
            errorNode := x
        | _ -> ()

        match Programs.findLabel p z with
        | Some nodeLabel when nodeLabel.Contains "end_of_subproperty_node" ->
            endOfPropertyCheckNode := z
        | _ -> ()

        pi_rev := (!pi_rev).Tail

    assert(!errorNode <> -1)
    assert(!endOfPropertyCheckNode <> -1)
    (!errorNode, !endOfPropertyCheckNode)

let strengthenCond pi_mod p1 =
    let mod_var =
        pi_mod
        |> List.choose
            (fun (_, cmd, _) ->
                match cmd with
                | Programs.Assign(_, v, _) -> Some(v)
                | _ -> None)
    let disj_fmla = ref Set.empty
    let split_disj = Formula.split_disjunction (Formula.polyhedra_dnf p1)

    for var in split_disj do
        let ts = ref (var |> SparseLinear.formula_to_linear_terms)
        for var in mod_var do
                ts := SparseLinear.eliminate_var var !ts
                ts := SparseLinear.simplify_as_inequalities !ts
        disj_fmla := Set.add (List.map SparseLinear.linear_term_to_formula !ts |> Formula.conj) !disj_fmla
    disj_fmla := Set.remove Formula.truec !disj_fmla
    disj_fmla


let propagateToTransitions (p_orig : Programs.Program) (p_orig_loops : Map<int, Set<int>>) f pi_mod cutp existential (loc_to_loopduploc : Map<int,int>) (visited_BU_cp : Map<int, int*int> ref) (cps_checked_for_term : Set<int>) (loopnode_to_copiednode : System.Collections.Generic.Dictionary<int,int>) propDir strengthen=
    let preStrengthSet = ref Set.empty
    let propertyMap = new SetDictionary<CTL.CTL_Formula, int * Formula.formula>()
    let elim_node = ref !p_orig.initial
    let pi_wp = ref pi_mod
    while !pi_wp <> [] do
        let (x,_,z) = (!pi_wp).Head
        let x = if propDir then x else z
        if (x <> !elim_node) && (x <> cutp) && not(loopnode_to_copiednode.ContainsKey cutp && loopnode_to_copiednode.[cutp] = x) then
            elim_node := x
            //We do not want to find a condition for the non-copy of a cp, only the copy cp
            let(tempfPreCond, _) = findPreconditionForPath !pi_wp
            //Propagate to all cutpoints, not just loops.
            if p_orig_loops.ContainsKey x || Set.contains x cps_checked_for_term || Set.contains x !p_orig.locs && isorigNodeNum x p_orig || loopnode_to_copiednode.ContainsValue x then
                let visited = loc_to_loopduploc.FindWithDefault x x
                if not((!visited_BU_cp).ContainsKey visited) then
                    let orig =  
                        if loopnode_to_copiednode.ContainsValue x then
                            let orig_node = loopnode_to_copiednode |> Seq.find(fun y -> y.Value = x)
                            orig_node.Key
                        else if p_orig_loops.ContainsKey x then x
                        else if (!p_orig.locs).Contains x then x
                        else loc_to_loopduploc |> Map.findKey(fun _ value -> value = x)

                    let truefPreCond = if existential then
                                            Formula.negate(tempfPreCond)
                                       else tempfPreCond

                    if strengthen then
                        let preStrengthf = (orig, truefPreCond)
                        preStrengthSet := Set.add preStrengthf !preStrengthSet
                    else
                        propertyMap.Add(f,(orig,truefPreCond))

        pi_wp := (!pi_wp).Tail
    (propertyMap, preStrengthSet)

let propagate_func (p_orig : Programs.Program) (p_orig_loops : Map<int, Set<int>>) (p_orig_sccs : Map<int, Set<int>>) f recur pi pi_mod cutp existential (loc_to_loopduploc : Map<int,int>) (visited_BU_cp : Map<int, int*int> ref) (cps_checked_for_term : Set<int>) loopnode_to_copiednode strengthen=
    let recurs, r =
        match recur with
        | Some x -> (x, true)
        | None -> (Formula.falsec, false)
    //First propagate preconditions to sccs contained within the loop
    let (propertyMap, preStrengthSet) = propagateToTransitions p_orig p_orig_loops f pi_mod cutp existential loc_to_loopduploc visited_BU_cp cps_checked_for_term loopnode_to_copiednode false strengthen
    //Second, propagate upwards to non-cp nodes that are not part of any SCCS.
    let sccs_vals = p_orig_sccs |> Map.filter(fun x y -> x <> cutp) |> Map.toSeq |> Seq.map snd |> Seq.fold (fun acc elem -> Seq.append elem acc) Seq.empty |> Set.ofSeq
    if sccs_vals.Contains cutp || r then
        let cp_reached = ref false
        let found_cp = ref false
        let node = cutp
        let pi_rev = ref (List.rev pi)
        let pi_elim = ref []
        while not(!cp_reached) && !pi_rev <> [] do
            let (_,_,x) = (!pi_rev).Head
            if (x = cutp || not(Map.isEmpty (loc_to_loopduploc |> Map.filter(fun y value -> value = x && y = cutp)))) && not(!found_cp) then
                pi_elim := List.append [(!pi_rev).Head] !pi_elim
                pi_rev := (!pi_rev).Tail
                found_cp := true
            else if !found_cp then
                if p_orig_loops.ContainsKey x || Set.contains x cps_checked_for_term || Set.contains x !p_orig.locs then
                    let visited = loc_to_loopduploc.FindWithDefault x x
                    if not((!visited_BU_cp).ContainsKey visited) then
                        if x = !p_orig.initial || p_orig_loops.ContainsKey x || not(Map.isEmpty (loc_to_loopduploc |> Map.filter(fun _ value -> value = x)))then
                            cp_reached := true
                pi_elim := List.append [(!pi_rev).Head] !pi_elim
                pi_rev := (!pi_rev).Tail
            else
                pi_rev := (!pi_rev).Tail

        if r then
            pi_elim := (!pi_elim)@[(node,Programs.assume(recurs),-1)]

        propertyMap.Union(propagateToTransitions p_orig p_orig_loops f !pi_elim cutp existential loc_to_loopduploc visited_BU_cp cps_checked_for_term loopnode_to_copiednode true strengthen|> fst)
    let is_dup x = loc_to_loopduploc |> Map.filter(fun _ value -> value = x) |> Map.isEmpty |> not
    let cex_path = pi |> List.map(fun (x,_,_) -> x) |> List.filter(fun x -> Set.contains x !p_orig.locs || loopnode_to_copiednode.ContainsValue x || is_dup x)
    let cex_path = cex_path |> List.map(fun x -> if loopnode_to_copiednode.ContainsValue x then
                                                    let orig_node = loopnode_to_copiednode |> Seq.find(fun y -> y.Value = x)
                                                    orig_node.Key
                                                 else if (!p_orig.locs).Contains x then x
                                                 else loc_to_loopduploc |> Map.findKey(fun _ value -> value = x) )
    (Set.ofList cex_path, propertyMap, preStrengthSet)

/// Prepare the program for another prover run, slowly enumerating all different pre-conditions
/// (which are either conjunctive/disjunctive, depending on whether we are doing universal/existential)
//Note: If a certain PC does not have a pre-condition, it means that there was no CEX, thus it's true.
let insertForRerun
    (pars : Parameters.parameters)
    (recurSet : (int * Formula.formula) option)
    (isExistentialFormula : bool)
    (propertyToProve : CTL.CTL_Formula)
    (final_loc : int)
    (p_orig : Programs.Program)
    (loopnode_to_copiednode : System.Collections.Generic.Dictionary<int,int>)
    (loc_to_loopduploc : Map<int,int>)
    (isAFFormula : bool)
    (p_bu_sccs : Map<int,Set<int>>)
    (safety : SafetyProver)
    (cps_checked_for_term : Set<int>)
    (pi : (int * Programs.command * int) list)
    (propertyMap: SetDictionary<CTL.CTL_Formula, (int*Formula.formula)>)
    (visited_BU_cp : Map<int, int*int> ref)
    (visited_nodes : Set<int> ref)
    (p_final : Programs.Program) =
    Stats.startTimer "T2 - Insert for rerun"
    //Store in a slot of the datastructure as the original formula (Versus the disjunction splits)
    let (p_orig_loops, p_orig_sccs) = Programs.find_loops p_orig

    let fillVisited_BU_cp cutp uncopied_cutp endOfPropertyCheckNode =
        if isAFFormula then
            visited_BU_cp := (!visited_BU_cp).Add(cutp, (uncopied_cutp, cutp))

        //For AG, we have to duplicate the original cp with no property checks in order to allow
        //other transitions to be explored despite adding in a pre-condition that could falsify the path
        else
            if cutp = -1 then
                visited_BU_cp := (!visited_BU_cp).Add(cutp, (endOfPropertyCheckNode,final_loc))
            else
                if loopnode_to_copiednode.ContainsKey cutp then
                    for (k, _, k') in Programs.enumerate_transitions p_final do
                        //Note: Since we do an AG property check at every node, there is now a lying assumption
                        //that the cutp only has one outer transition. That outer transition is the property check
                        //This is because we do the check, then transition to the next state(s).
                        if k = cutp then
                            visited_BU_cp := (!visited_BU_cp).Add(cutp, (cutp, k'))
                else
                    for node in p_orig_sccs.[cutp] do
                        if not (loopnode_to_copiednode.ContainsKey node) then
                            let copiednode = Programs.new_node p_final
                            loopnode_to_copiednode.Add(node, copiednode)

                    let get_copy_of_loopnode node = loopnode_to_copiednode.GetWithDefault node node

                    for (k, _, k') in Programs.enumerate_transitions p_final do
                        //Note: Since we do an AG property check at every node, there is now a lying assumption
                        //that the cutp only has one outer transition. That outer transition is the property check
                        //This is because we do the check, then transition to the next state(s).
                        if k = cutp then
                            visited_BU_cp := (!visited_BU_cp).Add(cutp, (cutp, k'))
                            Programs.plain_add_transition p_final k [] (get_copy_of_loopnode k)
                            safety.ResetFrom k

                    for (k, cmds, k') in Programs.enumerate_transitions p_orig do
                        if (k' <> cutp && not(loopnode_to_copiednode.ContainsKey k')) || p_orig_sccs.[cutp].Contains k then
                            if loopnode_to_copiednode.ContainsKey k || loopnode_to_copiednode.ContainsKey k' then
                                Programs.plain_add_transition p_final (get_copy_of_loopnode k)
                                    cmds (get_copy_of_loopnode k')
                                if p_orig_loops.ContainsKey k' && k' <> cutp && not ((!visited_BU_cp).ContainsKey k') && loopnode_to_copiednode.ContainsKey k' then
                                    Programs.plain_add_transition p_final (get_copy_of_loopnode k') [] k'
                        safety.ResetFrom k

                    //NOW PROPAGATE UPWARDS TO COPIES

    let updateInstrumentation preCond cutp errorNode endOfPropertyCheckNode (strengthen : bool) =
        //Now we want to instrument this into our program and re-run this whole process again.
        //The reason why we create an extra node to instrument in the pre-condition is because
        //we may need to generate another precondition given that we reached an error from another path
        let (m, m') = if cutp <> -1 then (!visited_BU_cp).[cutp] else (endOfPropertyCheckNode, final_loc)
        let mutable transitionToStrengthen = None
        for l in !p_final.active do
            let (k, cmds, k') = p_final.transitions.[l]
            if  (k = m && k' = m') || (cutp <> errorNode && cutp <> -1 && k = endOfPropertyCheckNode && k' = final_loc) then
            //if (k = m && k' = m') then
                if not(strengthen) then
                    for x in preCond do
                        Programs.plain_add_transition p_final k (Programs.assume(x)::cmds) k'
                    Programs.remove_transition p_final l
                //If we strengthened, we require the elimination of already existing precondition transitions
                else
                    Programs.remove_transition p_final l
                    transitionToStrengthen <- Some (k, k')
            //Redirect loop to cut-point without assumption: For soundness
            else if cutp <> -1 && k' = m && p_bu_sccs.[cutp].Contains k then
                Programs.plain_add_transition p_final k cmds m'
                Programs.remove_transition p_final l
            safety.ResetFrom k //Marc's note: This resets from EVERY location. Really needed?
        if strengthen then
            match transitionToStrengthen with
            | Some (k, k') ->
                for x in preCond do
                    Programs.plain_add_transition p_final k [Programs.assume x] k'
                safety.ResetFrom k
            | None ->
                () //Didn't find anything to insert

    //if cutp = -1, then we are checking a node that occurs before checking any cut-points.
    let(cutp, pi_mod) = findCP p_orig_loops cps_checked_for_term loc_to_loopduploc pi

    let(errorNode, endOfPropertyCheckNode) = findErrorNode p_final pi
    let orig_cp =
        if isAFFormula then
            if p_orig_loops.ContainsKey cutp then cutp
            else loc_to_loopduploc |> Map.findKey(fun _ value -> value = cutp)
        else if cutp = -1 then
            errorNode
        else cutp

    let (strengthen, precondition, preconditionDisjuncts) =
        match recurSet with
        | Some (_, r) ->
            //If we have a recurrent set:
            Log.log pars <| sprintf "Extracting preconditions from recurrent set %s on cutpoint %i for rerun" (r.pp) cutp
            //Getting rid of useless instrumented variables
            let fPreCondNeg =
                Formula.split_conjunction r
                |> List.filter (fun f -> not(Formula.contains_instr_var f) && not(Formula.contains_fair_var f))
                |> Formula.conj

            let precondition = fPreCondNeg |> Formula.negate
            let preconditionDisjuncts = Formula.polyhedra_dnf precondition |> Formula.split_disjunction

            //Now instrument recurrent set and negation of it at the edges going into the loop
            //This is to reassure that within the loop our recurrent sets are progessing and not repeating
            for l in !p_final.active do
                let (k,cmds,k') = p_final.transitions.[l]
                if k = cutp then
                    Programs.remove_transition p_final l
                    for precondDisjunct in preconditionDisjuncts do
                        Programs.plain_add_transition p_final k (Programs.assume(precondDisjunct)::cmds) k'

            let (visitedOnCex, propogateMap,_) = propagate_func p_orig p_orig_loops p_orig_sccs propertyToProve (Some(fPreCondNeg)) pi pi_mod orig_cp isExistentialFormula loc_to_loopduploc visited_BU_cp cps_checked_for_term loopnode_to_copiednode false
            propertyMap.Union(propogateMap)
            visited_nodes := Set.union !visited_nodes visitedOnCex
            (false, precondition, preconditionDisjuncts)
        | None ->   //***************************************************************
            let (precondition, preconditionDisjuncts) = findPreconditionForPath pi_mod
            let p0 = if isExistentialFormula then Formula.negate(precondition) else precondition
            let precond_length = propertyMap.[propertyToProve] |> List.count (fun (x,_) -> x = orig_cp)
            //Checking for repeated counterexamples/preconditions for strengthening
            if Set.contains (orig_cp, p0) propertyMap.[propertyToProve] || (precond_length > 3 )then
                let disjunctiveStrengthenedPreconditions = strengthenCond pi_mod precondition
                let disjunctiveStrengthenedPrecondition = Formula.disj !disjunctiveStrengthenedPreconditions
                //Add strength formula here to propertyMap
                let (visitedOnCex ,propogateMap, preStrengthSet) =
                    propagate_func p_orig p_orig_loops p_orig_sccs propertyToProve None pi pi_mod orig_cp isExistentialFormula loc_to_loopduploc visited_BU_cp cps_checked_for_term loopnode_to_copiednode true
                visited_nodes := Set.union !visited_nodes visitedOnCex

                preStrengthSet := Set.add (orig_cp, p0) !preStrengthSet
                //Saving the properties for formula f before going through the strengthening procedures
                let preStrengthProps = propertyMap.[propertyToProve]
                //We can now replace the properties with their strengthened versions, beginning with orig_cp
                if isExistentialFormula then
                    propertyMap.Replace propertyToProve (orig_cp, Formula.negate(disjunctiveStrengthenedPrecondition))
                else
                    propertyMap.Replace propertyToProve (orig_cp, disjunctiveStrengthenedPrecondition)
                //First, remove any obvious repeating preconditions that have been strengthened
                //preStrengthSet (x,formula) indicates the property before it is strengthened that
                //would definitely need to be removed. Later propogateMap will replace it with
                //a strengthened verison of the formula
                let strengthPropogation = Set.difference preStrengthProps !preStrengthSet
                //The case where preconditon may not be repeating, but getting infinitely more refined
                //We spot the formulas that need to be strengthened by checking if the newly produced (non-strengthened)
                //precondition would imply the old one. If so, then we also remove it, as it will be replaced by propagateMap
                let StrengthPropagation2 = !preStrengthSet |> Set.map(fun (x,y) ->
                                                                //Furtherstrength contains the set of values that should be removed from
                                                                //the non-strenghtened property list.
                                                                let furtherstrength =
                                                                    preStrengthProps |> Set.filter(fun (z,w) -> x = z && (Formula.entails y w))
                                                                furtherstrength) |> Set.unionMany
                for x in Set.difference strengthPropogation StrengthPropagation2 do
                    propertyMap.Add (propertyToProve, x)

                propertyMap.Union(propogateMap)
                (true, disjunctiveStrengthenedPrecondition, List.ofSeq !disjunctiveStrengthenedPreconditions)

            else
                let (visitedOnCex, propogateMap,_) = propagate_func p_orig p_orig_loops p_orig_sccs propertyToProve None pi pi_mod orig_cp isExistentialFormula loc_to_loopduploc visited_BU_cp cps_checked_for_term loopnode_to_copiednode false
                visited_nodes := Set.add orig_cp (Set.union !visited_nodes visitedOnCex)
                propertyMap.Union(propogateMap)
                (false, precondition, preconditionDisjuncts)

    //First, we must find the original cutpoint, versus a copy if it's in AF.
    let uncopied_cutp =
        if loc_to_loopduploc.IsEmpty then cutp
        else loc_to_loopduploc |> Map.findKey(fun _ value -> value = cutp)

    //If doing existential, we instrument the negation of the precondition, yet store the precondition
    //in propertyMap. This is due to the fact that a counterexample in A is a witness of E!
    let mapPreCond = if isExistentialFormula then Formula.negate(precondition) else precondition
    if not(strengthen) then
        if cutp <> -1 then
            propertyMap.Add (propertyToProve, (uncopied_cutp, mapPreCond))
        else
            propertyMap.Add (propertyToProve, (errorNode, mapPreCond))

    //Marc's note: This only happens the first time a cutpoint is visited (because all paths in fillVisited_BU_cp ensure that visited_BU_cp.[cutp] exists after this)
    if cutp <> -1 && not((!visited_BU_cp).ContainsKey cutp) then
        fillVisited_BU_cp cutp uncopied_cutp endOfPropertyCheckNode

    updateInstrumentation preconditionDisjuncts cutp errorNode endOfPropertyCheckNode strengthen
    Stats.endTimer "T2 - Insert for rerun"

let find_instrumented_loops p_instrumented (p_orig_loops : Map<int, Set<int>>) (p_instrumented_loops : Map<int, Set<int>>) (p_instrumented_sccs : Map<int, Set<int>>) (loc_to_loopduploc: Map<int, int>) =
    let loc_to_loopduploc = loc_to_loopduploc |> Map.filter (fun x y -> p_orig_loops.ContainsKey x)
    let duplicated_nodes = loc_to_loopduploc |> Map.toList |> List.map(fun (x,y) -> y)
    let to_add = Set.difference (Set.ofList duplicated_nodes) (Set.ofSeq p_instrumented_loops.Keys)

    let regions = Programs.isolated_regions_non_cp p_instrumented to_add
    let cps_to_loops =
        seq {
            for (cp, sccs) in regions do
                let loop = Set.unionMany sccs
                yield cp, loop
        } |> Map.ofSeq
    let cps_to_sccs =
        seq {
            for (cp, sccs) in regions do
                let loop = sccs |> Seq.filter (fun scc -> scc.Contains cp) |> Set.unionMany
                yield cp, loop
        } |> Map.ofSeq

    let cps_to_loops = Map.fold (fun acc key value -> Map.add key value acc) p_instrumented_loops cps_to_loops
    let cps_to_sccs = Map.fold (fun acc key value -> Map.add key value acc) p_instrumented_sccs cps_to_sccs

    (cps_to_loops,cps_to_sccs)

let private prover (pars : Parameters.parameters) (p_orig:Programs.Program) (f:CTL.CTL_Formula) (termination_only:bool) precondMap (fairness_constraint : (Formula.formula * Formula.formula) option) existential findPreconds next =
    Utils.timeout pars.timeout
    //Maybe let's do some AI first:
    if pars.do_ai_threshold > (!p_orig.active).Count then
        Log.log pars <| sprintf "Performing Interval-AI ... "
        pars.did_ai_first <- true
        do_interval_AI_on_program pars p_orig
        Log.log pars <| sprintf "done."
    else
        pars.did_ai_first <- false

    ///bottomUp: propertyMap represents a map from subformulas to a set of locations/pre-conditions pairs.
    let propertyMap = new SetDictionary<CTL.CTL_Formula, int * Formula.formula>()
    let (p_instrumented, final_loc, error_loc, cp_rf, loc_to_loopduploc) = Instrumentation.mergeProgramAndProperty pars p_orig f termination_only precondMap fairness_constraint findPreconds next
    if pars.chaining then
        let transMap = 
            Programs.chain_program_transitions pars p_instrumented 
                (Seq.append cp_rf.Keys (Seq.collect (function (l1,l2) -> [l1;l2]) loc_to_loopduploc.Items))
                true
        //Rewrite cp_rf to new transition names:
        let cp_rf_serialized = cp_rf |> List.ofSeq
        for KeyValue (cp, checkerTrans) in cp_rf_serialized do
            let mappedCheckerTrans = transMap.[checkerTrans]
            cp_rf.[cp] <- mappedCheckerTrans

    for KeyValue(loc, duploc) in loc_to_loopduploc do
        if not (Set.contains loc !p_instrumented.locs) then
            Log.log pars <| sprintf "Removed duplicated location %i" loc
        if not (Set.contains duploc !p_instrumented.locs) then
            Log.log pars <| sprintf "Removed location duplicate %i" duploc
    let cps_checked_for_term = Set.ofSeq cp_rf.Keys

    let (p_orig_loops, _) = Programs.find_loops p_orig
    let scc_simplification_rfs = ref []
    if pars.lex_term_proof_first then
        let (_, p_instrumented_sccs_plain) = Programs.find_loops p_instrumented
        //First, try to remove/simplify loops by searching for lexicographic arguments that don't need invariants:
        let seen_sccs = ref Set.empty
        for scc in (Map.filter (fun cp _ -> Set.contains cp cps_checked_for_term) p_instrumented_sccs_plain) do
            let (cp, scc_nodes) = (scc.Key, scc.Value)
            if not(Set.contains scc_nodes !seen_sccs) then
                seen_sccs := Set.add scc_nodes !seen_sccs
                match simplify_scc pars p_instrumented termination_only cp_rf cps_checked_for_term cp scc_nodes with
                | Some (rfs, removed_transitions) ->
                    scc_simplification_rfs := (rfs, removed_transitions)::(!scc_simplification_rfs)
                | None ->
                    ()
        if pars.print_log then
            Log.log pars <| (List.map snd !scc_simplification_rfs |> Set.unionMany |> sprintf "Initial lex proof removed transitions %A")

    if pars.dottify_input_pgms then
        Output.print_dot_program p_instrumented "input__instrumented_cleaned.dot"

    ///holds, for each cutpoint, a list of (the index of) the transitions that are lexicographic checkers
    let cp_rf_lex = new System.Collections.Generic.Dictionary<int, int list>()
    for entry in cp_rf do
        cp_rf_lex.Add(entry.Key,[entry.Value])

    let lex_info = Instrumentation.init_lex_info pars cps_checked_for_term

    //If empty, then property is not AF. In cutpoint_nesting_map we fetch the CP's from the original program. If not
    //empty, then proving AF. This means that we just need to match up the original cut-points with their loop copies
    //which are in cp_rf.
    let f_contains_AF = cps_checked_for_term.Count > 0

    //BottomUp changes the instrumentation, so make a copy for that purpose here, as we do not want the pre-conditions to persist in other runs
    let (p_instrumented_loops, p_instrumented_sccs) = Programs.find_loops p_instrumented
    let (_, p_bu_sccs) = find_instrumented_loops p_instrumented p_orig_loops p_instrumented_loops p_instrumented_sccs loc_to_loopduploc
    let p_final = p_instrumented
    let safety = Safety.GetProver pars p_final error_loc

    ///////////////////////////////////////////////////////////////////////////
    /// Main safety loop, instrumenting in termination arguments when needed //
    ///////////////////////////////////////////////////////////////////////////
    let finished = ref false
    let loopnode_to_copiednode = new System.Collections.Generic.Dictionary<int,int>()
    let terminating = ref None
    let unhandled_counterexample = ref None
    let cex_found = ref false
    let found_disj_rfs = ref Map.empty
    let found_lex_rfs = ref Map.empty
    let recurrent_set = ref None
    let cex = ref (Counterexample.make None None)
    let visited_BU_cp = ref Map.empty
    let visited_nodes = ref Set.empty
    let outputCexAsDefect cex =
        if pars.print_log then
            Counterexample.print_defect pars [cex] "defect.tt"
            Counterexample.print_program pars [cex] "defect.t2"
    let noteUnhandledCex cex =
        outputCexAsDefect cex
        unhandled_counterexample := Some cex

    while not !finished && (!terminating).IsNone do
        match safety.ErrorLocationReachable() with
        | None ->
            if (propertyMap.[f]).IsEmpty && not(existential) then
                p_orig_loops.Keys |> Seq.iter (fun locs -> propertyMap.Add(f,(locs,Formula.truec)))
            else if existential then
                p_orig_loops.Keys |> Seq.iter (fun locs -> propertyMap.Add(f,(locs,Formula.falsec)))
            else
                ()
            terminating := Some true
        | Some pi ->
            cex := (Counterexample.make (Some (List.map (fun (x,y,z) -> (x,[y],z)) pi)) None)
            outputCexAsDefect !cex
            //Investigate counterexample. Hopefully returns a solution:
            match Lasso.investigate_cex pars p_final p_instrumented_sccs safety pi !found_disj_rfs !found_lex_rfs lex_info with
            | (None, _) ->
                //We hit this case when the counterexample is not due to a cycle (i.e., we
                //investigated the counterexample, but it wasn't a lasso at all, but just a
                //straight-line path to the error loc)
                //dieWith "Obtained counterexample to termination without a cycle!"
                if findPreconds then
                    insertForRerun pars None existential f final_loc p_orig loopnode_to_copiednode loc_to_loopduploc f_contains_AF p_bu_sccs safety cps_checked_for_term pi propertyMap visited_BU_cp visited_nodes p_final

                    if pars.dottify_input_pgms then
                        Output.print_dot_program p_final "input__instrumented_cleaned_rerun.dot"
                else
                    cex_found := true
                    finished := true

            /////////// Disjunctive (transition invariant) argument:
            | (Some(Lasso.Disj_WF(cp, rf, bnd)),_) ->
                Instrumentation.instrument_disj_RF pars cp rf bnd found_disj_rfs cp_rf p_final safety

            /////////// Lexicographic termination argument:
            | (Some(Lasso.Lex_WF(cp, decr_list, not_incr_list, bnd_list)),_) ->
                Instrumentation.instrument_lex_RF pars cp decr_list not_incr_list bnd_list found_lex_rfs cp_rf_lex p_final safety lex_info

            /////////// Lexicographic polyranking termination argument:
            | (Some(Lasso.Poly_WF(poly_checkers)),cp) ->
                Instrumentation.instrument_poly_RF pars cp poly_checkers cp_rf_lex p_final safety

            /////////// Program simplification:
            | (Some(Lasso.Transition_Removal(trans_to_remove)), _) ->
                //Remove the transitions from the program, remove them from the reachability graph:
                for trans_idx in trans_to_remove do
                    let (k,cmds,k') = p_final.transitions.[trans_idx]
                    Programs.remove_transition p_final trans_idx
                    safety.DeleteProgramTransition (k, cmds, k')
                    safety.ResetFrom k

            /////////// Counterexample for which we couldn't find a program refinement:
            | (Some(Lasso.CEX(cex)), failure_cp) ->
                Log.log pars <| sprintf "Could not find termination argument for counterexample on cutpoint %i" failure_cp
                //If we're doing lexicographic method, try finding a recurrent set at this point (before trying anything else)
                let attempting_lex = ((!lex_info.cp_attempt_lex).[failure_cp])
                if attempting_lex && pars.prove_nonterm then
                    match RecurrentSets.synthesize pars (if termination_only then cex.stem.Value else []) cex.cycle.Value termination_only with
                    | Some set ->
                        terminating := Some false
                        recurrent_set := Some (failure_cp, set)
                    | None   -> ()

                //if we found a recurrent set, exit
                if (!terminating).IsSome then
                    noteUnhandledCex cex
                else
                    //We might haven chosen the wrong order of lexicographic RFs. Try backtracking to another option:
                    let exist_past_lex = (Lasso.exist_past_lex_options failure_cp lex_info)
                    if attempting_lex && exist_past_lex then
                        Log.log pars "Trying to backtrack to other order for lexicographic RF."
                        let (decr_list,not_incr_list,bnd_list) = Instrumentation.switch_to_past_lex_RF pars lex_info failure_cp
                        Instrumentation.instrument_lex_RF pars failure_cp decr_list not_incr_list bnd_list found_lex_rfs cp_rf_lex p_final safety lex_info
                    else
                        //If we are trying lexicographic termination arguments, try switching to lexicographic polyranking arguments:
                        let already_polyrank = (!lex_info.cp_polyrank).[failure_cp]
                        if pars.polyrank && not(already_polyrank) && attempting_lex then
                            Log.log pars "Switching to polyrank."
                            Instrumentation.switch_to_polyrank pars lex_info failure_cp cp_rf_lex p_final safety
                        else
                            //Try the "unrolling" technique
                            if attempting_lex && pars.unrolling && Instrumentation.can_unroll pars lex_info failure_cp then
                                Log.log pars "Trying the unrolling technique."
                                Instrumentation.do_unrolling pars lex_info failure_cp cp_rf_lex p_final safety termination_only
                            else
                                //Try the "detect initial condition" technique
                                let already_doing_init_cond = ((!lex_info.cp_init_cond).[failure_cp])
                                if pars.init_cond && attempting_lex && not(already_doing_init_cond) && not(pars.polyrank) then
                                    Log.log pars "Trying initial condition detection."
                                    Instrumentation.do_init_cond pars lex_info failure_cp p_final cp_rf_lex safety

                                // That's it, no tricks left. Return the counterexample and give up
                                else
                                    Log.log pars "Giving up."
                                    noteUnhandledCex cex
                                    cex_found := true

                                    //If we are doing lexicographic proving, we already tried nonterm further up:
                                    if not(attempting_lex) && (!terminating).IsNone && pars.prove_nonterm && ((!unhandled_counterexample).IsSome) then
                                        match RecurrentSets.synthesize pars (if termination_only then cex.stem.Value else []) cex.cycle.Value termination_only with
                                        | Some set ->
                                            terminating := Some false
                                            recurrent_set := Some (failure_cp, set)
                                        | None   -> ()

                                    finished := true

                if (!recurrent_set).IsSome then
                    cex_found := true

                if findPreconds then
                    //Some true = successful termination proof
                    //Some false = successful nontermination proof (RS in !recurrent_set)
                    //None = Giving up
                    if !terminating = Some false then
                        finished := false
                        terminating := None
                        insertForRerun pars !recurrent_set existential f final_loc p_orig loopnode_to_copiednode loc_to_loopduploc f_contains_AF p_bu_sccs safety cps_checked_for_term pi propertyMap visited_BU_cp visited_nodes p_final
                    else if !terminating = None && !finished = true then
                        //Giving up, if no lex/recurrent set found, then false and entail giving up.
                        //TODO: Exit recursive bottomUp all together, as we cannot proceed with verification
                        //if we have reached this point.
                        raise (System.ArgumentException("Cannot synthesize preconditions due to a failure in either lexicographic function or recurrent set generation!"))


        Utils.run_clear()
    done
    //This is marking nodes that have now cex reaching them for existential..
    for n in !p_orig.locs do
        if !p_orig.initial <> n && existential && isorigNodeNum n p_orig then
            if loopnode_to_copiednode.ContainsKey n then
                if not(Set.contains loopnode_to_copiednode.[n] !visited_nodes) && not(Set.contains n !visited_nodes) then
                    propertyMap.Add(f,(n,Formula.falsec))
            else if not(Set.contains n !visited_nodes) then
                propertyMap.Add(f,(n,Formula.falsec))

    Utils.reset_timeout()

    let is_eg f = match f with
                  | CTL.EG _ -> true
                  | _ -> false

    let return_option =
        if termination_only then
            match !terminating with
            | Some true ->
                Some (true, output_term_proof !scc_simplification_rfs !found_lex_rfs !found_disj_rfs)
            | Some false ->
                if not(!p_final.incomplete_abstraction) then
                    assert (!unhandled_counterexample <> None)
                    Some (false, output_nonterm_proof (!recurrent_set).Value)
                else
                    None
            | None ->
                None
        else
            if !cex_found && not(existential) then
                Some (false, output_cex !cex existential)
            else if !cex_found && (is_eg f) && (!recurrent_set).IsSome then
                Some (true, output_cex !cex existential)
            else if !cex_found && (is_eg f) && (!recurrent_set).IsNone then
                Some (false, output_nocex existential)
            else if !cex_found && existential then
                Some (true, output_cex !cex existential)
            else if not(!cex_found) && not(existential) then
                Some (true, output_nocex existential)
            else
                Some (false, output_nocex existential)

    (return_option, propertyMap)

let propagate_nodes (p : Programs.Program) f (propertyMap : SetDictionary<CTL.CTL_Formula, int * Formula.formula>) =
    //Propagate to non-cutpoints if those have not been reached yet.
    let locs = !p.locs
    let preCond_map = fold_by_loc Formula.And propertyMap.[f]
    for n in locs do
        if not(preCond_map.ContainsKey n) && n <> !p.initial then
            propertyMap.Add(f,(n ,Formula.truec))

let nested_X f f_opt (p : Programs.Program) x_formula (props : SetDictionary<CTL.CTL_Formula, int * Formula.formula>) (fairness_constraint : (Formula.formula*Formula.formula) option) =
    let (p_loops, _) = Programs.find_loops p
    let (orig_f,f) =
        match f_opt with
        |Some(sub_f) -> (f,sub_f)
        |None -> (f,f)
    let propertyMap = new SetDictionary<CTL.CTL_Formula, int * Formula.formula>()
    let prevMap = new System.Collections.Generic.Dictionary<int, List<int>>()
    for n in !p.active do
        let (k,_,k') = p.transitions.[n]
        if not(p_loops.ContainsKey k' && (p_loops.[k'].Contains k)) then
            if prevMap.ContainsKey k' then
               prevMap.[k'] <- k::prevMap.[k']
            else
               prevMap.Add(k', [k])

        else if p_loops.ContainsKey k' then
            if prevMap.ContainsKey k' then
               prevMap.[k'] <- k'::prevMap.[k']
            else
               prevMap.Add(k', [k'])
    let map_by_loc = if x_formula then
                        fold_by_loc Formula.Or props.[f]
                     else
                        fold_by_loc Formula.And props.[f]
    map_by_loc.Remove(!p.initial) |> ignore

    let cmd index_formula =
        match fairness_constraint with
        |Some _ ->
            if x_formula then
                Formula.And(index_formula,Formula.Eq(Term.Var(Formula.fair_term_var),Term.Const(bigint.Zero)))
            else
                Formula.Or(index_formula,Formula.Eq(Term.Var(Formula.fair_term_var),Term.Const(bigint.One)))
        |None -> index_formula

    map_by_loc.Keys |> Set.ofSeq |>
        Set.iter(fun x -> let prev_states = prevMap.[x]
                          prev_states |> List.filter (fun x -> x <> !p.initial)|>
                          List.iter(fun y -> propertyMap.Add(orig_f,(y, (cmd map_by_loc.[x]) ))))

    propertyMap

let set_Rest (props : SetDictionary<CTL.CTL_Formula, int * Formula.formula>) locs formula deflt =
    let X_loc = fold_by_loc Formula.And props.[formula]
    let remaining_loc = Set.difference (locs) (Set.ofSeq (X_loc.Keys))
    remaining_loc |> Set.iter(fun x -> props.Add(formula,(x,deflt)))

/// Proves a CTL property, innermost formulas first, using preconditions.
/// The parameter propertyMap represents a list with the first element being the nested CTL property
/// and the second being a seq of locations/pre-conditions pairs.
/// Note that this map is mutated throughout the proof process.
let rec bottomUp (pars : Parameters.parameters) (p:Programs.Program) (f:CTL.CTL_Formula) (termination_only:bool) nest_level fairness_constraint (propertyMap : SetDictionary<CTL.CTL_Formula, (int*Formula.formula)>)=
    let ret_value = ref None

    //Recurse through the formula, try finding preconditions for each (loc, subformula) pair:
    match f with
    | CTL.EG e
    | CTL.EF e ->
        //First get subresults
        bottomUp pars p e termination_only (nest_level + 1) fairness_constraint propertyMap |> ignore
        //If we are in the outermost case, check if the precondition holds for the initial state, return that:
        if nest_level = 0 then
            let ret = fst <| prover pars p f termination_only propertyMap fairness_constraint true false false
            ret_value := ret
        //Otherwise, check the formula and push the inferred loc/precondition data for the subproperty into our propertyMap
        //as disjunction (because we are proving existentials, these correspond to witnesses to the property)
        else
            match e with
            | CTL.AX _ ->
                let props = snd <| prover pars p f termination_only propertyMap fairness_constraint true true false
                set_Rest props !p.locs f Formula.falsec
                propertyMap.Union(nested_X f (Some(f)) p true props fairness_constraint)
            | CTL.EX _ ->
                let props = snd <| prover pars p f termination_only propertyMap fairness_constraint true true false
                set_Rest props !p.locs f Formula.falsec
                propertyMap.Union(nested_X f (Some(f)) p true props fairness_constraint)
            | _ ->
                let props = snd <| prover pars p f termination_only propertyMap fairness_constraint true true false
                let preCond_map = fold_by_loc Formula.Or props.[f]
                preCond_map |> Seq.iter(fun x -> propertyMap.Add(f,(x.Key,x.Value)))
    | CTL.EX e ->
        bottomUp pars p e termination_only (nest_level + 1) fairness_constraint propertyMap |> ignore
        //If we are in the outermost case, check if the precondition holds for the initial state, return that:
        if nest_level = 0 then
            let ret = fst <| prover pars p f termination_only propertyMap fairness_constraint true false true
            ret_value := ret
        //Otherwise, check the formula and push the inferred loc/precondition data into our propertyMap (as implicit conjunction)
        else
            let Props = snd <| prover pars p (CTL.EF(e)) termination_only propertyMap fairness_constraint true true true
            set_Rest Props !p.locs (CTL.EF(e)) Formula.falsec
            let preCond_map = nested_X f (Some(CTL.EF(e))) p true Props fairness_constraint
            let x_formulae = fold_by_loc Formula.Or preCond_map.[f]
            x_formulae |> Seq.iter(fun x -> propertyMap.Add(f,(x.Key,x.Value)))

    | CTL.AX e ->
        bottomUp pars p e termination_only (nest_level + 1) fairness_constraint propertyMap |> ignore
        //If we are in the outermost case, check if the precondition holds for the initial state, return that:
        if nest_level = 0 then
            let ret = fst <| prover pars p f termination_only propertyMap fairness_constraint false false true
            ret_value := ret
        //Otherwise, check the formula and push the inferred loc/precondition data into our propertyMap (as implicit conjunction)
        else
            let Props = snd <| prover pars p (CTL.AG(e)) termination_only propertyMap fairness_constraint false true true
            set_Rest Props !p.locs (CTL.AG(e)) Formula.truec
            let preCond_map =  nested_X f (Some(CTL.AG(e))) p false Props fairness_constraint
            let x_formulae = fold_by_loc Formula.And preCond_map.[f]
            x_formulae |> Seq.iter(fun x -> propertyMap.Add(f,(x.Key,x.Value)))
            propertyMap.Union(preCond_map)

    | CTL.AG e
    | CTL.AF e ->
        //First get subresults
        bottomUp pars p e termination_only (nest_level + 1) fairness_constraint propertyMap |> ignore
        //If we are in the outermost case, check if the precondition holds for the initial state, return that:
        if nest_level = 0 then
            let ret = fst <| prover pars p f termination_only propertyMap fairness_constraint false false false
            ret_value := ret
        //Otherwise, check the formula and push the inferred loc/precondition data into our propertyMap (as implicit conjunction)
        else
            match e with
            | CTL.AX _ ->
                let Props = snd <| prover pars p f termination_only propertyMap fairness_constraint false true false
                set_Rest Props !p.locs f Formula.truec
                propertyMap.Union(nested_X f (Some(f)) p false Props fairness_constraint)
            | CTL.EX _ ->
                let Props = snd <| prover pars p f termination_only propertyMap fairness_constraint false true false
                set_Rest Props !p.locs f Formula.truec
                propertyMap.Union(nested_X f (Some(f)) p false Props fairness_constraint)
            | _ ->
                let Props = snd <| prover pars p f termination_only propertyMap fairness_constraint false true false
                propertyMap.Union(Props)
    | CTL.AW(e1, e2) ->
        //First get subresults for the subformulae
        bottomUp pars p e1 termination_only (nest_level+1) fairness_constraint propertyMap |> ignore
        bottomUp pars p e2 termination_only (nest_level+1) fairness_constraint propertyMap |> ignore
        //Propagate knowledge for non-atomic formulae
        if not(e1.isAtomic) && e2.isAtomic then
            propagate_nodes p e1 propertyMap
        else if e1.isAtomic && not(e2.isAtomic) then
            propagate_nodes p e2 propertyMap

        //If Operator is not nested within another temporal property, then check at the initial state
        if nest_level = 0 then
            let ret = fst <| prover pars p f termination_only propertyMap fairness_constraint false false false
            ret_value := ret
        //Otherwise, check the formula and push the inferred loc/precondition data into our propertyMap (as implicit conjunction)
        else
            let Props = snd <| prover pars p f termination_only propertyMap fairness_constraint false true false
            propertyMap.Union(Props)
    | CTL.CTL_And(e1,e2)
    | CTL.CTL_Or(e1,e2)  ->
        //First get subresults for the subformulae
        if not(e1.isAtomic) && not(e2.isAtomic) && nest_level = 0 then
            let prop1 = bottomUp pars p e1 termination_only 0 fairness_constraint propertyMap
            let prop2 = bottomUp pars p e2 termination_only 0 fairness_constraint propertyMap

            let (prop_value1,output) =
                match prop1 with
                | Some(pair) -> pair
                | None -> failwith "Failure when doing &&/||"
            let (prop_value2,output) =
                match prop2 with
                | Some(pair) -> pair
                | None -> failwith "Failure when doing &&/||"
            match f with
               | CTL.CTL_And _ -> ret_value := Some(prop_value1 && prop_value2, output)
               | CTL.CTL_Or _ -> ret_value := Some(prop_value1 || prop_value2, output)
               | _ -> failwith "Failure when doing &&/||"


        else
            bottomUp pars p e1 termination_only (nest_level+1) fairness_constraint propertyMap |> ignore
            bottomUp pars p e2 termination_only (nest_level+1) fairness_constraint propertyMap |> ignore
            //Propagate knowledge for non-atomic formulae
            if not(e1.isAtomic) && e2.isAtomic then
                propagate_nodes p e1 propertyMap
            else if e1.isAtomic && not(e2.isAtomic) then
                propagate_nodes p e2 propertyMap
            else
                if nest_level = 0 then
                    propagate_nodes p e1 propertyMap
                    propagate_nodes p e2 propertyMap

            let preCond_map1 = match e1 with
                               |CTL.EF _ |CTL.EG _ |CTL.EU _ |CTL.EX _
                               |CTL.CTL_Or _-> fold_by_loc Formula.Or propertyMap.[e1]
                               |_ -> fold_by_loc Formula.And propertyMap.[e1]
            let preCond_map2 = match e2 with
                               |CTL.EF _ |CTL.EG _ |CTL.EU _ |CTL.EX _
                               |CTL.CTL_Or _ ->fold_by_loc Formula.Or propertyMap.[e2]
                               |_ -> fold_by_loc Formula.And propertyMap.[e2]


            let IentryKeys = Set.intersect ((preCond_map1.Keys) |> Set.ofSeq) ((preCond_map2.Keys) |> Set.ofSeq)

            for entry in IentryKeys do
                let precondTuple = (preCond_map1.[entry], preCond_map2.[entry])
                match f with
                | CTL.CTL_And _ -> propertyMap.Add (f, (entry, (Formula.And precondTuple)))
                | CTL.CTL_Or _ -> propertyMap.Add (f, (entry, (Formula.Or precondTuple)))
                | _ -> failwith "Failure when doing &&/||"

            //If Operator is not nested within another temporal property, then check at the initial state
            if nest_level = 0 then
               let ret = fst <| prover pars p f termination_only propertyMap fairness_constraint false false false
               ret_value := ret

    | CTL.Atom a ->
        //We've hit bottom, so now to prove the next outer temporal property
        //instrumenting in the atomic predicate versus preconditions at each
        //cutpoint.
        //If only one temporal property, then must check at every location
        if nest_level = 1 then
            for k in Programs.get_current_locations p do
                propertyMap.Add(f,(k,a))
        else
            //let scc_locs = p_sccs.Items |> Seq.collect snd |> Set.ofSeq
            //scc_locs |> Set.iter (fun loc -> propertyMap.Add(f, (loc, a)))
            //*****//
            !p.locs |> Set.iter(fun loc -> propertyMap.Add(f, (loc, a)))
    | CTL.EU _ ->
        raise (new System.NotImplementedException "EU constraints not yet implemented")

    let propertyMap =
                       if fairness_constraint.IsSome then
                            let formulaMap = propertyMap.[f]
                            propertyMap.Remove(f) |> ignore
                            propertyMap.Union(quantify_proph_var f f formulaMap)
                            propertyMap
                       else
                            propertyMap

    !ret_value

let make_program_infinite (p : Programs.Program) =
    let (p_loops, p_sccs) = Programs.find_loops p
    let visited = ref Set.empty
    let infinite_loop = Programs.map p "INF_Loop"

    //Creating self-loop
    Programs.plain_add_transition p infinite_loop [Programs.assign Formula.fair_term_var (Term.Const(bigint.One))] infinite_loop

    //Find dead end locations
    let dead_ends = ref !p.locs
    for n in !p.active do
       let (k,_,_) = p.transitions.[n]
       if Set.contains k !dead_ends then
           dead_ends := Set.remove k !dead_ends

    for n in !p.active do
        let (k,c,k') = p.transitions.[n]
        if k = !p.initial then
            p.transitions.[n] <- (k,c@ [Programs.assign Formula.fair_term_var (Term.Const(bigint.Zero))],k')
        else if (p_loops.ContainsKey k') && not(Set.contains k' !visited) then
            visited := Set.add k' !visited
            //Want to make sure that it's not a nested loop.
            let inner_loop = p_sccs.Items |> Seq.exists (fun (cp, locs) -> (k' <> cp && Set.contains k' locs))
            if not(inner_loop) then
                let intersect = Set.difference p_loops.[k'] p_sccs.[k']
                //If empty, then there are no outgoing edges from the loop
                //We thus add our own so we can create a non-terminating program
                if intersect.IsEmpty then
                    //Negate the loop guard to generate an outgoing edge
                    //This is done by finding all the edges going into the loop
                    let trans_visited = ref Set.empty
                    let trans_commands = ref List.Empty
                    for l in !p.active do
                        let (m,c,m') = p.transitions.[l]
                        if (m = k') && not(Set.contains m' !trans_visited) then
                            trans_visited := Set.add m' !trans_visited
                            let f = c |> List.map(function | (Programs.Assume(_,f)) -> f
                                                           | _ -> Formula.truec )
                            let f_conj = Formula.conj f
                            trans_commands := [f_conj] @ !trans_commands
                    let neg_commands = !trans_commands |> List.map(fun x -> Formula.negate(x)) |> Formula.conj
                    let disj_commands = Formula.polyhedra_dnf neg_commands |> Formula.split_disjunction
                    for i in disj_commands do
                        Programs.plain_add_transition p k' [Programs.assume i] infinite_loop
        if Set.contains k' !dead_ends then
            Programs.plain_add_transition p k' [Programs.assume (Formula.truec)] infinite_loop

let rec nTerm f =
    match f with
    | CTL.Atom a -> CTL.Atom a
    | CTL.CTL_And(e1,e2) ->  CTL.CTL_And(nTerm e1, nTerm e2)
    | CTL.CTL_Or(e1,e2)  ->  CTL.CTL_Or(nTerm e1, nTerm e2)
    //Revise X and W to also have nontermination and termination
    | CTL.EX e -> CTL.EX(CTL.CTL_And(nTerm e,CTL.Atom(Formula.Eq(Term.Var(Formula.fair_term_var),Term.Const(bigint.Zero)))))
    | CTL.AX e -> CTL.AX(CTL.CTL_Or(nTerm e,CTL.Atom(Formula.Eq(Term.Var(Formula.fair_term_var),Term.Const(bigint.One)))))
    | CTL.EG e -> CTL.EG(CTL.CTL_And(nTerm e, CTL.EG(CTL.Atom(Formula.truec))))
    | CTL.EF e -> CTL.EF(CTL.CTL_And(nTerm e, CTL.EG(CTL.Atom(Formula.truec))))
    | CTL.AG e -> CTL.AG(CTL.CTL_Or(nTerm e, CTL.AF(CTL.Atom(Formula.falsec))))
    //| CTL.AG e -> CTL.AG e
    | CTL.AF e -> CTL.AF e
    //| CTL.AF e -> CTL.AF(CTL.CTL_Or(nTerm e, CTL.AF(CTL.Atom(Formula.falsec))))
    | CTL.AW(e1,e2) -> CTL.AW(nTerm e1, (CTL.CTL_Or(nTerm e2, CTL.AF(CTL.Atom(Formula.falsec)))))
    | CTL.EU _ -> raise (new System.NotImplementedException "EU constraints not yet implemented")

let bottomUpProver (pars : Parameters.parameters) (p:Programs.Program) (f:CTL.CTL_Formula) (termination_only:bool) (fairness_constraint : (Formula.formula * Formula.formula) option) =
    Z.createZ3Context()
    Utils.timeout pars.timeout

    //Under CTL semantics, it is assumed that all paths are infinite. We thus add infinite loops to any terminating paths unless we are explicitly proving termination.
    //For example, we would be proving AF x instead of AF x || termination, which is what is proved if the path is not infinite.
    //All terminating states are marked by fair_term_var. This variable is then used by both AX/EX and later fairness, as an AX property holds if the next state is terminating, while an EX
    //property does not.
    //When proving Fair + CTL, we do not need to prove properties pertaining terminating paths, thus fair_term_var is utilized here as well.
    if not(termination_only) then make_program_infinite p

    if fairness_constraint.IsSome then
        p.vars := Set.add (Formula.fair_proph_var) !p.vars
        p.vars := Set.add (Formula.fair_proph_old_var) !p.vars
        p.vars := Set.add (Formula.fair_term_var) !p.vars

    //Termination proving obviously doesn't work as normal then, so instead check __fair_TERM == 1 and turn off termination trickery.
    let (f,termination_only) = if termination_only && fairness_constraint.IsSome then
                                    (CTL.AF(CTL.Atom((Formula.Eq(Term.Var(Formula.fair_term_var),Term.Const(bigint.One))))),false)
                               else if not(termination_only) && fairness_constraint.IsSome then
                                    (nTerm f, false)
                               else
                                    (f,termination_only)

    let propertyMap = SetDictionary<CTL.CTL_Formula, int * Formula.formula>()
    let ret_value =
        try
            bottomUp pars p f termination_only 0 fairness_constraint propertyMap
        with
        | :? System.ArgumentException as ex ->
            printfn "Exception! %s " (ex.Message)
            None

    Utils.reset_timeout()

    //Fix up return value to also print something proof-like for CTL things:
    if ret_value.IsSome && not(termination_only) then
        let (propertyValidity, proof_printer) = ret_value.Value
        let ext_proof_printer (outWriter : System.IO.TextWriter) =
            proof_printer outWriter
            outWriter.WriteLine("Preconditions generated / checked during the proof:")
            for (subFormula, preconditions) in propertyMap do
                outWriter.WriteLine(" - Preconditions for subformula {0}:", subFormula.pp)
                for (loc, precondition) in preconditions |> Seq.sortBy fst do
                    outWriter.WriteLine("    at loc. {0:D}{1}: {2}", loc, (if Map.containsKey loc !p.nodeToLabels then " (label " + (!p.nodeToLabels).[loc] + ")" else ""), precondition.pp)
        Some (propertyValidity, ext_proof_printer)
    else
        ret_value