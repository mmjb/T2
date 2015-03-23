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

let make_prio_map (p: Programs.Program) (error_loc: int) =
    //bfs from error location on reversed transition relation, assigned prio is inverted minimal distance
    let in_trans = new System.Collections.Generic.Dictionary<int, System.Collections.Generic.HashSet<int * Programs.command list * int>>()
    let all_nodes = ref Set.empty
    let add_to_set_dict (dict : System.Collections.Generic.Dictionary<int, System.Collections.Generic.HashSet<int * Programs.command list * int>>) k v =
        if dict.ContainsKey k then
            dict.[k].Add v
        else
            dict.Add(k, new System.Collections.Generic.HashSet<int * Programs.command list * int>())
            dict.[k].Add v
    for n in !p.active do
        let trans = p.transitions.[n]
        let (k, _, k') = trans
        add_to_set_dict in_trans k' trans |> ignore
        all_nodes := Set.add k' <| Set.add k !all_nodes

    let res = ref Map.empty
    let todo = new System.Collections.Generic.Queue<int * int>()
    todo.Enqueue(error_loc, 0)

    while todo.Count > 0 do
        let (node, dist) = todo.Dequeue()
        if not(Map.containsKey node !res) then
            res := Map.add node dist !res
            if in_trans.ContainsKey node then //not everyone has incoming transitions. Think start state
                let all_in_trans = in_trans.[node]
                for (pred, _, _) in all_in_trans do
                    todo.Enqueue(pred, dist - 1)

    //Whoever has no weight does not even reach error_loc. Make them go last:
    let min_weight = -(!p.active).Count
    for node in !all_nodes do
        if not(Map.containsKey node !res) then
            res := Map.add node min_weight !res

    !res

/// Tries to remove as many transitions as possible from a SCC. Returns a list of used rank functions/bounds.
let simplify_scc (pars : Parameters.parameters) p termination_only (cp_rf: System.Collections.Generic.Dictionary<int, int>) (all_cutpoints: int list) cp scc_nodes =
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
let findPreCond_FM (cex : (int*Programs.command*int) list) =
    let cex = cex |> List.map (fun (x,y,z) -> (x,(Programs.const_subst y), z))
    let cex = List.map (fun (x,y,z) -> (x,[y],z)) cex

    // Strip out the SSA indices from an entire formula
    let strip_ssa f = Formula.subst (fun v -> Term.var (Var.unprime_var v)) f

    //Fourier-Motzkin elimination done here
    let cex, var_map = Symex.path_to_transitions_and_var_map cex Map.empty
    let cex = Symex.transitions_to_formulae cex |> List.filter (fun f -> not(Formula.contains_instr_var f)) |> Formula.conj
    //let cex = Symex.transitions_to_formulae cex |> List.filter (fun f -> not(Formula.contains_instr_var f) && not(Formula.contains_fair_var f)) |> Formula.conj
    let ts = ref (cex |> SparseLinear.formula_to_linear_terms)
    for var in var_map.Keys do
        for i in (Symex.get_var_index Map.empty var)+1..(Symex.get_var_index var_map var) do
            let var_prime = (Var.prime_var var i)
            ts := SparseLinear.eliminate_var var_prime !ts
            ts := SparseLinear.simplify_as_inequalities !ts

    let f =  List.map SparseLinear.linear_term_to_formula !ts |> Formula.conj
    //This formula has an SSA tag, must strip off before returning
    //If disjunction, we also must split in order to properly instrument in graph.
    let f = Formula.negate (strip_ssa f)
    (f, Formula.polyhedra_dnf f |> Formula.split_disjunction)

let is_existential e = 
    match e with
    | CTL.EF _ | CTL.EG _ | CTL.EU _ | CTL.EX _ -> true
    | _ -> false

//Now we must either universally or existentially quantify out the prophecy variables
//from the preconditions.
//For each location, apply quantifier elimination.
//So make below a function that you can call, and also call it in other areas where you do this.
let quantify_proph_var e F formulaMap =
    let propertyMap_temp = ListDictionary<CTL.CTL_Formula, (int*Formula.formula)>()
    for n in formulaMap do 
        let (loc,loc_form) = n
        let loc_form = if (is_existential e) then loc_form else Formula.negate(loc_form)
        let proph_var = loc_form |> Formula.freevars |> Set.filter (fun x -> Formula.is_fair_var x)//x.Contains proph_string __proph_var_det")                    
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
        let strength_f = if (is_existential e) then Formula.disj !disj_fmla else Formula.negate(Formula.disj !disj_fmla)
        propertyMap_temp.Add(F,(loc,strength_f))
    
    propertyMap_temp

//Generating precondition using weakest precondition
let findPreCond (cex : (int*Programs.command*int) list)=
    let f = Analysis.weakest_precondition cex
    let f = Formula.polyhedra_dnf f |> Formula.split_disjunction
    let f = (f |> List.map(fun x -> SparseLinear.formula_to_linear_terms x))
    let f = f |> List.map(fun x -> x |> List.map (fun y -> SparseLinear.linear_term_to_formula y) |> Formula.conj) |> Formula.disj
    let f = Formula.fromZ3 (Z.simplify(Formula.z3 f))
    (f, Formula.polyhedra_dnf f |> Formula.split_disjunction)

let findCP (p_loops : Map<int, Set<int>>) all_cutpoints (copy_pair : Map<int, int>) pi =
    let cutp = ref -1
    let pi_rev = ref (List.rev pi)
    let loops = Set.ofSeq p_loops.Keys
    while !cutp = -1 && !pi_rev <> [] do
        let (z,_,_) = (!pi_rev).Head
        if (List.contains z all_cutpoints || Set.contains z loops) && !cutp = -1 then
            if List.contains z all_cutpoints then
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


let findErrNode p pi =
    let err_node = ref -1
    let insr_node = ref -1

    let pi_rev = ref (List.rev pi)
    while !err_node = -1 && !pi_rev <> [] do
        let (x,_,z) = (!pi_rev).Head
        let label =
            match Programs.findLabel p z with
            | Some(nodeLabel) -> if nodeLabel.Contains "start_of_subproperty_node" then true
                                 else false
            | None -> false
        let end_label =
            match Programs.findLabel p z with
            | Some(nodeLabel) -> if nodeLabel.Contains "end_of_subproperty_node" then true
                                 else false
            | None -> false

        if label then
           err_node := x
        else if end_label then
           insr_node := z
        pi_rev := (!pi_rev).Tail

    assert(!err_node <> -1)
    assert(!insr_node <> -1)
    (!err_node,!insr_node)

let propTotransitions p f recur pi_mod cutp existential (loc_to_loopduploc : Map<int,int>) (visited_BU_cp : Map<int, int*int> ref) visited_nodes cps_checked_for_term (loopnode_to_copiednode : System.Collections.Generic.Dictionary<int,int>) propDir=
    let (p_loops, _) = Programs.find_loops p
    let propertyMap = new ListDictionary<CTL.CTL_Formula, int * Formula.formula>()
    let elim_node = ref !p.initial
    let pi_wp = ref pi_mod
    let recur, r = match recur with
                   |Some(x) -> (x,true)
                   |None -> (Formula.falsec, false)
    while !pi_wp <> [] do 
        let (x,_,z) = (!pi_wp).Head
        let x = if propDir then x else z
        if (x = !elim_node) || (x = cutp) || (loopnode_to_copiednode.ContainsKey cutp && loopnode_to_copiednode.[cutp] = x)then
            pi_wp:= (!pi_wp).Tail
        else
            elim_node := x
            //We do not want to find a condition for the non-copy of a cp, only the copy cp
            let(tempfPreCond, _) = findPreCond_FM !pi_wp
            //Propagate to all cutpoints, not just loops.
            if p_loops.ContainsKey x || List.contains x cps_checked_for_term || Set.contains x !p.locs && isorigNodeNum x p || loopnode_to_copiednode.ContainsValue x then
                let visited = loc_to_loopduploc.FindWithDefault x x
                if not((!visited_BU_cp).ContainsKey visited) then
                    let orig =  if loopnode_to_copiednode.ContainsValue x then 
                                    let orig_node = loopnode_to_copiednode |> Seq.find(fun y -> y.Value = x)
                                    orig_node.Key
                                else if p_loops.ContainsKey x then x
                                else if (!p.locs).Contains x then x
                                else loc_to_loopduploc |> Map.findKey(fun _ value -> value = x)                               
                    if existential then                    
                        propertyMap.Add(f,(orig,Formula.negate(tempfPreCond)))
                    else
                        propertyMap.Add(f,(orig,tempfPreCond))    

            pi_wp := (!pi_wp).Tail
    propertyMap
    

let propogate_func p f recur pi pi_mod cutp existential (loc_to_loopduploc : Map<int,int>) (visited_BU_cp : Map<int, int*int> ref) visited_nodes cps_checked_for_term loopnode_to_copiednode=
    let recurs, r = match recur with
                   |Some(x) -> (x,true)
                   |None -> (Formula.falsec, false)
    let (p_loops, p_sccs) = Programs.find_loops p
    //First propagate preconditions to sccs contained within the loop
    let propertyMap = propTotransitions p f recur pi_mod cutp existential loc_to_loopduploc visited_BU_cp visited_nodes cps_checked_for_term loopnode_to_copiednode false
    //Second, propagate upwards to non-cp nodes that are not part of any SCCS.
    let sccs_vals = p_sccs |> Map.filter(fun x y -> x <> cutp) |> Map.toSeq |> Seq.map snd |> Seq.fold (fun acc elem -> Seq.append elem acc) Seq.empty |> Set.ofSeq
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
                if p_loops.ContainsKey x || List.contains x cps_checked_for_term || Set.contains x !p.locs then
                    let visited = loc_to_loopduploc.FindWithDefault x x
                    if not((!visited_BU_cp).ContainsKey visited) then
                        if x = !p.initial || p_loops.ContainsKey x || not(Map.isEmpty (loc_to_loopduploc |> Map.filter(fun _ value -> value = x)))then 
                            cp_reached := true
                pi_elim := List.append [(!pi_rev).Head] !pi_elim
                pi_rev := (!pi_rev).Tail
            else
                pi_rev := (!pi_rev).Tail

        if r then
            pi_elim := (!pi_elim)@[(node,Programs.assume(recurs),-1)]

        propertyMap.Union(propTotransitions p f recur !pi_elim cutp existential loc_to_loopduploc visited_BU_cp visited_nodes cps_checked_for_term loopnode_to_copiednode true)
    let is_dup x = loc_to_loopduploc |> Map.filter(fun _ value -> value = x) |> Map.isEmpty |> not
    let cex_path = pi |> List.map(fun (x,_,_) -> x) |> List.filter(fun x -> Set.contains x !p.locs || loopnode_to_copiednode.ContainsValue x || is_dup x)
    let cex_path = cex_path |> List.map(fun x -> if loopnode_to_copiednode.ContainsValue x then
                                                    let orig_node = loopnode_to_copiednode |> Seq.find(fun y -> y.Value = x)
                                                    orig_node.Key
                                                 else if (!p.locs).Contains x then x
                                                 else loc_to_loopduploc |> Map.findKey(fun _ value -> value = x) )
    visited_nodes := Set.union !visited_nodes (Set.ofList cex_path)
    (visited_nodes, propertyMap)

/// Prepare the program for another prover run, slowly enumerating all different pre-conditions
/// (which are either conjunctive/disjunctive, depending on whether we are doing universal/existential)
//Note: If a certain PC does not have a pre-condition, it means that there was no CEX, thus it's true.
let insertForRerun (pars : Parameters.parameters) recurSet existential f final_loc (p : Programs.Program) (loopnode_to_copiednode : System.Collections.Generic.Dictionary<int,int>)  (loc_to_loopduploc : Map<int,int>) f_contains_AF 
                     (p_bu_sccs : Map<int,Set<int>>) graph cps_checked_for_term pi (propertyMap: ListDictionary<CTL.CTL_Formula, (int*Formula.formula)>) (visited_BU_cp : Map<int, int*int> ref) visited_nodes (p_final : Programs.Program) =
    //Store in a slot of the datastructure as the original formula (Versus the disjunction splits)
    //But first we must find the original cutpoint, versus a copy if it's in AF.
    let (p_loops, p_sccs) = Programs.find_loops p
    let stren = ref false

    let instrument fPreCond preCond cutp err_node end_sub_node (strengthen : bool) =
        let orig_cp = if loc_to_loopduploc.IsEmpty then cutp
                        else loc_to_loopduploc |> Map.findKey(fun _ value -> value = cutp)
        //Now we want to instrument this into our program and re-run this whole process again.
        //The reason why we create an extra node to instrument in the pre-condition is because
        //we may need to generate another precondition given that we reached an error from another path

        //If doing existential, we instrument the negation of the precondition, yet store the precondition
        //in propertyMap. This is due to the fact that a counterexample in A is a witness of E!
        let mapPreCond = if existential then Formula.negate(fPreCond) else fPreCond
        if cutp <> -1 then
            if not(List.contains (orig_cp,mapPreCond) (propertyMap.[f])) then
                propertyMap.Add(f,(orig_cp,mapPreCond))
        else
            if not(List.contains (orig_cp,mapPreCond) (propertyMap.[f])) then
                propertyMap.Add(f,(err_node,mapPreCond))

        if cutp <> -1 && not((!visited_BU_cp).ContainsKey cutp) then
            if f_contains_AF then
                //let preCond_node = Programs.new_node p_final
                //visited_BU_cp := (!visited_BU_cp).Add(cutp, (preCond_node,cutp))
                for l in !p_final.active do
                    let (k,_,k') = (p_final).transitions.[l]
                    if k' = cutp then
                        let copiedLoop_node = loc_to_loopduploc |> Map.findKey(fun _ value -> value = k')
                        if (k = copiedLoop_node) then
                            visited_BU_cp := (!visited_BU_cp).Add(cutp, (k,cutp))

            //For AG, we have to duplicate the original cp with no property checks in order to allow
            //other transitions to be explored despite adding in a pre-condition that could falsify the path
            else
                //assert (Map.isEmpty loc_to_loopduploc)
                if cutp <> -1 && not(loopnode_to_copiednode.ContainsKey cutp) then
                    for node in p_sccs.[cutp] do
                        if not (loopnode_to_copiednode.ContainsKey node) then
                            let copiednode = Programs.new_node p_final
                            loopnode_to_copiednode.Add(node, copiednode)

                    let get_copy_of_loopnode node =
                        if loopnode_to_copiednode.ContainsKey node then
                            loopnode_to_copiednode.[node]
                        else
                            node

                    for l in !p_final.active do
                        let(k, _, k') = p_final.transitions.[l]
                        //Note: Since we do an AG property check at every node, there is now a lying assumption
                        //that the cutp only has one outer transition. That outer transition is the property check
                        //This is because we do the check, then transition to the next state(s).
                        if k = cutp then
                        //if k = cutp && not((!visited_BU_cp).ContainsKey cutp) then
                            visited_BU_cp := (!visited_BU_cp).Add(cutp, (k,k'))
                            Programs.plain_add_transition p_final k [] (get_copy_of_loopnode k)
                            Reachability.reset pars graph k
     
                    let env_var v =  Var.var v
                    for l in !p.active do
                        let(k, cmds, k') = p.transitions.[l]
                        if (k' <> cutp && not(loopnode_to_copiednode.ContainsKey k')) || p_sccs.[cutp].Contains k then
                            if loopnode_to_copiednode.ContainsKey k || loopnode_to_copiednode.ContainsKey k' then
                                let cmds = cmds |> List.map (function | Programs.Assume(p,f) -> Programs.Assume(p,Formula.alpha env_var f)
                                                                        | Programs.Assign(p,v,t) -> Programs.Assign(p,env_var v,Term.alpha env_var t))
                                Programs.plain_add_transition p_final (get_copy_of_loopnode k)
                                    cmds (get_copy_of_loopnode k')
                                if p_loops.ContainsKey k' && k' <> cutp && not ((!visited_BU_cp).ContainsKey k') && loopnode_to_copiednode.ContainsKey k' then 
                                    Programs.plain_add_transition p_final (get_copy_of_loopnode k') [] k'                          
                        Reachability.reset pars graph k

                    //NOW PROPAGATE UPWARDS TO COPIES
                else if cutp <> -1 && loopnode_to_copiednode.ContainsKey cutp then
                    for l in !p_final.active do
                        let(k, _, k') = p_final.transitions.[l]
                        //Note: Since we do an AG property check at every node, there is now a lying assumption
                        //that the cutp only has one outer transition. That outer transition is the property check
                        //This is because we do the check, then transition to the next state(s).
                        if k = cutp then
                            visited_BU_cp := (!visited_BU_cp).Add(cutp, (k,k'))    
                else visited_BU_cp := (!visited_BU_cp).Add(cutp, (end_sub_node,final_loc))

        let (m, m') = if cutp <> -1 then (!visited_BU_cp).[cutp] else (end_sub_node,final_loc)
        let insert = ref (-1,-1)
        for l in !p_final.active do
            let (k,cmds,k') = p_final.transitions.[l]
            if  (k = m && k' = m') || (cutp <> err_node && cutp <> -1 && k = end_sub_node && k' = final_loc) then
            //if (k = m && k' = m') then
                if not(strengthen) then
                    preCond |> List.iter (fun x ->  Programs.plain_add_transition p_final k (Programs.assume(x)::cmds) k')
                    Programs.remove_transition p_final l
                //If we strengthened, we require the elimination of already existing precondition transitions
                else
                    Programs.remove_transition p_final l
                    insert := (k,k')
            //Redirect loop to cut-point without assumption: For soundness
            else if cutp <> -1 && k' = m && (p_bu_sccs.[cutp]).Contains k then
                Programs.plain_add_transition p_final k cmds m'
                Programs.remove_transition p_final l
            Reachability.reset pars graph k
        if strengthen then
            if !insert <> (-1,-1) then
                let (k,k') = !insert
                preCond |> List.iter (fun x -> Programs.plain_add_transition p_final k (Programs.assume(x)::[]) k')
                Reachability.reset pars graph k
    //if cutp = -1, then we are checking a node that occurs before checking any cut-points.
    let(cutp, pi_mod) = findCP p_loops cps_checked_for_term loc_to_loopduploc pi
    let(err_node, end_sub_node) = findErrNode p_final pi
    let orig_cp =
        if f_contains_AF then
            if p_loops.ContainsKey cutp then cutp
            else loc_to_loopduploc |> Map.findKey(fun _ value -> value = cutp)
        else if cutp = -1 then
            err_node
        else cutp
    let (fPreCond, preCond) =
        match recurSet with
        |Some(_, (r : Formula.formula)) ->
            //If we have a recurrent set:
            Log.log pars <| sprintf "Extracting preconditions from recurrent set %s on cutpoint %i for rerun" (r.pp) cutp
            //Getting rid of useless instrumented variables
            let fPreCondNeg = Formula.split_conjunction r |> List.filter (fun f -> not(Formula.contains_instr_var f) && not(Formula.contains_fair_var f))
                                |> Formula.conj

            let fPreCond = fPreCondNeg |> Formula.negate
            let preCond =  Formula.polyhedra_dnf fPreCond |> Formula.split_disjunction

            //Now instrument recurrent set and negation of it at the edges going into the loop
            //This is to reassure that within the loop our recurrent sets are progessing and not repeating
            for l in !p_final.active do
                let (k,cmds,k') = p_final.transitions.[l]
                if k = cutp then
                    preCond |> List.iter (fun x -> Programs.plain_add_transition p_final k (Programs.assume(x)::cmds) k')
                    Programs.remove_transition p_final l
            
            let (vis_BU,propogateMap) = propogate_func p f (Some(fPreCondNeg)) pi pi_mod orig_cp existential loc_to_loopduploc visited_BU_cp visited_nodes cps_checked_for_term loopnode_to_copiednode
            propertyMap.Union(propogateMap)
            visited_nodes := !vis_BU
            (fPreCond, preCond)

        | None ->   //***************************************************************

                    let(fPreCond, preCond) =
                        let (p1,l1) = findPreCond_FM pi_mod
                        let p_0 = if existential then Formula.negate(p1) else p1
                        let precond_length = propertyMap.[f] |> List.filter (fun (x,y) -> x = orig_cp) |> List.length
                        let (vis_BU,propogateMap) = propogate_func p f None pi pi_mod orig_cp existential loc_to_loopduploc visited_BU_cp visited_nodes cps_checked_for_term loopnode_to_copiednode
                        visited_nodes := Set.union !vis_BU (set[orig_cp])
                        propertyMap.Union(propogateMap)
                        //Checking for repeated counterexamples/preconditions for strengthening
                        if List.contains (orig_cp,p_0) (propertyMap.[f])  || (precond_length > 3 )then
                            let mod_var = pi_mod |> List.map (fun (_,y,_)-> y) |>
                                            List.choose(fun cmd ->
                                                        match cmd with
                                                        | Programs.Assign(_,v,_) -> Some(v)
                                                        | _ -> None)
                            let disj_fmla = ref Set.empty
                            let split_disj = Formula.split_disjunction (Formula.polyhedra_dnf p1)

                            for var in split_disj do
                                let ts = ref (var |> SparseLinear.formula_to_linear_terms)
                                for var in mod_var do
                                        ts := SparseLinear.eliminate_var var !ts
                                        ts := SparseLinear.simplify_as_inequalities !ts
                                disj_fmla := Set.add (List.map SparseLinear.linear_term_to_formula !ts |> Formula.conj) !disj_fmla
                            disj_fmla := Set.remove (Formula.Le(Term.Const(bigint.Zero),Term.Const(bigint.Zero))) !disj_fmla
                            
                            let strength_f = Formula.disj !disj_fmla
                            let old_list = propertyMap.[f]
                            propertyMap.Replace f (orig_cp, strength_f)
                            old_list |> List.filter(fun (x,y) -> not(x = orig_cp && y = p_0))
                                            |> List.iter(fun (x,y) -> propertyMap.Add(f,(x,y)))
                            stren := true
                            (strength_f,List.ofSeq !disj_fmla)

                        else
                            (p1,l1)
                    (fPreCond, preCond)
    instrument fPreCond preCond cutp err_node end_sub_node !stren


let find_instrumented_loops (p_loops : Map<int, Set<int>>) p_instrumented (loc_to_loopduploc: Map<int, int>) =
    let (instrumented_loops, p_instrumented_sccs) = Programs.find_loops p_instrumented
    let loc_to_loopduploc = loc_to_loopduploc |> Map.filter (fun x y -> p_loops.ContainsKey x)
    let duplicated_nodes = loc_to_loopduploc |> Map.toList |> List.map(fun (x,y) -> y)
    let to_add = Set.difference (Set.ofList duplicated_nodes) (Set.ofSeq instrumented_loops.Keys) 

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
    
    let cps_to_loops = Map.fold (fun acc key value -> Map.add key value acc) instrumented_loops cps_to_loops
    let cps_to_sccs = Map.fold (fun acc key value -> Map.add key value acc) p_instrumented_sccs cps_to_sccs

    (cps_to_loops,cps_to_sccs)

let prover (pars : Parameters.parameters) (p:Programs.Program) (f:CTL.CTL_Formula) (termination_only:bool) precondMap (fairness_constraint : (Formula.formula * Formula.formula) option) existential findPreconds next =
    Utils.timeout pars.timeout
    //Maybe let's do some AI first:
    if pars.do_ai_threshold > (!p.active).Count then
        Log.log pars <| sprintf "Performing Interval-AI ... "
        pars.did_ai_first <- true
        do_interval_AI_on_program pars p
        Log.log pars <| sprintf "done."
    else
        pars.did_ai_first <- false

    ///bottomUp: propertyMap represents a map from subformulas to a list the
    ///second being an array of locations/pre-conditions pairs.
    let propertyMap = new ListDictionary<CTL.CTL_Formula, int * Formula.formula>()
    let (p_instrumented, final_loc, error_loc, cp_rf, loc_to_loopduploc) = Instrumentation.mergeProgramAndProperty pars p f termination_only precondMap fairness_constraint findPreconds next
    let cps_checked_for_term = Seq.toList cp_rf.Keys

    let scc_simplification_rfs = ref []
    let (p_loops, _) = Programs.find_loops p
    let (_, p_instrumented_sccs) = find_instrumented_loops p_loops p_instrumented loc_to_loopduploc
    let(_,connected_scc_cp) = Programs.find_loops p_instrumented
    //First, try to remove/simplify loops by searching for lexicographic arguments that don't need invariants:
    let seen_sccs = ref Set.empty
    for scc in (Map.filter (fun cp _ -> List.contains cp cps_checked_for_term) connected_scc_cp) do
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

    //Filters out all transitions not starting in src_loc.
    let trans_fun (trs : (int * Programs.command list * int) []) (src_loc : int) =
        List.ofSeq (trs |> Seq.choose (fun (a,b,c) -> if a <> src_loc then None else Some (b,c)))

    //If empty, then property is not AF. In cutpoint_nesting_map we fetch the CP's from the original program. If not
    //empty, then proving AF. This means that we just need to match up the original cut-points with their loop copies
    //which are in cp_rf.
    let f_contains_AF = cps_checked_for_term.Length > 0

    //BottomUp changes the instrumentation, so make a copy for that purpose here, as we do not want the pre-conditions to persist in other runs
    let p_final = Programs.copy p_instrumented
    let graph = Reachability.init !p_final.initial error_loc (trans_fun p_final.transitions) (Some (make_prio_map p_final error_loc)) !p_final.abstracted_disjunctions
    //let p_bu_sccs = snd <| Programs.find_loops p_final
    let p_bu_sccs = snd <| find_instrumented_loops p_loops p_instrumented loc_to_loopduploc
    ///////////////////////////////////////////////////////////////////////////
    /// Main safety loop, instrumenting in termination arguments when needed //
    ///////////////////////////////////////////////////////////////////////////
    let finished = ref false
    let loopnode_to_copiednode = new System.Collections.Generic.Dictionary<int,int>()
    let terminating = ref None
    let unhandled_counterexample = ref None
    let refine_cnt = ref 0
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
        match Reachability.reachable pars graph with
        | None ->
            if (propertyMap.[f]).IsEmpty && not(existential) then
                p_loops.Keys |> Seq.iter (fun locs -> propertyMap.Add(f,(locs,Formula.truec)))
            else if existential then
                p_loops.Keys |> Seq.iter (fun locs -> propertyMap.Add(f,(locs,Formula.falsec))) 
            else
                ()
            terminating := Some true
        | Some(pi, disj_refinements) ->
            refine_cnt := !refine_cnt + 1          
            cex := (Counterexample.make (Some (List.map (fun (x,y,z) -> (x,[y],z)) pi)) None)
            outputCexAsDefect !cex
            //Investigate counterexample. Hopefully returns a solution:
            match Lasso.investigate_cex pars p_final p_instrumented_sccs graph pi !found_disj_rfs !found_lex_rfs lex_info with
            | (None, _) ->
                //We hit this case when the counterexample is not due to a cycle (i.e., we
                //investigated the counterexample, but it wasn't a lasso at all, but just a
                //straight-line path to the error loc)
                //dieWith "Obtained counterexample to termination without a cycle!"
                if findPreconds then
                    insertForRerun pars None existential f final_loc p loopnode_to_copiednode loc_to_loopduploc f_contains_AF p_bu_sccs graph cps_checked_for_term pi propertyMap visited_BU_cp visited_nodes p_final
                else
                    cex_found := true
                    finished := true

            /////////// Disjunctive (transition invariant) argument:
            | (Some(Lasso.Disj_WF(cp, rf, bnd)),_) ->
                Instrumentation.instrument_disj_RF pars cp rf bnd found_disj_rfs cp_rf p_final graph

            /////////// Lexicographic termination argument:
            | (Some(Lasso.Lex_WF(cp, decr_list, not_incr_list, bnd_list)),_) ->
                Instrumentation.instrument_lex_RF pars cp decr_list not_incr_list bnd_list found_lex_rfs cp_rf_lex p_final graph lex_info

            /////////// Lexicographic polyranking termination argument:
            | (Some(Lasso.Poly_WF(poly_checkers)),cp) ->
                Instrumentation.instrument_poly_RF pars cp poly_checkers cp_rf_lex p_final graph

            /////////// Program simplification:
            | (Some(Lasso.Transition_Removal(trans_to_remove)), _) ->
                //Remove the transitions from the program, remove them from the reachability graph:
                for trans_idx in trans_to_remove do
                    let (k,cmds,k') = p_final.transitions.[trans_idx]
                    Programs.remove_transition p_final trans_idx
                    Reachability.delete_program_transition graph (k,cmds,k')
                    Reachability.reset pars graph k'

            /////////// Counterexample for which we couldn't find a program refinement:
            | (Some(Lasso.CEX(cex)), failure_cp) ->
                Log.log pars <| sprintf "Could not find termination argument for counterexample on cutpoint %i" failure_cp
                // First option: This was due to our lazy treatment of disjunctions. Refine the problematic disjunctions, try again:
                if List.length disj_refinements > 0 then
                    Log.log pars <| sprintf "Refining abstracted %i disjunctions." (List.length disj_refinements)
                    for disj_refinement in disj_refinements do
                        disj_refinement () //This changes the state of the underlying reachability graph
                else
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
                            Instrumentation.instrument_lex_RF pars failure_cp decr_list not_incr_list bnd_list found_lex_rfs cp_rf_lex p_final graph lex_info
                        else
                            //If we are trying lexicographic termination arguments, try switching to lexicographic polyranking arguments:
                            let already_polyrank = (!lex_info.cp_polyrank).[failure_cp]
                            if pars.polyrank && not(already_polyrank) && attempting_lex then
                                Log.log pars "Switching to polyrank."
                                Instrumentation.switch_to_polyrank pars lex_info failure_cp cp_rf_lex p_final graph
                            else
                                //Try the "unrolling" technique
                                if attempting_lex && pars.unrolling && Instrumentation.can_unroll pars lex_info failure_cp then
                                    Log.log pars "Trying the unrolling technique."
                                    Instrumentation.do_unrolling pars lex_info failure_cp cp_rf_lex p_final graph termination_only
                                else
                                    //Try the "detect initial condition" technique
                                    let already_doing_init_cond = ((!lex_info.cp_init_cond).[failure_cp])
                                    if pars.init_cond && attempting_lex && not(already_doing_init_cond) && not(pars.polyrank) then
                                        Log.log pars "Trying initial condition detection."
                                        Instrumentation.do_init_cond pars lex_info failure_cp p_final cp_rf_lex graph

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
                            insertForRerun pars !recurrent_set existential f final_loc p loopnode_to_copiednode loc_to_loopduploc f_contains_AF p_bu_sccs graph cps_checked_for_term pi propertyMap visited_BU_cp visited_nodes p_final
                        else if !terminating = None && !finished = true then
                            //Giving up, if no lex/recurrent set found, then false and entail giving up.
                            //TODO: Exit recursive bottomUp all together, as we cannot proceed with verification
                            //if we have reached this point. 
                            raise (System.ArgumentException("Cannot synthesize preconditions due to a failure in either lexicographic function or recurrent set generation!"))

                                    
        Utils.run_clear()
    done
    //This is marking nodes that have now cex reaching them for existential.. 
    for n in !p.locs do
        if !p.initial <> n && existential && isorigNodeNum n p then
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
                Stats.inc_stat "termination - yes"
                Some (true, output_term_proof !scc_simplification_rfs !found_lex_rfs !found_disj_rfs)
            | Some false ->
                if not(!p_final.incomplete_abstraction) then
                    assert (!unhandled_counterexample <> None)
                    Stats.inc_stat "termination - no"
                    Some (false, output_nonterm_proof (!recurrent_set).Value)
                else
                    Stats.inc_stat "termination - don't know"
                    None
            | None ->
                Stats.inc_stat "termination - don't know"
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

///Takes a loc->formula list as second arg, groups the formulas by loc and connects them using the first argument
let fold_by_loc collector l =
    let preCond_map = new System.Collections.Generic.Dictionary<int, Formula.formula>()
    //First thing, is to eliminate duplicates in the list.
    let l =
        match l with
        | [ ] -> [ ]
        | x::xs -> List.fold(fun acc x -> if x = List.head acc then acc else x::acc) [x] xs 

    l |> List.iter(fun (x,y) -> if preCond_map.ContainsKey x then
                                    preCond_map.[x] <- collector (preCond_map.[x], y)
                                else
                                    preCond_map.Add (x,y))
    preCond_map

let propagate_nodes (p : Programs.Program) f (propertyMap : ListDictionary<CTL.CTL_Formula, int * Formula.formula>) =
    //Propagate to non-cutpoints if those have not been reached yet.
    let locs = !p.locs
    let formula_list = propertyMap.[f]
    let preCond_map = fold_by_loc Formula.And formula_list
    for n in locs do
        if not(preCond_map.ContainsKey n) && n <> !p.initial then
            propertyMap.Add(f,(n ,Formula.truec))

let nested_X f f_opt (p : Programs.Program) x_formula (props : ListDictionary<CTL.CTL_Formula, int * Formula.formula>) (fairness_constraint : (Formula.formula*Formula.formula) option) =
    let (p_loops, _) = Programs.find_loops p
    let (orig_f,f) =
        match f_opt with
        |Some(sub_f) -> (f,sub_f)
        |None -> (f,f)    
    let propertyMap = new ListDictionary<CTL.CTL_Formula, int * Formula.formula>()
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
    let formula_list = props.[f]
    let map_by_loc = if x_formula = 1 then 
                        fold_by_loc Formula.Or formula_list
                     else
                        fold_by_loc Formula.And formula_list
    map_by_loc.Remove(!p.initial) |> ignore

    let cmd index_formula = 
        match fairness_constraint with
        |Some _ -> 
            if x_formula = 1 then
                Formula.And(index_formula,Formula.Eq(Term.Var(Formula.fair_term_var),Term.Const(bigint.Zero)))
            else
                Formula.Or(index_formula,Formula.Eq(Term.Var(Formula.fair_term_var),Term.Const(bigint.One)))    
        |None -> index_formula

    map_by_loc.Keys |> Set.ofSeq |>
        Set.iter(fun x -> let prev_states = prevMap.[x]
                          prev_states |> List.filter (fun x -> x <> !p.initial)|>
                          List.iter(fun y -> propertyMap.Add(orig_f,(y, (cmd map_by_loc.[x]) ))))                

    propertyMap 

let set_Rest (props : ListDictionary<CTL.CTL_Formula, int * Formula.formula>) locs formula deflt =
    let X_loc = fold_by_loc Formula.And props.[formula]
    let remaining_loc = Set.difference (locs) (Set.ofSeq (X_loc.Keys))
    remaining_loc |> Set.iter(fun x -> props.Add(formula,(x,deflt)))

/// Proves a CTL property, innermost formulas first, using preconditions.
/// The parameter propertyMap represents a list with the first element being the nested CTL property
/// and the second being a seq of locations/pre-conditions pairs.
/// Note that this map is mutated throughout the proof process.
let rec bottomUp (pars : Parameters.parameters) (p:Programs.Program) (f:CTL.CTL_Formula) (termination_only:bool) nest_level fairness_constraint (propertyMap : ListDictionary<CTL.CTL_Formula, (int*Formula.formula)>)=
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
                propertyMap.Union(nested_X f (Some(f)) p 1 props fairness_constraint)
            | CTL.EX _ ->
                let props = snd <| prover pars p f termination_only propertyMap fairness_constraint true true false
                set_Rest props !p.locs f Formula.falsec
                propertyMap.Union(nested_X f (Some(f)) p 1 props fairness_constraint)
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
            let preCond_map = nested_X f (Some(CTL.EF(e))) p 1 Props fairness_constraint
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
            let preCond_map =  nested_X f (Some(CTL.AG(e))) p 2 Props fairness_constraint           
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
                propertyMap.Union(nested_X f (Some(f)) p 2 Props fairness_constraint)
            | CTL.EX _ ->
                let Props = snd <| prover pars p f termination_only propertyMap fairness_constraint false true false
                set_Rest Props !p.locs f Formula.truec
                propertyMap.Union(nested_X f (Some(f)) p 2 Props fairness_constraint)
            | _ ->
                let Props = snd <| prover pars p f termination_only propertyMap fairness_constraint false true false
                propertyMap.Union(Props)
        for n in propertyMap do printfn "%A" n                                                                                           
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
                match prop1 with
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
    let inf_trans = Programs.map p "INF_trans"

    //Creating self-loop
    Programs.plain_add_transition p infinite_loop [Programs.assign Formula.fair_term_var (Term.Const(bigint.One))] inf_trans
    Programs.plain_add_transition p inf_trans [] infinite_loop

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

    let propertyMap = ListDictionary<CTL.CTL_Formula, int * Formula.formula>()
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
                for (loc, precondition) in preconditions |> List.sortBy fst do
                    outWriter.WriteLine("    at loc. {0:D}{1}: {2}", loc, (if Map.containsKey loc !p.nodeToLabels then " (label " + (!p.nodeToLabels).[loc] + ")" else ""), precondition.pp)
        Some (propertyValidity, ext_proof_printer)
    else
        ret_value
