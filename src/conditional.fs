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
//
//  Abstract:  Used for finding conditions on termination
//  Author:    Maria Gorinova

module Microsoft.Research.T2.Conditional

open Var
open Term
open Formula
open Programs
open Utils




let print_vars  (vars:Map<var,int>) =
    printf "\nVARS: "
    for v in vars.Keys do
        printf "%s-%d;  " v (Map.find v vars) 
    printfn ""


/// Transforms the program to include some instrument states needed for the reachability procedure. 
/// Returns the transformed program and the error state.
let instrument (p : Programs.Program) (fs : formula) =
    let (cps, _) = p.FindLoops()
    let flags = ref []
    let error = p.NewNode()
    let added = ref []

    for (n, (node, label, node_to)) in p.TransitionsWithIdx do
        if(node <> p.Initial) && (cps.ContainsKey node) then            
            let node_new = p.NewNode()
            let flag:var = (String.concat ("_") (seq["__flag"; (string n)]))
            flags := flag::(!flags)
            let ft:formula = Eq(Var(flag), Const(bigint.Zero))

            p.AddTransition node [(Programs.assume ft); (Programs.assign flag (Const(bigint.One)))] node_new 
            p.AddTransition node_new label node_to
            p.RemoveTransition n
            
            let ff:formula = Eq(Var(flag), Const(bigint.One))
            
            // Here we only add the transition if we don't already have a transition from that node to the error state.
            // If we do have such transition, we update the command list to include the new assume command.
            // Thit is needed so we can distinguish loop-in-a-if-then-else (which can be split to linear cases) and
            // if-then-else-in-a-loop (which leads to non-linear transition function and must be treated separately) 
            let exists = ref false
            for (n1, _, _) in !added do
                if(n1 = node) then 
                    p.TransitionsInplaceMap (fun (n, lab, n') -> if(n = node && n' = error) then (n, (Programs.assume ff)::lab, n') else (n, lab, n'))
                    exists := true

            if(not !exists) then 
                p.AddTransition node [(Programs.assume ff)] error
                added := (node, Programs.assume ff, error)::(!added)                   
        

        //*************************************************************************************************************

        if(cps.ContainsKey node_to) && (not ((cps.Item node_to).Contains node)) then
            let node_new = p.NewNode()

            p.AddTransition node_new label node_to 
            for f in (fs |> Formula.polyhedra_dnf |> Formula.split_disjunction) do
                p.AddTransition node ((Programs.assume (Not(f)))::[for fl in !flags -> (Programs.assign fl (Const(bigint.Zero)))]) node_new 
            
            p.RemoveTransition n  


    (p, error)


///Filters out all transitions not starting in src_loc. Copied from Termination
let trans_fun (trs : (int * Programs.Command list * int) []) (src_loc : int) =
    List.ofSeq (trs |> Seq.choose (fun (a,b,c) -> if a <> src_loc then None else Some (b,c)))


let find_counterexample pars p err_loc =
    let safety = Safety.GetProver pars p err_loc
    safety.ErrorLocationReachable() 
    
let contains path s = 
    let flag = ref false
    for (s1, _, _) in !path do
        if (s1 = s) then flag := true
    !flag    


/// Given a counterexample cex, it splits it into transitions 
/// describing the stem and transitions describing the cycle    
let find_cycle cex =

    let stem = ref []
    let cycle = ref []
    let (cyc_node, _, _) = Seq.last cex 
    let flag = ref true         
    
    for (s1, l, s2) in cex do
        if(!flag) then
            if(s1 = cyc_node) then 
                flag := false
                cycle := (s1, l, s2)::(!cycle)
            else stem := (s1, l, s2)::(!stem)                      
        
        else cycle := (s1, l, s2)::(!cycle)                

    (List.rev !stem, List.rev !cycle)



/// Takes a formula and a mapping of variables
/// Returns the result of Fourier-Motzkin elimination on that formula
let formula_qelim (vars:Map<var,int>) f =

    let linear_terms = f 
                    |> Formula.split_conjunction                     
                    |> List.filter (fun x -> not(Formula.contains_instr_var x))                     
                    |> Formula.conj 
                    |> SparseLinear.formula_to_linear_terms 
                    |> ref 
    
    for v in vars.Keys do
        for i in 1..(Symex.get_var_index vars v) do
            let prime_v = Var.prime_var v i
            linear_terms := SparseLinear.eliminate_var prime_v !linear_terms
            linear_terms := SparseLinear.simplify_as_inequalities !linear_terms

    let ret = !linear_terms
            |> List.map SparseLinear.linear_term_to_formula 
            |> Filter.redundant
            |> Formula.conj
            |> Formula.alpha Var.unprime_var

    ret


/// Finds the weakest liberal precondition, s.t. the postcondition phi is invariant
let wlp_star (rho:formula) (phi:formula) (vars_base:Map<var,int>) =

    let max_iterations = 4
    let rho_n = ref rho
    let rho_conj = ref rho

    let phi_n = ref (Formula.advance_formula (alpha (fun v -> Var.prime_var v 0) phi) vars_base)
    let vars_cur = ref vars_base

    let to_recurse_with = ref []
    let result = ref truec    

    for i in 1..max_iterations do

        vars_cur := Map.map (fun v j -> j + vars_base.Item v) !vars_cur 

        let result_new = And(!rho_conj, Not(!phi_n))
                      |> formula_qelim !vars_cur
                      |> Not
                      |> Formula.polyhedra_dnf 
                      |> Formula.clean_formula

        result := And(!result, result_new)
               |> Formula.polyhedra_dnf 
               |> Filter.redundant_disjunctions 
               |> Formula.clean_formula

        rho_n := Formula.advance_formula !rho_n vars_base
        phi_n := Formula.advance_formula !phi_n vars_base
        rho_conj := And(!rho_conj, !rho_n)                    
    
    
    let disjs = Formula.split_disjunction (!result)  
    result := falsec

    for d in disjs do
        let generalised_d = Filter.generalise d                     
        result := Or((!result), generalised_d)

        if(generalised_d <> d) then to_recurse_with := generalised_d::(!to_recurse_with)      

    (!result, !to_recurse_with)        


/// Takes initial condition tetha and transition function rho of the program. 
/// Returns a disjunction describing preconditions for termination of a program
/// without phase change. 
let pre_synth (rho:formula, econd:formula, vars) = 
    
    let get_vars_and_primes f =
    
        let vs = Formula.freevars f
        let weird = Set.map (fun v -> (Var.unprime_var v), int (Var.get_prime_idx v)) vs 
        
        let res = ref Map.empty

        for (v, i) in weird do
            if(Map.containsKey v !res) then 
                if(Map.find v !res < i) then 
                    res := Map.remove v !res
                        |> Map.add v i 

            else res := Map.add v i !res

        !res

                 
    let ret_c = ref falsec
    let ret_b = ref falsec
    let change_in_ret = ref false
    let vars = get_vars_and_primes rho

    // As we don't need to use each disjunction as a constraint for the next call of
    // pre_synth_phase, we keep the "important" ones in ret_rec_terms and give that 
    // as a return value as well
    let ret_rec_terms_c = ref []
    let ret_rec_terms_b = ref [] 

    //printfn "\n************************************************\nEC: %s" econd.pp

    let potential_ranking_functions = rho 
                                   |> Formula.polyhedra_cnf
                                   |> Formula.simplify                                   
                                   |> Filter.redundant_disjunctions
                                   |> Filter.redundant_conjunction

    //printfn "rho: %s\nPRF before QELIM: %s" rho.pp (potential_ranking_functions).pp 

    let potential_ranking_functions = potential_ranking_functions
                                   |> formula_qelim vars    
                                   |> Filter.redundant_conjunction
                                   |> Formula.split_conjunction 
                                   |> formulae_to_terms
                                   |> List.map (fun t -> Ge(t, Const(bigint.Zero)))

    //printfn "PRF after QELIM: %s" (Formula.conj potential_ranking_functions).pp 

    for b in potential_ranking_functions do

        // does the ranking function imply the exit conditions? 
        let implies_exit_conditions = Formula.entails (Not(b)) econd
      
        //printfn "\nPotential Ranking Function for \n%s \nis:\n %s" rho.pp b.pp

        let freevars = Formula.freevars b
        let varsb = Map.filter (fun var _ -> if freevars.Contains var then true else false) vars

        let (Ge(b_term_primed, _)) = alpha (fun v -> Var.prime_var v (Symex.get_var_index varsb v)) b
        let (Ge(b_term, _)) = alpha (fun v -> Var.prime_var v 0) b

        // Find strengthening by QELIM on (forall X'. rho(X, X') -> b(X') <= b(X)-1 ).
        // That is equivalent to not exist X'. rho(X, X') AND not b(X') <= b(X)-1
        let decrease_condition = Le(b_term_primed, Sub(b_term, Const(bigint.One)))
        let dc = (formula_qelim vars decrease_condition)
        //printfn "decrease condition: %s" dc.pp        
        

        // We are only interested in the current ranking function and strengthening 
        // if rho(X, X') -> b(X') <= b(X)-1 has its RHS satisfiable
        if(not (Formula.unsat dc)) then

            let qelim = And(rho, Not(decrease_condition))      
            let strengthening = qelim 
                             |> formula_qelim varsb 
                             |> Not 
                             |> Formula.polyhedra_dnf 
                             |> Formula.clean_formula        

            //printfn "Strengthening is:\n %s\n" strengthening.pp

            // TODO: When applied to transition functions with several constrains, it might give unwanted results. 
            // For example, if we are analysing the program (while(true) do if(x<=0) then () elif (x<10) then x=x+y)
            // when looking at the elif branch and the ranking function (x-1), we want to consider exit from the 
            // component only through the condition (x>0). However we get strengthening (y <= -1 or x <= 0 or 0 <= -__const_10+x)
            // The last disjunct is a direct exit through the condition (x<10). Thus, when applying wlp procedure on that 
            // strengthening we also get conditions guaranteeing terminating through the (x<10) condition. 
            // Those, however, don't imply that the potential ranking function is decreasing...
            
            let (wlp, rec_terms) = wlp_star rho strengthening vars                        
            
            if(implies_exit_conditions) then 
                ret_c := Or (!ret_c, (Formula.simplify wlp))
                //printfn "update C: %s" (Formula.simplify wlp).pp
                ret_rec_terms_c := rec_terms@(!ret_rec_terms_c)
            else 
                ret_b := Or (!ret_b, (Formula.simplify wlp))
                //printfn "update B: %s" (Formula.simplify wlp).pp
                ret_rec_terms_b := rec_terms@(!ret_rec_terms_b)
            change_in_ret := true
        else 
            // the only way that terminates is if it never enters the loop, so transition function is false:
            if(implies_exit_conditions) then
                ret_c := Or (!ret_c, Not(b))
            else ret_b := Or (!ret_b, Not(b))                     
            change_in_ret := true

    ret_c := !ret_c |> Formula.simplify  |> Filter.redundant_disjunctions
    ret_b := !ret_b |> Formula.simplify  |> Filter.redundant_disjunctions

    if(not !change_in_ret) then 
        ret_c := truec
        
    //printfn "\nC: %s; \nB: %s \n************************************************\n" (!ret_c).pp (!ret_b).pp
                             
    (!ret_c, !ret_rec_terms_c, !ret_b, !ret_rec_terms_b)



/// Takes initial condition tetha and transition function rho of the program. 
/// Returns a disjunction describing preconditions for termination of a program
/// with phase change. 
let rec pre_synth_phase (rho:formula, vars, cur_constr:formula, econd, depth_left) = 


    // pre_synth, as everything else in T2 doesn't really like disjunctions.
    // Only call it with a formula purely made of AND-s.    
    let rho_disjs = Formula.polyhedra_dnf rho |> Formula.split_disjunction
    let result = ref truec
    let constraints = ref []

    for r in rho_disjs do
        let (formula, constr, _, _) = (pre_synth (r, econd, vars))

        // a disjunction is well founded if the conjunction of its disjuncts is well founded, 
        // instead of the disjunction of its disjuncts
        result := And(formula, !result) |> Formula.polyhedra_dnf |> Formula.simplify |> Formula.clean_formula |> Filter.redundant_disjunctions
        constraints := constr@(!constraints)             


    if(not (Formula.valid (!result))) then 
        if(depth_left > 0) then

            for c_temp in !constraints do

                // We check if the constraint is not a subformula some the constraint already 
                // enforced on the formula. If that's the case, we don't use this constraint
                // for a recursive call
                let n = List.filter (fun c ->  
                                                if(c <> truec && Formula.entails (Not(c_temp)) c) then true
                                                else false

                                     ) (Formula.split_conjunction cur_constr)
                     |> List.length

                if(n = 0) then                    
                    
                    let find_new_vars =
                        let ret = ref vars
                        for v in (Formula.freevars c_temp) do
                            if (not (Map.containsKey v !ret)) then ret := Map.add(v) 0 (!ret)
                        !ret
            
                    let new_vars = find_new_vars
                    let c = Formula.clean_formula c_temp 
                    let c_unprimed = Not(c)

                    let new_constr = And(c_unprimed, cur_constr)
                    let new_econd = Or(econd, c)
                    let c = c 
                         |> Formula.alpha (fun v -> prime_var v 0) 
                         |> Not 
            
                    let new_rho = And(rho, c)
                                        
                    //printfn "\nRECURSE WITH %s\n" new_rho.pp
                    let update:formula = pre_synth_phase (new_rho, new_vars, new_constr, new_econd, (depth_left-1))

                    if (update <> truec) then result := Or(!result, update)


        else result := falsec // If we've reached the allowed recursion depth, just assume that the current formula is unsatisfiable            
    else result := truec // If the formula is valid, there are no conditions on termination
    
    !result



let get_transition_formulae pars (p : Programs.Program) err : formula*formula*Map<var,int> =

    let get_transition_number trans =
        let mutable result = -1
        for (n, t) in p.TransitionsWithIdx do
            if t = trans then result <- n
        result

    let get_transitions_number_modified tran =

        let result = ref -1
        let (n1, [l], n2) = tran
        for (n, (n1c, lc, n2c)) in p.TransitionsWithIdx do
            if(n1c = n1 && n2c = n2 && (List.contains l lc)) then result := n 

        !result

    let split trans_numb =
        let (n1, commands, n2) = p.GetTransition trans_numb
        p.RemoveTransition trans_numb

        let rec disj_trans list =
            match list with
            | [] -> ()
            | l::ls -> 
                p.AddTransition n1 [l] n2
                disj_trans ls
                
        disj_trans commands   


    let priority_concat (var_map1:Map<var, int>) (var_map2:Map<var, int>) =

        let result = ref Map.empty

        for v in var_map1.Keys do

            let r1 = Map.find v var_map1
            if(Map.containsKey v var_map2) then                
                let r2 = Map.find v var_map2
                if(r1 > r2) then result := Map.add v r1 (!result)
                else result := Map.add v r2 (!result)
            else result := Map.add v r1 (!result)

        for v in var_map2.Keys do 
            if(not (Map.containsKey v !result)) then result := Map.add v (Map.find v var_map2) !result

        !result

    let cex = find_counterexample pars p err

    let rho = ref falsec
    let tetha = ref falsec
    let vars = ref Map.empty

    match cex with
    | None -> (falsec, falsec, Map.empty)
    | Some(counterexample) -> 

        // get the number of disjuncts you will have by the end of this, by counting the things in the 
        // label list. Then split them to different transitions and run the reachability checker disabling them 
        // one by one and oring the transition functions representing the error path.
        // What about tetha though? Should be the same for each of them... 
        // Variables? Keeping the highest prime should work... 
        // See what happens if we have an if-then-else-in-an-if-then-else-in-a-loop

        let counterexample = counterexample |> List.map (fun (from,cmds,dst) -> (from, Programs.const_subst cmds, dst))

        // Remove the transitions that led to reaching the error state for the next iteration of the loop
        let transition_numb = get_transitions_number_modified (List.last counterexample |> (fun (n1, l, n2) -> (n1, [l], n2) ))
        let (_, l, _) = p.GetTransition transition_numb
        split transition_numb        

        for k in 1..(List.length l) do
            Output.print_dot_program p ("input" + (string k) + (string k) + ".dot")  

            let cex = find_counterexample pars p err
            

            match cex with
            | None -> tetha:= Or(falsec, !tetha)
                      rho := Or(falsec, !rho)
                      p.RemoveTransition (get_transition_number (List.last counterexample |> (fun (n1, l, n2) -> (n1, [l], n2) )))
                      
            | Some(counterexample) ->

                p.RemoveTransition (get_transition_number (List.last counterexample |> (fun (n1, l, n2) -> (n1, [l], n2) )))
                let (stem, cycle) = counterexample 
                                    |> find_cycle
                                    |> (fun (x,y) -> (List.map (fun (s1, l, s2) -> (s1, [l], s2)) x, List.map (fun (s1, l, s2) -> (s1, [l], s2)) y))

                let project_to_cmds path = List.concatMap (fun (_, cmds, _) -> cmds) path
                let path_invariant = Analysis.path_invariant (project_to_cmds stem) (project_to_cmds cycle)

                let cycle = (-1, [Programs.assume path_invariant], -1)::cycle         

                let (r, v) = Symex.path_to_transitions_and_var_map cycle Map.empty
                let update_rho = r
                              |> List.concatMap (fun (_, f, _) -> f) 
                              |> List.filter (fun f -> not(Formula.contains_instr_var f) && not(Formula.contains_fair_var f)) 
                              |> Formula.conj

                rho := Or(update_rho, !rho)

                //tetha should stay the same on each iteration
                tetha := stem 
                      |> Symex.path_to_formulae 
                      |> List.concatMap (fun (_, f, _) -> f) 
                      |> List.filter (fun f -> not(Formula.contains_instr_var f) && not(Formula.contains_fair_var f)) 
                      |> Formula.conj
                      |> Formula.simplify

                vars := priority_concat !vars v

        tetha := Formula.simplify !tetha
        rho := Formula.simplify !rho
        (!tetha, !rho, !vars)


/// Finds conditions for proper termination (C) of a given branch 
/// and conditions for branch change (B). Returns list of tuples (c,b)
let find_classified_conditions (rho, vars, econd, depth_left) =

    let pre_synth_initial r =
 
        let result_proper = ref truec
        let result_branch = ref truec
        let constraints_proper = ref []
        let constraints_branch = ref []

        
        let (cond_proper, constr_proper, cond_branch, constr_branch) = (pre_synth (r, econd, vars))

        result_proper := And(cond_proper, !result_proper) |> Formula.polyhedra_dnf |> Formula.simplify |> Formula.clean_formula |> Filter.redundant_disjunctions
        result_branch := And(cond_branch, !result_branch) |> Formula.polyhedra_dnf |> Formula.simplify |> Formula.clean_formula |> Filter.redundant_disjunctions
        constraints_proper := constr_proper@(!constraints_proper)
        constraints_branch := constr_branch@(!constraints_branch)          

        if(not (Formula.valid (!result_proper))) then 

            for c_temp in !constraints_proper do

                let find_new_vars =
                    let ret = ref vars
                    for v in (Formula.freevars c_temp) do
                        if (not (Map.containsKey v !ret)) then ret := Map.add(v) 0 (!ret)
                    !ret
            
                let new_vars = find_new_vars
                let c = Formula.clean_formula c_temp 
                let c_unprimed = Not(c)

                let new_constr = c_unprimed
                let econd_refinment = Formula.split_conjunction c |> Formula.disj
                let new_econd = Or(econd, econd_refinment) 
                let c = c 
                        |> Formula.alpha (fun v -> prime_var v 0) 
                        |> Not 
            
                let new_rho = And(r, c)
                                        
                //printfn "\nINITIAL CALL: %s\n" new_rho.pp
                let update:formula = pre_synth_phase (new_rho, new_vars, new_constr, new_econd, (depth_left-1))

                if (update <> truec) then result_proper := Or(!result_proper, update)

        //***************************************************************************************************************************//
            for c_temp in !constraints_branch do

                let find_new_vars =
                    let ret = ref vars
                    for v in (Formula.freevars c_temp) do
                        if (not (Map.containsKey v !ret)) then ret := Map.add(v) 0 (!ret)
                    !ret
            
                let new_vars = find_new_vars
                let c = Formula.clean_formula c_temp 
                let c_unprimed = Not(c)

                let new_constr = c_unprimed
                let econd_refinment = Formula.split_conjunction c |> Formula.disj
                let new_econd = Or(econd, econd_refinment) 
                let c = c 
                        |> Formula.alpha (fun v -> prime_var v 0) 
                        |> Not 
            
                let new_rho = And(r, c)
                                        
                //printfn "\nINITIAL CALL BRANCH: %s\n" new_rho.pp
                let update:formula = pre_synth_phase (new_rho, new_vars, new_constr, new_econd, (depth_left-1))

                if (update <> truec) then result_branch := Or(!result_branch, update)
                           
        else
            result_proper := truec // If the formula is valid, there are no conditions on termination
            result_branch := falsec

        result_proper := !result_proper
                      |> Formula.simplify
                      |> Filter.redundant_conjunction
                      |> Filter.redundant_disjunctions

        result_branch := !result_branch
                |> Formula.simplify
                |> Filter.redundant_conjunction
                |> Filter.redundant_disjunctions


        //printfn "final return c: %s\nb: %s" (!result_proper).pp (!result_branch).pp
        (!result_proper, !result_branch)



    let rec find trans_rel acc = 
        match trans_rel with
        | [] -> acc
        | r::list -> find list (pre_synth_initial(r)::acc)    

    find (Formula.split_disjunction rho) []      

/// Builds a formula describing the conditions for termination
/// from list of tuples (c, b)
let build_condition classified = 

    let rec build conds (acc:formula) =
        match conds with 
        | [] -> acc
        | (c:formula, b:formula)::list -> 
                build list (Or(And(c, acc), And(b, acc)) |> Formula.polyhedra_dnf |> Formula.simplify)

    let bs = List.fold (fun acc (c, b) -> And(acc, b)) truec classified


    And(build classified truec, Not(bs)) |> Formula.simplify 


let run pars (p : Programs.Program) =

    //the negation of ExCond actually
    let find_exit_conditions rho vars =        

        let rho_disjs = Formula.polyhedra_dnf rho |> Formula.split_disjunction

        seq{
            for d in rho_disjs do
                yield formula_qelim vars d
           }
        |> Seq.map Not
        |> Formula.conj
        |> Formula.polyhedra_dnf
        |> Formula.split_disjunction
        |> Seq.filter (fun f ->
                            if(Formula.unsat f) then false
                            else true 
                        )
        |> Formula.disj
        |> Filter.redundant_conjunction
        |> Formula.simplify


    Output.print_dot_program p "input.dot"
    let conditions = ref falsec
    let precond = ref falsec
    let (p_work, err) = instrument p !precond    
    let number_of_pred = p.TransitionsTo err |> Seq.length

    if(number_of_pred = 0) then conditions := truec

    let p_ref = ref p_work

    for j in 1.. (number_of_pred) do
        
        Output.print_dot_program !p_ref ("input" + (string j) + ".dot") 

        let (tetha, rho, vars) = get_transition_formulae pars !p_ref err

        printfn "\n\nTETHA: %s\nRHO: %s" tetha.pp rho.pp
        printfn "EXIT CONDITIONS: %s" (find_exit_conditions rho vars).pp

        let econd = find_exit_conditions rho vars

        let cond = find_classified_conditions (rho, vars, econd, 3)
                |> build_condition

        // We need to take the conjunction of pre_synth_phase's result and 
        // the initial conditions for the respective path, to make sure we
        // "took the right turn in the program" 
        conditions := Or(And(tetha, cond), !conditions)
        
                     
     
    printfn "*************************************************\n"
    conditions := !conditions |> Formula.polyhedra_dnf |> Formula.simplify |> Formula.clean_formula |> Filter.redundant_disjunctions |> Filter.redundant_conjunction

    if (Formula.valid !conditions) then printfn "The program always terminates"
    elif (Formula.unsat !conditions) then printfn "The program does not terminate"
    else printfn "The program terminates if the following condition holds:\n%s" (!conditions).pp
        
                     

    



