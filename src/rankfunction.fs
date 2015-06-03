////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      rankfunction.fs
//
//  Abstract:
//
//      Rank function synthesis based on Farkas lemma
//
//  Notes:
//
//      * In comparison to interpolation, speed is not really very important here.
//      * See the "Note on iterative strengthening" in interpolation.fs.  I'm using the
//        same approach here, except in the other direction (e.g. "x" is judged to be a better
//        ranking function than "x+y+z"
//      * We can generate single ranking functions, lexicographic ranking functions, and lexicographic polyranking functions.
//      * There are two optimisations: fewer_rfs and max_unaffect, which are for lexicographic ranking functions only.
//        You can't have both on at once.
//      * Note that polyranking functions have constants within the function and the bound is always zero
//      * All the Farkas Lemma constraints are labelled as in "A Complete Method for the Synthesis of Lienar Ranking Functions"
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


module Microsoft.Research.T2.Rankfunction

open Z
open Utils
open SparseLinear

let ONE_var = SparseLinear.ONE

/// Generates the constraints to find a linear rf for rel
let make_decr_and_bnded_constraints rel (rf_diff: Map<Var.var,Microsoft.Z3.ArithExpr>) (rf_on_pre: Map<Var.var,Microsoft.Z3.ArithExpr>) bound =
    [
        let ZERO = Z.constantInt 0
        let prevars = Relation.prevars rel
        let postvars = Relation.postvars rel
        let ts = Relation.relation_to_linear_terms rel |> SparseLinear.simplify_as_inequalities

        let lambdas1 = Z.fresh_var_list ts.Length
        let lambdas2 = Z.fresh_var_list ts.Length

        /// A*lambda1
        let bounded = SparseLinear.combine_with_z3_terms ts lambdas1
        /// A*lambda2
        let decreasing = SparseLinear.combine_with_z3_terms ts lambdas2

        // lambda1,lambda2 >= 0
        for lambda in lambdas1 @ lambdas2 do
            yield Z.ge lambda ZERO

        // lambda1*A=-r, lambda1*A'=0
        for var in prevars @ postvars do
            yield Z.eq (bounded.FindWithDefault var ZERO) (Z.neg (rf_on_pre.FindWithDefault var ZERO))

        // lambda2*A=-r, lambda2*A'=r
        for var in prevars @ postvars do
            yield Z.eq (decreasing.FindWithDefault var ZERO) (rf_diff.FindWithDefault var ZERO)

        // -lambda2*b>0
        yield Z.gt (decreasing.FindWithDefault ONE_var ZERO) ZERO

        // -bound=-lambda1*b. This is an assignment more than a constraint
        yield Z.eq (Z.neg bound) (bounded.FindWithDefault ONE_var ZERO)
    ] |> Z.conj

/// Takes a relation between program points k, k' and generates constraints that it is not increasing when using the (symbolic) rank functions for k, k' that are stored in mu.[lex_pos]
/// Returns a pair of the variable that holds the decrease (constrained to be non-negative -- for strict decrease, ask for it to be positive) and the constraints.
let generate_weakly_decreasing_constraints_for_rel
    (k : int)
    (rel : Relation.relation)
    (rel_as_linterm : LinearTerm list)
    (k' : int)
    (lex_pos : int)
    (mu : Map<int, Map<int, Map<Var.var, Microsoft.Z3.IntExpr>>>) =
        let decrease_var = Z.fresh_var "decrease"
        let rel_strict_decrease_var = Z.fresh_bool_var "strict"
        let constraints =
            [
                let ZERO = Z.constantInt 0 :?> Microsoft.Z3.IntExpr
                let mu_k = mu.[lex_pos].[k]
                let mu_k' = mu.[lex_pos].[k']
                let prevars = Relation.prevars rel
                let postvars = Relation.postvars rel

                let lambdas2 = Z.fresh_var_list rel_as_linterm.Length

                // lambda2 >= 0
                for lambda in lambdas2 do
                    yield Z.ge lambda ZERO

                // lambda2 * A
                let decreasing = SparseLinear.combine_with_z3_terms rel_as_linterm lambdas2
                //Printf.printfn "lambda2_%A * A_%A: %A"  i i decreasing

                // lambda2_i * A_i = mu_k
                for var in prevars do
                    yield Z.eq (decreasing.FindWithDefault var ZERO) (mu_k.FindWithDefault var ZERO)

                // lambda2_i * A_i' = -mu_k'
                for var in postvars do
                    //Here we have to use a trick: We need to unprime the variable and turn it into a prevar (because the mus are defined as maps of the prevars)
                    let prevar_for_postvar = Var.prime_var (Var.unprime_var var) 0
                    yield Z.eq (decreasing.FindWithDefault var ZERO) (Z.neg (mu_k'.FindWithDefault prevar_for_postvar ZERO))

                // lambda2_i * b_i = e_i >= 0
                yield (Z.eq (decreasing.FindWithDefault ONE_var ZERO) decrease_var)
                yield (Z.ge decrease_var ZERO)
                yield Z.z3Context.MkEq (rel_strict_decrease_var, Z.gt decrease_var ZERO)
            ] |> Z.conj
        (rel_strict_decrease_var, constraints)

/// Takes a relation between program points k, k' and generates constraints that it is bounded when using the (symbolic) rank function for k that is stored in mu.[lex_pos].
/// Returns a pair of the variable that is equivalent to boundedness in a model and the constraints
let generate_bounded_constraints_for_rel
    (k : int)
    (rel : Relation.relation)
    (rel_as_linterm : LinearTerm list)
    (lex_pos : int)
    (mu : Map<int, Map<int, Map<Var.var, Microsoft.Z3.IntExpr>>>) =
        let ZERO = Z.constantInt 0 :?> Microsoft.Z3.IntExpr
        let mu_k = mu.[lex_pos].[k]
        let prevars = Relation.prevars rel
        let postvars = Relation.postvars rel

        let lambdas1 = Z.fresh_var_list rel_as_linterm.Length

        // lambda1_i * A_i
        let bounded = SparseLinear.combine_with_z3_terms rel_as_linterm lambdas1
        //Printf.printfn "lambda * A: %A" bounded

        let rel_bounded_var = Z.fresh_bool_var "bounded"
        let rel_bound_var = Z.fresh_var "bound"

        // Set trans_decreasing_and_bounded_var to 1 if and only if the corresponding transition is bounded
        let constraints =
            Z.z3Context.MkEq (rel_bounded_var,
                Z.conj [
                    // lambda1_i >= 0
                    for lambda in lambdas1 do
                        yield Z.ge lambda ZERO

                    // lambda1_i * A_i = mu_k
                    for var in prevars do
                        yield Z.eq (bounded.FindWithDefault var ZERO) (mu_k.FindWithDefault var ZERO)

                    // lambda1_i * A_i' = 0
                    for var in postvars do
                        yield Z.eq (bounded.FindWithDefault var ZERO) ZERO

                    // -bound=-lambda1*b. This is an assignment more than a constraint
                    yield Z.eq (Z.neg rel_bound_var) (bounded.FindWithDefault ONE_var ZERO)
                ])
        (rel_bounded_var, rel_bound_var, constraints)

///Takes a map mu describing several symbolic ranking functions and a model for the corresponding formula and spits out an instantiated ranking function
let extract_rf_from_model mu m =
       mu
    |> Map.map
        (fun _ mu_k ->
                mu_k
             |> Map.map (fun _ coeffVar -> -(Z.get_model_int m coeffVar))
             |> Map.filter (fun _ coeff -> coeff <> bigint.Zero))

///
/// Return pair (rf, bound), where ref is term in prevars, and bound is consant term.
/// RF should be always >= bound.
///
let synthesis rel =

    //printfn "rel: %A" rel

    let prevars = Relation.prevars rel
    let postvars = Relation.postvars rel

    assert (prevars.Length = postvars.Length)
    assert ((Set.intersect (Set.ofList prevars) (Set.ofList postvars)).IsEmpty)

    let rf_coeffs = Z.fresh_var_list prevars.Length
    let rf_on_pre = List.zip prevars rf_coeffs |> Map.ofSeq
    let rf_on_post = List.zip postvars rf_coeffs |> Map.ofSeq

    // rf_on_post minus rf_on_pre
    let rf_diff =
        [for KeyValue(v, k) in rf_on_post -> (v, k)] @
        [for KeyValue(v, k) in rf_on_pre -> (v, Z.neg k)] |> Map.ofSeq

    let bound = Z.fresh_var()

    let constraints = make_decr_and_bnded_constraints rel rf_diff rf_on_pre bound

    //  See the "Note on iterative strengthening" in interpolation.fs.
    //  Here in this instance we assume that "x" makes a better ranking function than
    //  "x+y" when given the choice. This is in contrast to interpolation where "x<y" is judged to be better
    //  than "x<0"
    let var_count vars =
        let n0 = Z.constantInt 0
        let n1 = Z.constantInt 1
        List.fold Z.add n0
            [for var in vars do
                yield (Z.ite (Z.neq n0 var) n1 n0 :?> Microsoft.Z3.ArithExpr) ]
    let n_used = var_count [for KeyValue(v, k) in rf_on_pre do if v <> ONE_var then yield k]
    let n_less_than m = Z.le n_used (Z.constantInt m)
    let strengthenings = List.map n_less_than [3; 2; 1]

    match Z.solve (constraints::strengthenings) with
    | None -> None
    | Some m ->
        let rf_on_pre = Map.map (fun _ coeff -> Z.get_model_int m coeff) rf_on_pre |> linear_term_to_term
        let bound = Term.Const -(Z.get_model_int m bound)

        m.Dispose()

        Some (rf_on_pre, bound)

(* LEXICOGRAPHIC RFS *)

//(relation, rf, bound) list
type Lex_RF = (Relation.relation * Term.term * Term.term) list
//A list of possible lex rfs we found, or a list of transitions that can be removed from the program
type Lex_Synthesis_Result =   Lexoptions of Lex_RF list
                            | Program_Simplification of int list

let make_symbolic_rf vars = Map.ofSeq (vars |> Seq.map (fun v -> (v, Z.fresh_var v)))

/// construct mu_k for every program point k, where every prevar gets a coefficient, for a number of lex ranking functions:
let construct_mu lex_rf_length program_points_to_consider vars =
    let mu : Map<int, Map<int, Map<Var.var, Microsoft.Z3.IntExpr>>> =
        [for lex_pos in 0 .. lex_rf_length do
            let mu_at_lex_pos =
               program_points_to_consider
            |> Seq.map (fun p -> (p, make_symbolic_rf vars))
            |> Map.ofSeq
            yield (lex_pos, mu_at_lex_pos)
        ] |> Map.ofSeq
    mu

///Constructs contraints such that all prior rfs mu.[j] orient rel_i weakly
///and relation i is bounded and strictly decreasing using mu.[i]
let gen_constraints_for_lex_rf_order
    (sigma : Relation.relation list)
    (cp : int)
    (mu : Map<int, Map<int, Map<Var.var, Microsoft.Z3.IntExpr>>>)
    (linterm_for_relation : Map<Relation.relation, LinearTerm list>)
    (bound_var_for_lex_pos : Map<int, Microsoft.Z3.IntExpr> ref) =
        [
            for lex_pos in 0 .. (sigma.Length-1) do
                let rel_i = sigma.[lex_pos]
                let linterm_for_rel_i = linterm_for_relation.[rel_i]

                //For all prior rfs, this relations is weakly oriented:
                for j in 0 .. (lex_pos - 1) do
                    let (_, weak_decr_constraint) =
                        generate_weakly_decreasing_constraints_for_rel cp rel_i linterm_for_rel_i cp j mu
                    yield weak_decr_constraint

                //This one's oriented, bounded and the decrease is strict:
                let (decr_var, weak_decr_constraint) =
                    generate_weakly_decreasing_constraints_for_rel cp rel_i linterm_for_rel_i cp lex_pos mu
                let (is_bounded_var, rel_bound_var, bounded_constraint) =
                    generate_bounded_constraints_for_rel cp rel_i linterm_for_rel_i lex_pos mu
                bound_var_for_lex_pos := Map.add lex_pos rel_bound_var !bound_var_for_lex_pos
                yield weak_decr_constraint
                yield bounded_constraint
                yield Z.conj2 is_bounded_var decr_var //This ensures boundedness and strict decrease
        ] |> Z.conj

///Gives a list of all selections of k objects from input_list
///Assumes there are no duplicates in input_list
let rec combs (k:int) (input_list:'a list) =
    if k=0 then [Set.empty]
    else
        match input_list with
            | [] -> List.empty
            | head::tail -> [for comb in (combs (k-1) tail) -> (Set.add head comb)]@(combs k tail)

///For each possible insertion of rel_to_add to partial_order, try to find a lexicographic solution
let synthesis_lex_no_opt
    (rel_to_add:Relation.relation)
    (partial_order: Relation.relation list)
    (cp: int)
    (linterm_for_relation : Map<Relation.relation, LinearTerm list>) =
        let prevars = Relation.prevars rel_to_add
        let mu = construct_mu partial_order.Length [cp] prevars
        let lexoptions =
            [for lex_pos in 0..partial_order.Length do
                //insert rel_to_add into ith position:
                let sigma = (List.take lex_pos partial_order)@(rel_to_add::(List.drop lex_pos partial_order))
                let bound_var_for_lex_pos = ref Map.empty
                let constraints_for_this_lex_rf_order = gen_constraints_for_lex_rf_order sigma cp mu linterm_for_relation bound_var_for_lex_pos

                match Z.solve [constraints_for_this_lex_rf_order] with
                | None -> ()
                | Some m ->
                    let rf_lex = [for i in 0 .. (sigma.Length - 1) do
                                        let rel = sigma.[i]
                                        let rf = (extract_rf_from_model mu.[i] m).[cp] |> SparseLinear.linear_term_to_term
                                        let bnd = Term.Const -(Z.get_model_int m (!bound_var_for_lex_pos).[i])
                                        yield (rel, rf, bnd)]
                    m.Dispose()
                    yield rf_lex
            ]
        Lexoptions lexoptions

///For each possible insertion of rel_to_add to partial_order, try to find a lexicographic solution. Order results such that solutions with more unaffected relations are preferred
let synthesis_lex_max_unaff
    (rel_to_add:Relation.relation)
    (partial_order: Relation.relation list)
    (cp: int)
    (linterm_for_relation : Map<Relation.relation, LinearTerm list>) =
        let prevars = Relation.prevars rel_to_add
        let mu = construct_mu partial_order.Length [cp] prevars
        let make_extra_unaffects (sigma:Relation.relation list) =
            [for i in 0 .. (sigma.Length-1) do
                let rel_i = sigma.[i] //the ith relation
                //for all j>i, jth r.f. doesn't go up via ith rel
                for j in i+1 .. (sigma.Length-1) do
                    let rel_j = sigma.[j-1]
                    let (_, weak_decr_constraint) =
                        generate_weakly_decreasing_constraints_for_rel cp rel_j linterm_for_relation.[rel_i] cp i mu
                    yield weak_decr_constraint
            ]

        ///Makes the constraint that the unaffect score is >= u
        //The unaffect score is the number of EXTRA unaffecting relation/RF pairs there are
        //The maximum score is (((n-1)*n)/2)
        let make_unaffect_ge (u:int) (sigma:Relation.relation list) =
            let extra_unaffects = make_extra_unaffects sigma
            let n = sigma.Length
            assert ((extra_unaffects.Length) = ((n-1)*n)/2)

            // Ways to choose u of the extra_unaffects
            let poss_combs = combs u extra_unaffects |> List.map List.ofSeq |> List.map Z.conj

            Z.disj poss_combs

        //For each possible insertion of rel_to_add to partial_order, try to find a lexicographic solution with highest possible unaffect score
        [for lex_pos in 0..partial_order.Length do
            //insert rel_to_add into ith position:
            let sigma = (List.take lex_pos partial_order)@(rel_to_add::(List.drop lex_pos partial_order))
            let n = sigma.Length

            //start with the highest possible unaffect score
            let u = ref (((n-1)*n)/2)
            let finished = ref false

            while not !finished do
                //try to find a solution with an unaffect score >=u
                let U_ge = make_unaffect_ge !u sigma
                let bound_var_for_lex_pos = ref Map.empty
                let constraints_for_this_lex_rf_order = gen_constraints_for_lex_rf_order sigma cp mu linterm_for_relation bound_var_for_lex_pos
                let allconstraints = Z.conj[constraints_for_this_lex_rf_order;U_ge]

                match Z.solve [allconstraints] with
                //if no soln for this u, decrease u and try again, unless we've reached 0, in which case give up
                | None -> if !u > 0 then decr u
                                    else finished := true
                //if a soln is found, return it
                | Some m ->
                        let rf_lex = [for i in 0 .. (sigma.Length - 1) do
                                            let rel = sigma.[i]
                                            let rf = (extract_rf_from_model mu.[i] m).[cp] |> SparseLinear.linear_term_to_term
                                            let bnd = Term.Const -(Z.get_model_int m (!bound_var_for_lex_pos).[i])
                                            yield (rel, rf, bnd)]
                        m.Dispose()
                        finished := true
                        yield (rf_lex,!u)
        ]|> List.sortBy (fun (_, u)-> -u) //sorts the lexoptions by having the highest unaffecting score first
         |> List.map (fun (x, _) -> x) //drop the score again
         |> Lexoptions

///For each possible insertion of rel_to_add to partial_order, try to find a lexicographic solution. Minimize the number of used rfs in that.
let synthesis_lex_min_rfs
    (rel_to_add:Relation.relation)
    (partial_order: Relation.relation list)
    (cp: int)
    (linterm_for_relation : Map<Relation.relation, LinearTerm list>) =
        let prevars = Relation.prevars rel_to_add
        let mu = construct_mu partial_order.Length [cp] prevars

        ///Creates the constraint that means that there are k or fewer RFs used
        let equal_to_k_rfs (k:int) =
            [
                let dummy_rfs = [ for _ in 1..k do yield make_symbolic_rf prevars ]

                //takes a RF map and extracts the list of Z3 coefficients
                let rf_map_to_Z3_list (rf:Map<Var.var,Microsoft.Z3.IntExpr>) =
                    let (_,rf_list) = List.unzip (Map.toList rf)
                    rf_list

                //takes two RF maps and creates the Z3 term that means they are equal
                let rfs_equal rf_map1 rf_map2 =
                    let rf_list1 = rf_map_to_Z3_list rf_map1
                    let rf_list2 = rf_map_to_Z3_list rf_map2
                    assert (rf_list1.Length = rf_list2.Length)
                    [for i in 1..rf_list1.Length -> Z.eq rf_list1.[i-1] rf_list2.[i-1]] |> Z.conj

                //for each relation, require that its RF is equal to one of the k dummy RFs
                yield [
                    for i in 0 .. partial_order.Length do
                        let rel_i_rf = mu.[i].[cp]
                        let dummy_rf = dummy_rfs.[i-1]
                        yield rfs_equal rel_i_rf dummy_rf
                ] |> Z.disj
            ] |> Z.conj

        //For each possible insertion of rel_to_add to partial_order, try to find a lexicographic solution using the fewest functions
        [for lex_pos in 0..partial_order.Length do
            //insert rel_to_add into ith position:
            let sigma = (List.take lex_pos partial_order)@(rel_to_add::(List.drop lex_pos partial_order))

            let k = ref 1
            let finished = ref false
            //search for shorter solutions, taking the shortest one
            while (!k <= sigma.Length) && (!finished = false) do
                let bound_var_for_lex_pos = ref Map.empty
                let constraints_for_this_lex_rf_order = gen_constraints_for_lex_rf_order sigma cp mu linterm_for_relation bound_var_for_lex_pos
                let allconstraints = Z.conj[constraints_for_this_lex_rf_order;(equal_to_k_rfs !k)] //require lex soln for this sigma, plus k or fewer RFs used
                match Z.solve [allconstraints] with
                | None -> ()
                | Some m -> //If there is a solution of length k:
                        let rf_lex = [for i in 0 .. (sigma.Length - 1) do
                                            let rel = sigma.[i]
                                            let rf = (extract_rf_from_model mu.[i] m).[cp] |> SparseLinear.linear_term_to_term
                                            let bnd = Term.Const -(Z.get_model_int m (!bound_var_for_lex_pos).[i])
                                            yield (rel, rf, bnd)]
                        m.Dispose()
                        finished := true
                        yield (rf_lex,!k)
                incr k
        ]|> List.sortBy (fun (_,k) -> k) //sorts the lexoptions by having the shortest lex rfs first
         |> List.map (fun (x,_) -> x) //drop the length
         |> Lexoptions

let node_numbering (nodes: Set<int>) =
    let ONE = Z.constantInt 1
    let MAXNUM = Z.constantInt (nodes.Count)
    let node_num_map = ref Map.empty
    let node_num_constr =
        [ for pp in nodes do
            let num = Z.fresh_var "num"
            node_num_map := Map.add pp num !node_num_map
            yield Z.ge num ONE
            yield Z.le num MAXNUM
        ]
    (node_num_constr, !node_num_map)

let get_simplified_linterm_cache (rels : seq<'a * 'b * Relation.relation * 'c>) =
    rels
    |> Seq.map (fun (_, _, rel, _) -> (rel, rel |> Relation.relation_to_linear_terms |> SparseLinear.simplify_as_inequalities))
    |> Map.ofSeq

let build_scc_constraints (pars : Parameters.parameters) transitions mu add_bound_constraints (rel_to_simplified_linterm_cache : Map<Relation.relation, LinearTerm list>) =
    let decreasing_and_bounded_var_for_transition = ref Map.empty
    let bound_var_for_transition = ref Map.empty
    let decreasing_var_for_transition = ref Map.empty
    let bounded_var_for_transition = ref Map.empty
    let decr_constraints =
        [ for (i, k, rel, k') in transitions do
            let rel_as_linterm = rel_to_simplified_linterm_cache.[rel]

            let (decreasing_var, decrease_constraints) = generate_weakly_decreasing_constraints_for_rel k rel rel_as_linterm k' 0 mu
            decreasing_var_for_transition := Map.add i decreasing_var !decreasing_var_for_transition
            yield decrease_constraints
        ]

    if add_bound_constraints then
        let bound_constraints =
            [ for (i, k, rel, _) in transitions do
                let rel_as_linterm = rel_to_simplified_linterm_cache.[rel]
                let (bounded_var, bound_var, bounded_constraints) = generate_bounded_constraints_for_rel k rel rel_as_linterm 0 mu
                bounded_var_for_transition := Map.add i bounded_var !bounded_var_for_transition
                bound_var_for_transition := Map.add i bound_var !bound_var_for_transition
                yield bounded_constraints
            ]

        let trans_decr_and_bounded_constraints =
            if pars.mcnp_style_bound_decr then
                //Implement bounded/decreasing split from Lemma 31 in "SAT-Based Termination Analysis Using Monotonicity Constraints over the Integers" (TPLP)
                let all_pp = transitions |> Seq.map (fun (_, k, _, k') -> [k; k']) |> List.concat |> Set.ofList
                [
                    //Generate #_D (#_S in the paper), #_B id for each program point, add constraints
                    let (d_num_constraints, d_num_map) = node_numbering all_pp
                    let (b_num_constraints, b_num_map) = node_numbering all_pp
                    yield! d_num_constraints
                    yield! b_num_constraints

                    //Enforce compatibility of node numbering, set variable if delta on node numberings is non-null
                    let ZERO = Z.constantInt 0
                    for (i, k, _, k') in transitions do
                        let decreasing_var = (!decreasing_var_for_transition).[i]
                        let bounded_var = (!bounded_var_for_transition).[i]
                        let rel_strict_decrease_and_bounded_var = Z.fresh_bool_var "bounded_and_decr"
                        decreasing_and_bounded_var_for_transition := Map.add i rel_strict_decrease_and_bounded_var !decreasing_and_bounded_var_for_transition

                        yield Z.implies (Z.gt (d_num_map).[k'] (d_num_map).[k]) decreasing_var
                        yield Z.implies (Z.gt (b_num_map).[k'] (b_num_map).[k]) bounded_var

                        let locally_decr_and_bounded = Z.conj2 decreasing_var bounded_var
                        let d_diff_nonnull = Z.mk_not <| Z.eq (Z.add (d_num_map).[k'] (Z.neg (d_num_map).[k])) ZERO // not(#_D(k') - #_D(k) = 0)
                        let b_diff_nonnull = Z.mk_not <| Z.eq (Z.add (b_num_map).[k'] (Z.neg (b_num_map).[k])) ZERO // not(#_B(k') - #_B(k) = 0)
                        let globally_decr_and_bounded = Z.conj2 d_diff_nonnull b_diff_nonnull
                        yield Z.z3Context.MkEq(rel_strict_decrease_and_bounded_var, Z.disj2 locally_decr_and_bounded globally_decr_and_bounded)
                ]
            else
                [ for (i, _, _, _) in transitions do
                    let decreasing_var = (!decreasing_var_for_transition).[i]
                    let bounded_var = (!bounded_var_for_transition).[i]
                    let rel_strict_decrease_and_bounded_var = Z.fresh_bool_var "bounded_and_decr"
                    decreasing_and_bounded_var_for_transition := Map.add i rel_strict_decrease_and_bounded_var !decreasing_and_bounded_var_for_transition
                    yield Z.z3Context.MkEq(rel_strict_decrease_and_bounded_var, (Z.conj2 decreasing_var bounded_var))
                ]
        ([decr_constraints; bound_constraints; trans_decr_and_bounded_constraints] |> List.concat |> Z.conj, !decreasing_and_bounded_var_for_transition, !bound_var_for_transition)
    else
        (Z.conj decr_constraints, !decreasing_and_bounded_var_for_transition, !bound_var_for_transition)

///Try to find a lex rf such that all SCC transitions are unaffected and the cex is decreasing. Then find out what part of the SCC might be deleted.
let synthesis_lex_scc_trans_unaffected
    (pars : Parameters.parameters)
    (p:Programs.Program)
    (p_sccs: Map<int, Set<int>>)
    (rel_to_add:Relation.relation)
    (partial_order: Relation.relation list)
    (cp: int)
    (linterm_for_relation : Map<Relation.relation, LinearTerm list>) =
        //Get all transitions in the considered SCC, clean them up a bit:
        let loops_containing_cp = p_sccs |> Map.filter (fun _ ns -> ns.Contains cp) |> Map.toList
        if loops_containing_cp.IsEmpty then
            synthesis_lex_no_opt rel_to_add partial_order cp linterm_for_relation
        else
        let (_, scc_nodes) = loops_containing_cp.Head
        let (scc_vars, _, scc_rels) = Symex.get_scc_rels_for_lex_rf_synth_from_program pars p scc_nodes cp

        //Now construct a set of ranking functions for all considered states such that everything's weakly oriented and we are strictly oriented:
        let cleaned_scc_nodes = [ for (_, k, _, k') in scc_rels do yield! [k; k'] ] |> Set.ofList
        let all_vars = Set.union (scc_vars |> Set.map (fun v -> Var.prime_var v 0)) (Relation.prevars rel_to_add |> Set.ofSeq)
        let mu = construct_mu 0 cleaned_scc_nodes all_vars

        /// These constraints ensure that every transition is not increasing
        let (all_transitions_weakly_decreasing, decreasing_and_bounded_var_for_transition, _) = build_scc_constraints pars scc_rels mu false (get_simplified_linterm_cache scc_rels)

        //Now enforce that the new relation is strictly oriented and feed everything to the SMT solver:
        let extra_pre_var : Var.var = Var.var (Formula.const_var bigint.One + "^0")
        let extra_post_var : Var.var = Var.var (Formula.const_var bigint.One + "^post")
        let rel_to_add' = Programs.add_const1_var_to_relation extra_pre_var extra_post_var rel_to_add
        let linterm_for_rel_to_add' = rel_to_add' |> Relation.relation_to_linear_terms |> SparseLinear.simplify_as_inequalities
        let (decreasing_var, decrease_constraints) = generate_weakly_decreasing_constraints_for_rel cp rel_to_add' linterm_for_rel_to_add' cp 0 mu
        let (bounded_var, bound_var, bounded_constraints) = generate_bounded_constraints_for_rel cp rel_to_add' linterm_for_rel_to_add' 0 mu
        let trans_strict_and_bounded = decreasing_and_bounded_var_for_transition.Items |> Seq.map (fun (_, var) -> var) |> List.ofSeq
        let at_least_one_trans_strict_bounded = Z.disj trans_strict_and_bounded
        let all_constraints = Z.conj [decreasing_var; bounded_var; all_transitions_weakly_decreasing; decrease_constraints; bounded_constraints]

        //printfn "All constraints:\n%A" all_constraints

        //Check out if all of that works (second constraint is optional heuristic, asking the SMT solver nicely for a solution that allows to remove a transition):
        match Z.solve [ all_constraints ; at_least_one_trans_strict_bounded ] with
            | None ->
                //fall back to standard thing:
                synthesis_lex_no_opt rel_to_add partial_order cp linterm_for_relation
            | Some m ->
                //Party! Check if we can even remove transitions:
                let trans_to_delete =
                       decreasing_and_bounded_var_for_transition
                    |> Map.filter (fun _ v -> match (Z.get_model_bool_opt m v) with
                                                | Some(true) -> true
                                                | _          -> false)
                    |> Map.toList
                    |> List.map (fun (k, _) -> k)

                if List.isEmpty trans_to_delete then
                    //Oh well. No transition could be shown to decrease and be bounded (but everything is weakly oriented):
                    let rfs = extract_rf_from_model mu.[0] m
                    let rf = rfs.[cp] |> SparseLinear.linear_term_to_term |> Term.subst (fun v -> if v = extra_pre_var then Term.constant 1 else Term.var v)
                    let bnd = Term.Const -(Z.get_model_int m bound_var)
                    m.Dispose()

                    if partial_order.IsEmpty then
                        Lexoptions [[(rel_to_add, rf, bnd)]]
                    else
                        //Now we need to regenerate a solution for the rest again, because we don't keep this around... (this is a TODO)
                        let rest_res = synthesis_lex_no_opt partial_order.Head partial_order.Tail cp linterm_for_relation
                        match rest_res with
                        | Lexoptions(lexoptions) -> Lexoptions(List.map (fun rest_sol -> (rel_to_add, rf, bnd)::rest_sol) lexoptions)
                        | Program_Simplification(_) -> assert(false); rest_res //the no_opt synth should never return a program simplification!

                else
                    m.Dispose()
                    Program_Simplification(trans_to_delete |> List.map (fun s -> List.ofSeq s) |> List.concat)

/// Tries to find a lexicographic ranking function with rel_to_add inserted into partial_order.
/// Returns None or a list of Lex_RF.
/// Note partial_order will be empty initially
let synthesis_lex (pars : Parameters.parameters) (p:Programs.Program) (p_sccs: Map<int, Set<int>>) (cp: int) (rel_to_add':Relation.relation) (partial_order': Relation.relation list) =
    let rel_to_add = Relation.standardise_postvars rel_to_add'
    let partial_order = List.map Relation.standardise_postvars partial_order'

    //NOTE: If rel_to_add is already in partial_order, then it shouldn't have been found
    //We often get bugs turning up here due to something going wrong elsewhere, like finding unsat path invariants, or finding a path but detecting the wrong CP for it.
    assert not(List.contains rel_to_add partial_order)

    /// Cache for linterms, to avoid computing them four times. I promise, they'll not change in the next 20 lines...
    let linterm_for_relation =
           rel_to_add::partial_order
        |> Seq.map (fun rel -> (rel, Relation.relation_to_linear_terms rel |> SparseLinear.simplify_as_inequalities))
        |> Map.ofSeq

    let synth_res =
        if pars.lex_opt_fewer_rfs then
            synthesis_lex_min_rfs rel_to_add partial_order cp linterm_for_relation

        else if pars.lex_opt_max_unaffect then
            synthesis_lex_max_unaff rel_to_add partial_order cp linterm_for_relation

        else if pars.lex_opt_scc_unaffected then
            synthesis_lex_scc_trans_unaffected pars p p_sccs rel_to_add partial_order cp linterm_for_relation

        else
            synthesis_lex_no_opt rel_to_add partial_order cp linterm_for_relation

    match synth_res with
        | Lexoptions (_::_)        -> Some synth_res
        | Program_Simplification _ -> Some synth_res
        | _                        -> None

/// Given a list of transition as (transitionIdx, fromPC, relation, toPC), this tries to find a lexicographic
/// ranking function that maximizes the number of strictly decreasing and bound transitions and ensures that
/// all others are unaffected (corresponding to the DepPair approach). 
/// It returns a list of the used rank functions and bounds, and a set of transitions that were strictly
/// oriented, allowing to remove them from the instrumented program copy.
let rec synth_maximal_lex_rf (pars : Parameters.parameters) (loop_transitions : seq<Set<int> * int * Relation.relation * int>) (rel_to_simplified_linterm_cache : Map<Relation.relation, LinearTerm list>) =
    /// points for which we need to generate a measurement
    let program_points = Set.ofSeq [ for (_, in_pc, _, out_pc) in loop_transitions do yield in_pc; yield out_pc ]

    /// all variables we are looking at
    let all_prevars : Set<Var.var> =
           loop_transitions
        |> Seq.map (fun (_, _, rel, _) -> Relation.prevars rel)
        |> Seq.concat
        |> Set.ofSeq

    /// mu_k for every program point k, where every prevar gets a coefficient
    let mu = construct_mu 0 (List.ofSeq program_points) all_prevars
    let (all_enriched_transitions_weakly_decreasing, trans_decreasing_and_bounded, bound_var_for_transition) =
        build_scc_constraints pars loop_transitions mu true rel_to_simplified_linterm_cache

    /// This enforces that at least one transition is strictly decreasing and bounded:
    let at_least_one_strictly_decreasing_and_bounded = trans_decreasing_and_bounded.Items |> Seq.map (fun (_, var) -> var) |> List.ofSeq
    // Now go off and find something (ensure everything is non-increasing, at least one strictly decreasing and bounded):
    match Z.solve [Z.conj2 all_enriched_transitions_weakly_decreasing (Z.disj at_least_one_strictly_decreasing_and_bounded)] with
        | None -> None
        | Some m ->
            let strictly_decreasing_and_bounded : Set<Set<int>> =
                trans_decreasing_and_bounded
             |> Map.filter (fun _ var ->
                                match Z.get_model_bool_opt m var with
                                    | None -> false
                                    | Some v -> v)
             |> Map.toSeq
             |> Seq.map (fun (trans_idx, _) -> trans_idx)
             |> Set.ofSeq

            if strictly_decreasing_and_bounded.IsEmpty then
                m.Dispose()
                None
            else
                //Now that we killed some transitions, filter them out and try again:
                let rfs = extract_rf_from_model mu.[0] m
                let bounds = 
                       strictly_decreasing_and_bounded 
                    |> Set.map (fun idx -> (idx, -(Z.get_model_int m (bound_var_for_transition).[idx]))) 
                    |> Map.ofSeq;

                m.Dispose()

                let remaining_loop_transitions =
                   loop_transitions
                |> Seq.filter (fun (idx, _, _, _) -> not (Set.contains idx strictly_decreasing_and_bounded))
                //Printf.printfn "Remaining transitions: "
                //remaining_loop_transitions |> Seq.iter (fun t -> Printf.printfn "  %A" t)

                //Recurse if we still have unsolved problems:
                if Seq.isEmpty remaining_loop_transitions then
                    Some ([(rfs, bounds)], strictly_decreasing_and_bounded)
                else
                    match synth_maximal_lex_rf pars remaining_loop_transitions rel_to_simplified_linterm_cache with
                        | None -> Some ([(rfs, bounds)], strictly_decreasing_and_bounded)
                        | Some (found_rfs, to_remove) -> Some ((rfs, bounds)::found_rfs, Set.union to_remove strictly_decreasing_and_bounded)

(* POLYRANKING LEXICOGRAPHIC RFS *)

//template function used to construct polyranking trees. Should contain prevars, postvars and ONE_var in its keys
type template_fn = Map<Var.var,Microsoft.Z3.ArithExpr>

//Holds all the template functions on which to construct the polyranking constraints.
//if type = 0, node is negative (N)
//if type = 1, node is unaffected (U)
//if type = 2, node is eventually negative (EN)
type template_tree =
    //node = index, function, type, children
    | Node of int*template_fn*(Microsoft.Z3.IntExpr)*template_tree list
    //leaf = index, function, type
    | Leaf of int*template_fn*(Microsoft.Z3.IntExpr)

//A poly_tree holds the solution RFs to the polyranking problem
//See "The Polyranking Principle" for description of EN-trees
type poly_tree =
    //N = index,function
    | N of int*Term.term
    //EN = index,function,children
    | EN of int*Term.term*poly_tree list
    //U = index
    | U of int

//A lexicographic polyranking function consists of the order of the relations,
//and a tree for each relation
type Lex_Poly_RF = Relation.relation list * poly_tree list

/// Generates constraint that rf is bounded below by zero on rel. rf contains its own constant
let make_bounded_constraints_consts rel (rf:template_fn) =
    [
        let ZERO = Z.constantInt 0 :?> Microsoft.Z3.IntExpr
        let prevars = Relation.prevars rel
        let postvars = Relation.postvars rel
        let ts = Relation.relation_to_linear_terms rel |> SparseLinear.simplify_as_inequalities

        let lambdas1 = Z.fresh_var_list ts.Length

        let bounded = SparseLinear.combine_with_z3_terms ts lambdas1

        // lambda1 >= 0
        for lambda in lambdas1 do
            yield Z.ge lambda ZERO

        // lambda1*A=-r
        for var in prevars do
            yield Z.eq (bounded.FindWithDefault var ZERO) (Z.neg (rf.FindWithDefault var ZERO))

        // lambda1*A'= 0
        for var in postvars do
            yield Z.eq (bounded.FindWithDefault var ZERO) ZERO

        // lambda*(-b) >= -const coeff of r
        let const_coeff_r = rf.FindWithDefault ONE_var ZERO
        yield Z.ge (bounded.FindWithDefault ONE_var ZERO) (Z.neg(const_coeff_r))

    ] |> Z.conj

///Generates the constraint that rf is unaffected by rel. rf contains its own constant
let make_unaffecting_constraint_consts (rel:Relation.relation) (rf:template_fn) =
    [
        let ZERO = Z.constantInt 0 :?> Microsoft.Z3.IntExpr
        let ts = Relation.relation_to_linear_terms rel |> SparseLinear.simplify_as_inequalities
        let lambdas2 = Z.fresh_var_list ts.Length

        let decreasing = SparseLinear.combine_with_z3_terms ts lambdas2

        let prevars = Relation.prevars rel
        let postvars = Relation.postvars rel

        // lambda2 >= 0
        for lambda in lambdas2 do
            yield Z.ge lambda ZERO

        //lambda2*A'=r
        for var in postvars do
            yield Z.eq (decreasing.FindWithDefault var ZERO) (rf.FindWithDefault var ZERO)

        // lambda2*A=-r
        for var in prevars do
            yield Z.eq (decreasing.FindWithDefault var ZERO) (Z.neg(rf.FindWithDefault var ZERO))

        // -lambda2*b>=0
        yield Z.ge (decreasing.FindWithDefault ONE_var ZERO) ZERO

    ] |> Z.conj

//Generate constraint: fn ISN'T a constant function, i.e. one of the coeffs for the vars other than 1 is nonZERO
let make_rf_not_const_constraint (fn:template_fn) =
    let ZERO = Z.constantInt 0
    let vars = Seq.filter (fun var-> var<>ONE_var) fn.Keys
    let fn_is_const = [for var in vars -> Z.eq fn.[var] ZERO] |> Z.conj
    Z.mk_not fn_is_const

/// Makes constraint that says the rf at the head of the tree is Eventually Negative by A in T_bar
//See "The Polyranking Principle" to see what this means
//A is the relation given by the index at the top of the tree
//t_bar_indexes give the indexes of the relations in T_bar
//sigma is the ordering of the relations
let rec make_eventually_neg_constraints (tree:template_tree) (sigma:Relation.relation list) (t_bar_indexes:int list) =

    let ZERO = Z.constantInt 0 :?> Microsoft.Z3.IntExpr
    let (index,rf,node_type,children,reached_depth) =
        match tree with
        |template_tree.Node(index,rf,node_type,children) -> (index,rf,node_type,children,false)
        |template_tree.Leaf(index,rf,node_type) -> (index,rf,node_type,[],true)

    let A = sigma.[index-1]
    assert List.contains index t_bar_indexes

    let prevars = Relation.prevars A
    let postvars = Relation.postvars A

    //now we want to generate the constraints that say:
    //rf is eventually negative by A in T_bar

    //constraint: rf is Negative on all rels in sigma
    //in which case label this node "zero" i.e. negative
    let negative =

        (Z.eq node_type ZERO)::
        [for rel in sigma do
            let ts = Relation.relation_to_linear_terms rel |> SparseLinear.simplify_as_inequalities

            let lambdas = Z.fresh_var_list ts.Length

            let neg = SparseLinear.combine_with_z3_terms ts lambdas

            //lambdas >=0
            for lambda in lambdas do
                yield Z.ge lambda ZERO

            //lambda*A=r
            for var in prevars do
                yield Z.eq (neg.FindWithDefault var ZERO) (rf.FindWithDefault var ZERO)

            //lambda*A'=0
            for var in postvars do
                yield Z.eq (neg.FindWithDefault var ZERO) ZERO

            //-lambda*b-1>=const term of r
            yield Z.ge (Z.add (neg.FindWithDefault ONE_var ZERO) (Z.constantInt -1)) (rf.FindWithDefault ONE_var ZERO)

        ] |> Z.conj

    if not(reached_depth) then

        //generates constraint: fn is Eventually Decreasing for rel
        let eventually_decreasing (fn:template_fn) (rel:Relation.relation) (aux_tree:template_tree)=

            let aux_fn =
                    match aux_tree with
                    |template_tree.Node(_,aux_fn,_,_) -> aux_fn
                    |template_tree.Leaf(_,aux_fn,_) -> aux_fn

            //constraint: fn is increased by <= aux fn
            let is_incr_by_le_aux_fn =
                [
                    let ts = Relation.relation_to_linear_terms rel |> SparseLinear.simplify_as_inequalities
                    let lambdas = Z.fresh_var_list ts.Length
                    let lim_incr = SparseLinear.combine_with_z3_terms ts lambdas

                    //lambdas >=0
                    for lambda in lambdas do
                        yield Z.ge lambda ZERO

                    //lambda*A= -r-s
                    for var in prevars do
                        let fn_plus_aux_fn = Z.add (fn.FindWithDefault var ZERO) (aux_fn.FindWithDefault var ZERO)
                        yield Z.eq (lim_incr.FindWithDefault var ZERO) (Z.neg(fn_plus_aux_fn))

                    //lambda*A'= r
                    for var in postvars do
                        yield Z.eq (lim_incr.FindWithDefault var ZERO) (fn.FindWithDefault var ZERO)

                    //-lambda*b >= -const term of s
                    let min_const_term_aux = Z.neg(aux_fn.FindWithDefault ONE_var ZERO)
                    yield Z.ge (lim_incr.FindWithDefault ONE_var ZERO) min_const_term_aux

                ] |> Z.conj

            let (aux_eventually_neg:Microsoft.Z3.BoolExpr) = make_eventually_neg_constraints aux_tree sigma t_bar_indexes

            Z.conj2 is_incr_by_le_aux_fn aux_eventually_neg

        //constraint: rf is Eventually Negative for A in T_bar, in which case label the node 2
        let eventually_negative =
            (Z.eq node_type (Z.constantInt 2))::
            (make_rf_not_const_constraint rf)::
            [for i in t_bar_indexes do //for each rel in T_bar

                let rel = sigma.[i-1]

                //fetch the auxiliary function from the tree
                let is_aux_tree (subtree:template_tree) =
                    match subtree with
                    |template_tree.Node(aux_index,_,_,_) ->
                        if aux_index = i then true
                        else false
                    |template_tree.Leaf(aux_index,_,_) ->
                        if aux_index = i then true
                        else false

                let aux_tree = List.find is_aux_tree children

                let aux_type =
                    match aux_tree with
                    |template_tree.Node(_,_,aux_type,_) -> aux_type
                    |template_tree.Leaf(_,_,aux_type) -> aux_type

                //constraint: rf is eventually decreasing for rel
                let eventually_decreasing_option = eventually_decreasing rf rel aux_tree
                //constraint: rf is unaffected by rel, in which case label the child node 1
                let unaffecting_option =
                    Z.conj2 (Z.eq aux_type (Z.constantInt 1)) (make_unaffecting_constraint_consts rel rf)

                //for rel=A, eventually decreasing:
                if i=index then
                    assert (rel=A)
                    yield eventually_decreasing_option

                //for rel in T_bar\A, can be eventually decreasing or nonincreasing:
                else
                    yield Z.disj2 eventually_decreasing_option unaffecting_option

            ] |> Z.conj

        //rf has to be Negative or Eventually Negative
        Z.disj2 negative eventually_negative

    else //we've reached the max depth, so rf is a leaf and has to be Negative
        negative

/// Tries to find a lexicographic polyranking function with rel_to_add inserted into partial_order.
/// Returns None or a list of Lex_Poly_RF.
/// Note partial_order will be empty initially
let synthesis_poly_lex rel_to_add' partial_order' depth =

    let rel_to_add = Relation.standardise_postvars rel_to_add'
    let partial_order = List.map Relation.standardise_postvars partial_order'

    //printfn "rel_to_add:%A" rel_to_add
    //printfn "partial_order:%A" partial_order

    //Note the pre and postvars of all the relations should be the same, but perhaps in a different order.
    let prevars = Relation.prevars rel_to_add
    let postvars = Relation.postvars rel_to_add
    let allrels = rel_to_add::partial_order

    //NOTE: If rel_to_add is already in partial_order, then it shouldn't have been found
    //We often get bugs turning up here due to something going wrong elsewhere, like finding unsat path invariants, or finding a path but detecting the wrong CP for it.
    assert not(List.contains rel_to_add partial_order)

    let new_template_fn _ =
        let rf_coeffs_sans_const = Z.fresh_var_list (prevars.Length)
        let rf_coeff_const : Microsoft.Z3.ArithExpr = upcast Z.fresh_var()
        let new_fn:template_fn =
            (ONE_var,rf_coeff_const)::
            (List.zip prevars rf_coeffs_sans_const)@
            (List.zip postvars rf_coeffs_sans_const)
            |> Map.ofList
        new_fn

    //Make a new template_tree with given index (this determines how many children each node has)
    let rec make_template_tree (index:int) (depth:int) (t_bar_indexes:int list) =
        let new_fn = new_template_fn()
        let new_type = Z.fresh_var()
        if depth = 0 then
            template_tree.Leaf(index,new_fn,new_type)
        else
            let children = [for k in t_bar_indexes -> (make_template_tree k (depth-1) t_bar_indexes)]
            template_tree.Node(index,new_fn,new_type,children)

    //the list of EN trees we will put constraints on
    let my_trees =
        [for i in 1..allrels.Length -> make_template_tree i depth [i..allrels.Length]]

    ///Generate constraints: for each i, RF i is bounded (below by zero) on rel i
    let bounded_constraints (sigma:Relation.relation list) =
        [for i in 1..sigma.Length do
            let rel_i = sigma.[i-1]
            let tree_i = my_trees.[i-1]
            //find the top-level rf
            let rf_i =
                match tree_i with
                    |template_tree.Node(index,fn,_,_) ->
                        assert(index=i)
                        fn
                    |_ -> failwith "unexpected"
            yield make_bounded_constraints_consts rel_i rf_i]
        |> Z.conj

    ///Generate constraints: for each i, rf_i is Eventually Negative by rel_i in {rel_i,...,rel_n}
    let poly_lex_constraints (sigma:Relation.relation list) =
        [for i in 1..sigma.Length do
            let tree_i = my_trees.[i-1]
            let T_bar = [for j in i..sigma.Length -> j]
            yield make_eventually_neg_constraints tree_i sigma T_bar
        ] |> Z.conj

    //Given a solution m, converts a template_tree into a poly_tree
    let rec retrieve_tree (m:Microsoft.Z3.Model) (tree:template_tree) =
        match tree with
        |template_tree.Node(index,fn,node_type,children) ->
            let soln_fn = Map.map (fun var coeff ->
                                        if List.contains var postvars then
                                            bigint.Zero
                                        else Z.get_model_int m coeff
                                        ) fn |> SparseLinear.linear_term_to_term
            let soln_type = (Z.get_model_int m node_type)
            if (soln_type = bigint.Zero) then //Negative
                poly_tree.N(index,soln_fn)
            else if (soln_type = bigint.One) then //Unaff
                poly_tree.U(index)
            else //EN
                let poly_children = List.map (retrieve_tree m) children
                poly_tree.EN(index,soln_fn,poly_children)

        |template_tree.Leaf(index,fn,node_type) ->
            let soln_fn = Map.map (fun var coeff ->
                                        if List.contains var postvars then
                                            bigint.Zero
                                        else
                                            Z.get_model_int m coeff
                                        ) fn |> SparseLinear.linear_term_to_term
            let soln_type = (Z.get_model_int m node_type)
            //if we're investigating it, and it's a leaf, then it should be negative or unaff
            assert (soln_type <> (bigint 2))
            if (soln_type = bigint.Zero) then //Negative
                poly_tree.N(index,soln_fn)
            else //Unaff
                poly_tree.U(index)

    //For each possible insertion of rel_to_add to partial_order, try to find a lexicographic polyranking solution
    let (lexoptions:Lex_Poly_RF list) =
        [for i in 0..partial_order.Length do
            let sigma=[for j in 0..i-1 -> partial_order.[j]]@[rel_to_add]@[for j in i..partial_order.Length-1 -> partial_order.[j]]//inserts rel_to_add into ith position
            let bounded_cons = bounded_constraints sigma
            let poly_lex_cons = poly_lex_constraints sigma
            let allconstraints = Z.conj[bounded_cons;poly_lex_cons]
            match Z.solve [allconstraints] with
            | None -> ()
            | Some m ->
                    let soln_trees = [for k in 1..sigma.Length -> retrieve_tree m my_trees.[k-1]]
                    m.Dispose()
                    yield (sigma,soln_trees)
        ]

    if lexoptions.Length >0 then
        Some lexoptions
    else
        None
