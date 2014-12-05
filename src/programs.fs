//////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      programs.fs
//
//  Abstract:
//
//      Representation for arithmetic, non-recursive programs
//
//  Notes:
//      * During construction of programs we abstract away disjunctions within assume(...) commands
//        and store them away to be used later if needed
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


module Programs

open Utils
open Term
open Formula
open Log

///
/// Constants not abstracted away because they are used as bounds
///
let bound_constants = [-4 .. 4] |> List.map (fun i -> bigint i) |> Set.ofList |> ref
//let bound_constants = ref (Set.ofList [0])

///
/// File position information for commands: (line number, file name)
///
type pos = (int * string) option

///
/// Commands datatype
///
type command =

    ///
    /// Assign(p,v,t) represents v := t at location p
    ///
    | Assign of pos * Var.var * term

    ///
    /// Assume(p,f) represents  "if (!f) ignore" at location p
    ///
    | Assume of pos * formula

    member cmd.Is_Assign = match cmd with
                           | Assign(_,_,_) -> true
                           | Assume(_,_) -> false
    member cmd.Is_Assume = cmd.Is_Assign |> not
    member cmd.Position  = match cmd with
                           | Assign(pos,_,_) -> pos
                           | Assume(pos,_) -> pos

///
///
///
let assume f = Assume(None, f)
let assign v t = Assign(None, v, t)

///
/// We don't have a skip command, encoded instead as assume(true)
///
let skip = Assume(None,Formula.truec)

//
// Pretty-printing routines
//

let pos2pp pos = match pos with
                 | None -> ""
                 | Some(k,file) -> sprintf "%s:%d" file k

let command2pp c = match c with
                   | Assign(None,v,e) ->   Var.pp v + " := " + e.pp ^ ";"
                   | Assume(None,e) ->    "assume(" + Formula.pp e + ");"
                   | Assign(p,v,e) ->   Var.pp v + " := " + e.pp + "; // at " + pos2pp p
                   | Assume(p,e) ->    "assume(" + Formula.pp e + "); // at " + pos2pp p

let commands2pp b = (List.fold (fun x y -> x ^ "    " ^ command2pp y ^ "\n") "{\n" b) ^ "}"

///
/// Return free variables in a sequence of commands
///
let freevars cmds =
    let cmd_vars c =
        match c with
        | Assign(_, v, e) ->  (Term.freevars e).Add v
        | Assume(_, e) ->    freevars e

    Seq.map cmd_vars cmds |> Set.unionMany

///
/// Return the set of variables modified by a sequence of commands
///
let modified cmds =
    seq {
        for cmd in cmds do
            match cmd with
            | Assume _ -> ()
            | Assign (_, v, _) -> yield v
    } |> Set.ofSeq

//
// Control flow graphs -----------------------------------------------------
//

/// Default size for transitions array
let transitions_sz = ref 50000

type Program = { initial : int ref
               ; node_cnt : int ref
               ; nodeToLabels : Map<int,string> ref
               ; labels : Map<string,int> ref
               /// Map from newly introduced instrumentation variables to disjunctions abstracted by them
               ; abstracted_disjunctions : Map<string, command list> ref
               ; transitions : (int * command list * int) []
               ; transitions_cnt : int ref

               /// x \in active iff transitions[x] != (-1,_,-1)
               ; active : Set<int> ref

               /// Variables in the program
               ; vars : Set<Var.var> ref

               /// Locations in the program
               ; locs : Set<int> ref

               /// Constants used in the program.
               ; constants : Set<bigint> ref

               /// Flag indicating that we abstracted away things in an incomplete manner and hence should not report non-term
               ; incomplete_abstraction : bool ref

               }

let enumerate_transitions p = seq {
        for node in !p.active do
            let (k, _,k' ) = p.transitions.[node]
            assert (k <> -1)
            assert (k' <> -1)

            yield p.transitions.[node]
    }

/// take function that transforms transition
/// and apply it to every transition in the program
let transitions_inplace_map p f =
    for n in !p.active do
        let (k,_,k') = p.transitions.[n]
        assert (k <> -1)
        assert (k' <> -1)
        p.transitions.[n] <- f (p.transitions.[n])

///
/// If variables are used temporarly in basic blocks and then are killed or not used elsewhere, let_convert
/// removes them in the obvious way. livevars is assumed to be the set of live variables
/// Our heuristic is based on the idea that more variables are bad, given how constraint-based rank
/// function synthesis and interpolation work.
/// It also special cases instrumentation variables, which might be considered dead, but are still
/// important to us.
///
let let_convert p livevars =

    //
    // Is the variable read in the later commands before being written to again? We know the livevars
    // at the beginning and end of the command sequence, but not in the intermediate points.
    // We could compute the live
    //
    let rec needed_local v cmds =
        match cmds with
        | Assume(_,f)::cmds'   -> if Set.contains v (Formula.freevars f) then true
                                  else needed_local v cmds'
        | Assign(_,v',t)::cmds' -> if Set.contains v (Term.freevars t) then true
                                   else if v'=v then false
                                   else needed_local v cmds'
        | [] -> false

    let unrelated x v t = x<>v && not (Set.contains x  (Term.freevars t))
    let wipe x env = Map.filter (unrelated x) env

    let rewrite_cmd map cmd =
        let env v =
            match Map.tryFind v map with
            | Some t -> t
            | None -> Var v

        match cmd with
        | Assume(p,f) -> Assume(p,Formula.subst env f)
        | Assign(p,v,t) -> Assign(p,v,Term.subst env t)

    let rec interp lvs env cmds =
        match cmds with
        | Assign(pos,v,Nondet)::r ->
            let env' = wipe v env
            Assign(pos,v,Nondet)::interp lvs env' r
        | Assign(pos,v,t)::r ->
            let cmd' = rewrite_cmd env (Assign(pos,v,t))
            let t' = match cmd' with
                     | Assign(_,_,t') -> t'
                     | _ -> die()
            let env' = wipe v env
            let env'' = if not (Set.contains v lvs) then Map.add v t' env' else env'
            if not (Set.contains v lvs) && not (needed_local v r) && not(Formula.is_saved_var v) then skip::interp lvs env'' r
            else cmd'::interp lvs env'' r
        | assm::r -> rewrite_cmd env assm::interp lvs env r
        | [] -> []

    transitions_inplace_map p (fun (k,T,k') ->
        let lvs = Map.find k' livevars
        let T' = interp lvs Map.empty T
        (k,T',k')
    )
    ()

//
// Constant propagation
//
let prop_constants p mapping =

    let rewrite_cmd map cmd =
        let env v =
            match Map.tryFind v map with
            | Some c -> Term.Const c
            | None -> Var v
        match cmd with
        | Assume(p,f) -> Assume(p,Formula.subst env f)
        | Assign(p,v,t) -> Assign(p,v,Term.subst env t)

    let get_mods T =
        seq {
            for c in T do
                match c with
                | Assume(_, _) -> ()
                | Assign(_, v, _) -> yield v
        } |> Set.ofSeq

    // make sure not to rewrite x to 5 if x is temporarily set to some other value in T
    let clean_map k T =
        let vs = get_mods T
        Map.filter (fun v _ -> not (Set.contains v vs)) (Map.find k mapping)

    transitions_inplace_map p (fun (k,T,k') ->
        let map' = clean_map k T
        let T' = List.map (rewrite_cmd map') T
        (k,T',k')
    )

type TransitionFunction = int -> (command list * int) list

//
// APPROVED API
//
let new_node p =
    let old = !p.node_cnt
    p.node_cnt := old + 1
    assert (!p.node_cnt > old)
    old

//
// Mapping from labels to internally used nodes
//
let map p k = match Map.tryFind k !p.labels with
              | None -> let node = new_node p
                        p.labels := Map.add k node !p.labels
                        p.nodeToLabels := Map.add node k !p.nodeToLabels
                        node
              | Some(node) -> node

let findLabel p node = Map.tryFind node !p.nodeToLabels

//
// APPROVED API
//
let set_initial p x =
    p.initial := map p x

///
/// Replace all constants that are not in 'range' with special variables
/// like __const__42. Return new term and set of eliminated constants.
///
let rec term_constants range t =
    let s = ref Set.empty
    let rec alpha t =
        match t with
        | Nondet -> Nondet
        | Const(c) when Set.contains c range -> Const(c)
        | Const(c) -> s := Set.add c !s;
                      Var(Formula.const_var c)
        | Var(v) -> Var(v)
        | Neg(t) -> Neg(alpha t)
        | Add(t1, t2) -> Add(alpha t1, alpha t2)
        | Sub(t1, t2) -> Sub(alpha t1, alpha t2)
        | Mul(t1, t2) -> Mul(alpha t1, alpha t2)
    let t' = alpha t
    (t',!s)

///
/// Replace all constants that are not in range with special variables
/// like __const__42. Return new formula and set of eliminated constants.
///
let rec formula_constants range f =
    let s = ref Set.empty

    let case_term t1 t2 f =
        let (t1',s1) = term_constants range t1
        let (t2',s2) = term_constants range t2
        s := Set.unionMany [!s; s1; s2]
        f(t1',t2')

    let rec alpha f =
        match f with
        | Eq(t1, t2) -> case_term t1 t2 Eq
        | Ge(t1, t2) -> case_term t1 t2 Ge
        | Le(t1, t2) -> case_term t1 t2 Le
        | Gt(t1, t2) -> case_term t1 t2 Gt
        | Lt(t1, t2) -> case_term t1 t2 Lt
        | And(f1, f2) -> And(alpha f1, alpha f2)
        | Or(f1, f2) -> Or(alpha f1, alpha f2)
        | Not(f) -> Not(alpha f)
    let f' = alpha f
    (f',!s)

///
/// Replace all constants that are not in range with special variables
/// like __const__42. Return new command and set of eliminated constants.
///
let command_constants range cmd =

    let cmd =
        let vs = freevars [cmd]
        let pos = match cmd with
                  | Assign(pos,_,_) -> pos
                  | Assume(pos,_) -> pos
        let contains_pc = Set.exists (fun (v:string) -> v.Contains "_pc") vs
        if contains_pc then
            Assume(pos,Formula.truec)
        else
            cmd

    match cmd with
    | Assume(pos,f) ->
        let (f',s) = formula_constants range f
        (Assume(pos,f'),s)
    | Assign(pos,v,t) ->
        let (t',s) = term_constants range t
        (Assign(pos,v,t'),s)

///
/// Replace all constants that are not in range with special variables
/// like __const__42. Return new commands and set of eliminated constants.
///
let commands_constants range cmds =
    let cmds', constants = List.unzip (List.map (command_constants range) cmds)
    (cmds', Set.unionMany constants)

///
/// Is cmd c representing a disjunction?
///
let is_disj_cmd c = Set.exists Formula.is_disj_var (freevars [c])


///
/// add transition n--T-->m as it is, without any preprocessing
///
let plain_add_transition p n T m =
    let cnt = !p.transitions_cnt
    p.transitions_cnt := cnt + 1;
    p.active := Set.add cnt !p.active
    if (!p.transitions_cnt >= !transitions_sz) then die()
    assert (!p.transitions_cnt > cnt);
    assert (!p.transitions_cnt < !transitions_sz);
    p.transitions.[cnt] <- (n,T,m)
    p.vars := Set.union !p.vars (freevars T)
    p.locs := Set.add n !p.locs
    p.locs := Set.add m !p.locs

type SeqPar =
    | Atom of command
    | Seq of SeqPar list
    | Par of SeqPar list

let rec as_seq sp =
    match sp with
    | Seq ss -> ss |> List.map as_seq |> List.concat
    | _ -> [sp]

let rec add_transition_seqpar p n sp m =
    let parts = as_seq sp
    if List.length parts = 0 then
        plain_add_transition p n [] m
    else
        let get_tmp_node() = new_node p

        let len = List.length parts

        let mutable last_loc = n
        let mutable unsaved_commands = []
        for part, number in List.zip parts [0 .. len-1] do
            match part with
            | Atom cmd ->
                unsaved_commands <- cmd::unsaved_commands
            | Par pars ->
                assert (List.length pars >= 1)
                // it is important that Par introduces new nodes even when length(pars) = 1
                // see command_to_seqpar
                if unsaved_commands <> [] then
                    let loc = get_tmp_node()
                    plain_add_transition p last_loc (List.rev unsaved_commands) loc
                    unsaved_commands <- []
                    last_loc <- loc
                let next_loc = if number = len-1 then m else get_tmp_node()
                for par in pars do
                    add_transition_seqpar p last_loc par next_loc
                last_loc <- next_loc
                ()
            | Seq _ -> die()
        if unsaved_commands <> [] then
            assert (n = m || last_loc <> m)
            plain_add_transition p last_loc (List.rev unsaved_commands) m

let rec command_to_seqpar p cmd =

    let skip_if_true cmd =
        match cmd with
        | Assume (_, f) when Formula.is_true_formula f -> Seq []
        | _ -> Atom cmd

    match cmd with
    | Assume(_, f) when contains_nondet f ->
        Seq []
    | Assume(pos, f) ->
        let f = polyhedra_dnf f
        match f |> split_disjunction |> List.map split_conjunction with
        | [[f1]; [f2]] -> // disjunction of two atomic formulae
            if !Arguments.lazy_disj then
                log "Lazy disjunction"
                let cmd1 = Assume (pos, f1)
                let cmd2 = Assume (pos, f2)
                let k = (!p.abstracted_disjunctions).Count
                let v = Formula.disj_var k
                p.abstracted_disjunctions := Map.add v [cmd1; cmd2] !p.abstracted_disjunctions
                let cmd = Assign(pos, v, Term.var v)

                // this is important to wrap it into fake Par, because
                // we have to generate nodes for this instruction
                // (so that later disj refinement callback can
                // remove this edge and introduce two concrete edges)
                Par [Atom cmd]
            else
                Par [for f' in [f1; f2] -> command_to_seqpar p (Assume (pos, f'))]
        | [fs] -> // conjunction of atomic formulae
            Seq [
                for f in fs do
                    match f with
                    | Le (t1, t2) ->
                        let f =
                            try
                                Le (SparseLinear.term_as_linear t1, SparseLinear.term_as_linear t2)
                            with SparseLinear.Nonlinear _ ->
                                sprintf "WARNING: Non-linear assumption %s\n" (command2pp cmd) |> Log.log
                                p.incomplete_abstraction := true
                                Formula.truec

                        let cmd = Assume (pos, f)
                        yield skip_if_true cmd

                    | _ -> dieWith "polyhedra_dnf returned something strange"
            ]
        | x -> if !Arguments.abstract_disj then
                   Log.log <| sprintf "WARNING: IGNORING ASSUME\n"
                   Seq []
               else
                   Log.log <| sprintf "WARNING: assume blowup = %d\n" x.Length
                   Par [for f' in x -> Seq [for f'' in f' -> command_to_seqpar p (Assume (pos, f''))]]

    | Assign(_, _, Nondet) ->
        Atom cmd
    | Assign(pos, v, tm) ->
        let c =
            try
                Assign(pos, v, SparseLinear.term_as_linear tm)
            with SparseLinear.Nonlinear _ ->
               sprintf "WARNING: Non-linear assignment %s\n" (command2pp cmd) |> Log.log
               p.incomplete_abstraction := true
               Assign(pos, v, Term.Nondet)
        Atom c

let add_transition_unmapped p n T m =
    let T =
        if !Arguments.elim_constants then
            let (T, consts) = commands_constants !bound_constants T
            p.constants := Set.union !p.constants consts
            T
        else
            T
    let sp = T |> List.map (command_to_seqpar p) |> Seq

    add_transition_seqpar p n sp m

/// add transition n--T-->M with preprocessing
/// (elim_constants; lazy_disj / split disjunctions)
let add_transition p input_n T input_m =
    let n = map p input_n
    let m = map p input_m

    if n <> m then
        add_transition_unmapped p n T m
    else
        // split loop edge, because loop edges cause problems with compact_path
        let tmp = new_node p
        add_transition_unmapped p n T tmp
        add_transition_unmapped p tmp [] m

///
/// copy p returns a deep copy of program p
///
let copy q  =
        let p = { initial = ref (!q.initial)
                ; node_cnt = ref (!q.node_cnt)
                ; labels = ref (!q.labels)
                ; nodeToLabels = ref(!q.nodeToLabels)
                ; abstracted_disjunctions = ref (!q.abstracted_disjunctions)
                ; transitions_cnt = ref (!q.transitions_cnt)
                ; transitions = Array.copy q.transitions
                ; active = ref (!q.active)
                ; vars = ref (!q.vars)
                ; locs = ref (!q.locs)
                ; constants = ref (!q.constants)
                ; incomplete_abstraction = q.incomplete_abstraction
                }
        p

//
// APPROVED API
//

// Using List.rev because originally they were constructed in imperative manner, accumulating from the head

let transitions_from p loc =
    List.rev [for k, T, k' in enumerate_transitions p do if k = loc then yield (T, k')]

let transitions_to p loc =
    List.rev [for k, T, k' in enumerate_transitions p do if k' = loc then yield (T, k)]

//
// Return the locations used in the program
//
let locations p = !p.locs

//
// Return the variables used in the program
//
let variables p = !p.vars

//
// Return a mapping from nodes to nodes that are reachable using the CFG edges
//
let cfg_reach p =
    let reachable = new SetDictionary<int, int>()
    let locs = locations p |> Set.toList

    for l, _, l' in enumerate_transitions p do
        reachable.Add(l, l')

    //
    // Take a step towards building the table
    //
    let update loc =
        let oldReachable = reachable.[loc]
        let newReachable = Set.fold (fun closure reachableLoc -> Set.union closure reachable.[reachableLoc]) oldReachable oldReachable
        if Set.count oldReachable = Set.count newReachable then 
            false
        else
            reachable.ReplaceSet loc newReachable
            true
    let step () = List.map update locs |> List.exists id
    while step() do
        ()
    done
    reachable

///Remove transition with index n from the program p
let remove_transition p n =
    p.transitions.[n] <- (-1,[],-1)
    p.active := Set.remove n !p.active

//
// Prune out stupidly unreachable locations in the program
//
let remove_unreachable p =
    let reachableMap = cfg_reach p
    let reachableLocs = Set.add !p.initial reachableMap.[!p.initial]
    let unreachable = Set.difference (locations p) reachableLocs

    for n in [0 .. !p.transitions_cnt-1] do
        let (k,_,k') = p.transitions.[n]
        if Set.contains k unreachable || Set.contains k' unreachable then
            remove_transition p n

    p.locs := Set.difference !p.locs unreachable

///
/// Returns strongly connected subgraphs in the transitive closure of p's
/// control-flow graph.
///
let sccsgs p =
    //Get map from location to all reachable locations:
    let reachableMap = cfg_reach p

    SCC.find_sccs reachableMap !p.initial |> List.map Set.ofList

//
// Compute dominators tree
//
let dominators_from p_orig loc =
    //Turn program into a CFG (as a map from location to directly reachable locations):
    let cfg = new SetDictionary<int, int>()
    for l, _, l' in enumerate_transitions p_orig do
        cfg.Add(l, l')

    Dominators.find_dominators cfg loc

let dominators p_orig =
    let initial = !p_orig.initial
    dominators_from p_orig initial

let dominates t x y = Dominators.dominates t x y

/// Are all elements of the set dominated by one element?
/// Equivalenthly, does the set have single entry point?
let well_formed t xs = Dominators.well_formed t xs

let headers t xs = Dominators.headers t xs

let cutpoints p =
    let cuts = ref Set.empty
    let marks = new System.Collections.Generic.Dictionary<int, bool>()

    let rec dfs_visit node =
        marks.Add(node, false) // false means in progress

        for _, node' in transitions_from p node do
            match marks.TryGetValue(node') with
            | false, _ -> dfs_visit node'
            | true, true -> ()
            | true, false ->
                // node->node' is backedge
                cuts := (!cuts).Add node'

        marks.[node] <- true // true means fully processed

    dfs_visit !p.initial

    !cuts |> Set.toList

//
// For each node we return a set of nodes representing the nodes "inside" the loop. As described in
// "Variance analyses from invariance analyses", POPL'07
//
// Return list of pairs (cutpoint, corresponding region)
let isolated_regions p =
    let scs = sccsgs p
    let cps = cutpoints p

    let dtree = dominators p

    //Check out all CPs
    [for cutpoint in cps do
        //For each CP, find the SCCs dominated by it:
        let sets = [
            //Check each SCC:
            for comp in scs do
                //Weed out trivial one-element SCCs. Invariant guarantees that we have no self-loops:
                if comp.Count > 1 then
                    //Does this SCC only have one entry point?
                    if well_formed dtree comp then
                        //Is that entry point our cutpoint? If yes, add things.
                        yield Set.filter (dominates dtree cutpoint) comp // is that even right?
                    else
                        //If not, are we part of the SCC?
                        if comp.Contains cutpoint then
                            yield comp
            ]
        yield cutpoint, sets
    ]

let combine (xs:'a Set) (ys:'a Set) = [yield! xs; yield! ys] |> Seq.fold (fun (acc:'a Set) x -> acc.Add(x)) Set.empty
let concat (xs:(Set<'a>) seq) = Seq.fold combine Set.empty xs

let find_loops p =
    let regions = isolated_regions p
    let cps_to_loops =
        seq {
            for (cp, sccs) in regions do
                let loop = concat sccs
                yield cp, loop
        } |> Map.ofSeq
    let cps_to_sccs =
        seq {
            for (cp, sccs) in regions do
                let loop = sccs |> Seq.filter (fun scc -> scc.Contains cp) |> concat
                yield cp, loop
        } |> Map.ofSeq
    (cps_to_loops, cps_to_sccs)

//Returns a map of a nested loop, out loop
let make_isolation_map (loops : Map<int,Set<int>>) =
    let isolation_map = ref Map.empty

    for KeyValue(cp, loop) in loops do
        for loc in loop do
            if loops.ContainsKey(loc) then
                let v = loops.[loc]
                if not(Set.contains cp v) then
                    isolation_map := (!isolation_map).Add(loc, cp)

    !isolation_map

//
// APPROVED API
//
let make is_temporal init ts incomplete_abstraction =
        let p = { initial = ref 0
                ; node_cnt = ref 0
                ; labels = ref Map.empty
                ; nodeToLabels = ref Map.empty
                ; abstracted_disjunctions = ref Map.empty
                ; transitions_cnt = ref 0
                ; transitions = Array.create !transitions_sz (-1,[],-1)
                ; active = ref Set.empty
                ; vars = ref Set.empty
                ; locs = ref Set.empty
                ; constants = ref Set.empty
                ; incomplete_abstraction = ref incomplete_abstraction
                }
        let mutable init_is_target = false
        for x, cmds, y in ts do
            add_transition p x cmds y
            if y = init then
                init_is_target <- true
        done
        p.initial := map p init

        //Make sure that an initial state is not in a loop:
        if not(is_temporal) then
            let new_initial = new_node p
            plain_add_transition p new_initial [] !p.initial
            p.initial := new_initial
        else
            if init_is_target then
                let (cp_to_dominated_loops, _) = find_loops p
                if Map.containsKey !p.initial cp_to_dominated_loops then
                    Utils.dieWith "Cannot do temporal proofs for programs with start state on a loop."
        p

/// Collapse adjacent commands so that if there were multiple commands
/// in the transition from location x to location y, we end up with a single list of commands
/// for the transition from x to y.
/// Example: [(1, a, 2), (1, b, 2), (2, c, 3), (2, d, 3)] -> [(1, [a, b], 2), (2, [c, d], 3)]
/// Loop edges are not allowed.
let collapse_path p =
    let mutable first = true
    let mutable prev_l1 = 0
    let mutable prev_l2 = 0
    let mutable accum_cmds = []
    let mutable result = []

    for l1, cmd, l2 in p do
        assert (l1 <> l2)
        if not first && l1 = prev_l1 && l2 = prev_l2 then
            accum_cmds <- cmd :: accum_cmds
        else
            //assert (first || prev_l2 = l1)
            if accum_cmds <> [] then
                result <- (prev_l1, List.rev accum_cmds, prev_l2) :: result
                accum_cmds <- []
            prev_l1 <- l1
            prev_l2 <- l2
            accum_cmds <- [cmd]
        first <- false

    if accum_cmds <> [] then
        result <- (prev_l1, List.rev accum_cmds, prev_l2) :: result

    List.rev result

let print_path path =
    for from ,cmds, to_ in path do
        printf "    %d-->%d;\n" from to_
        List.iter (command2pp >> printf "              %s\n") cmds

let symbolic_consts_cmds consts =

    let small = !bound_constants

    assert ((Set.intersect small consts).IsEmpty)

    let consts = Set.union small consts
    let consts = Set.toList consts |> List.sort

    let make_const k =
       if Set.contains k small then
           Term.Const k
       else
           Var(Formula.const_var k)

    [
        if not consts.IsEmpty then
            for c1, c2 in List.zip (List.all_but_last consts) (List.tail consts) do
                if not (Set.contains c1 small &&
                        Set.contains c2 small) then
                    let v1 = make_const c1
                    let v2 = make_const c2
                    assert (c1 < c2)
                    let lt = Lt(v1, v2)
                    yield Assume(None, lt)
    ]

let consts_cmds path =
    let used = ref Set.empty
    let assign_const_vars cmd =
        match cmd with
        | Assume(_,_) -> Set.empty
        | Assign(_,_,t) -> Term.freevars t |> Set.filter Formula.is_const_var
    let assign_const_vars_cmds cmds = List.map assign_const_vars cmds |> Set.unionMany

    for (_,cmds,_) in path do
        let vs = assign_const_vars_cmds cmds
        used := Set.union !used (Set.filter Formula.is_const_var vs)
    done
    let used_ints = Set.map Formula.get_const_from_constvar !used
    symbolic_consts_cmds used_ints

let symbconsts_init p =
    if not <| Set.isEmpty !p.constants then
        let commands = symbolic_consts_cmds !p.constants
        let new_init = new_node p
        plain_add_transition p new_init commands !p.initial
        p.initial := new_init

/// Replace __const variables by the actual constants again
let const_subst cmd =
    match cmd with
        | Assign(pos,v,t) ->
            let t' = Term.subst Formula.eval_const_var t
            Assign(pos,v,t')
        | Assume(pos,f)   ->
            let f' = Formula.subst Formula.eval_const_var f
            Assume(pos,f')

/// Merge chains of transitions together.
let chain_transitions nodes_to_consider transitions =
    // (1) Create maps in_trans/out_trans mapping nodes to incoming/outgoing transitions.
    let in_trans = new System.Collections.Generic.Dictionary<int, System.Collections.Generic.HashSet<(Set<int> * (int * command list * int))>>()
    let out_trans = new System.Collections.Generic.Dictionary<int, System.Collections.Generic.HashSet<(Set<int> * (int * command list * int))>>()
    let add_to_set_dict (dict : System.Collections.Generic.Dictionary<int, System.Collections.Generic.HashSet<(Set<int> * (int * command list * int))>>) k v =
        if dict.ContainsKey k then
            dict.[k].Add v
        else
            dict.Add(k, new System.Collections.Generic.HashSet<(Set<int> * (int * command list * int))>())
            dict.[k].Add v
    for trans in transitions do
        let (_, (k, _, k')) = trans
        add_to_set_dict in_trans k' trans |> ignore
        add_to_set_dict out_trans k trans |> ignore

    let first_elem_of_set (set : System.Collections.Generic.HashSet<'T>) =
        let mutable set_enum = set.GetEnumerator()
        set_enum.MoveNext() |> ignore
        set_enum.Current

    // (2) If for some k out_trans.[k] and in_trans.[k] are singleton sets, replace the two transitions by a direct one.
    for k in nodes_to_consider do
        if in_trans.ContainsKey k && out_trans.ContainsKey k then
            let in_trans_k = in_trans.[k]
            let out_trans_k = out_trans.[k]
            if in_trans_k.Count = 1 && out_trans_k.Count = 1 then
                // k has only one incoming and one outgoing transition. Merge:
                let t1 = first_elem_of_set in_trans_k //that's the only one!
                let (idxs1, (k1, cmds1, _)) = t1
                let t2 = first_elem_of_set out_trans_k //that's the only one!
                let (idxs2, (_, cmds2, k2)) = t2
                let t = (Set.union idxs1 idxs2, (k1, cmds1@cmds2, k2))
                if k1 <> k then
                    //printfn "Chaining %i->%i and %i->%i" k1 k k k2
                    //Now remove t1 and t2, add t instead:
                    in_trans.Remove k |> ignore
                    out_trans.Remove k |> ignore
                    if out_trans.ContainsKey k1 then
                        out_trans.[k1].Remove t1 |> ignore
                        out_trans.[k1].Add t |> ignore
                    if in_trans.ContainsKey k2 then
                        in_trans.[k2].Remove t2 |> ignore
                        in_trans.[k2].Add t |> ignore
    // (3) The updated transitions are now in in_trans and out_trans:
    in_trans.Values |> Seq.concat |> Set.ofSeq

///Returns all transitions reachable from cp that are not an artifact of the termination instrumentation, where copied is set
let filter_out_copied_transitions cp scc_transitions =
    if !Arguments.lexicographic then //if we didn't do lexicographic instrumentation, this optimization is unsound
        let cleaned_scc_nodes = new System.Collections.Generic.HashSet<int>()
        let mutable found_new_node = ref (cleaned_scc_nodes.Add cp)
        while !found_new_node do
            found_new_node := false
            for (_, (k, cmds, k')) in scc_transitions do
                if cleaned_scc_nodes.Contains k && not(cleaned_scc_nodes.Contains k') then
                    //Ignore instrumentation transitions:
                    let is_no_copy_transition =
                           cmds
                        |> Seq.filter
                            (function | Assume(_,_) -> false
                                      | Assign(_,var,term) -> (Formula.is_copied_var var) && term.Equals(Term.constant 1))
                        |> Seq.isEmpty
                    if is_no_copy_transition then
                        found_new_node := cleaned_scc_nodes.Add k'

        scc_transitions
        |> Set.filter (fun (_, (k, _, k')) -> cleaned_scc_nodes.Contains k && cleaned_scc_nodes.Contains k')
    else 
        scc_transitions

let get_current_locations p =
    let res = ref Set.empty
    for n in !p.active do
        let (k,_,k') = p.transitions.[n]
        res := Set.add k !res
        res := Set.add k' !res
    !res

let add_const1_var_to_relation extra_pre_var extra_post_var rel =
    let (formula, prevars, postvars) = (Relation.formula rel, Relation.prevars rel, Relation.postvars rel)
    let newformula =
        Formula.And (
            Formula.And (formula,
                (Formula.Eq (Term.Var extra_pre_var, (Term.constant 1)))),
            (Formula.Eq (Term.Var extra_post_var, (Term.constant 1))))
    Relation.standardise_postvars (Relation.make newformula (extra_pre_var::prevars) (extra_post_var::postvars))
