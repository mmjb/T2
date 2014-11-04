////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      Reachability
//
//  Abstract:
//
//       Interpolation-based safety/reachability prover
//
//  Notes:
//
//       * Currently we're using an interpolation procedure that really likes only convex constraits.  That
//         causes some problems, particularly when attempting to force covers (see try_force_cover)
//       * I've implemented a lazy method of hiding disjunction such that disjunction in assume(...)
//         statements is only used if/when it's needed in the lazy interpolation graph
//       * I've also implemented an optimization that explictly tracks when "seeding" has happened when
//         the safety prover is being used as the basis of a termination prover
//       * I've also implemented a priority-scheme such that the caller can specify transitions that he/she
//         would prefer to be taken before others.  Since binary reachability checking has a certain state
//         machine in mind in the encoding this is helpful.  We also implement a heuristic with this strategy
//         which allows us to try to stay within the current loop (and not leave the loop or go into a nested
//         loop) when looking for bugs.  This helps us find better ranking functions (the assumption is that for
//         the most part a loop body itself has all the information you need to find a termination argument and
//         that you usually only need to CHECK that its still valid when go into a nested loop
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


module Reachability

open Utils
open Log
open Programs
open Stats
open PrioStack

/// Should we perform garbage collection on the abstraction graph?
let do_gc = ref true

/// Should we perform some sanity checks to make sure that we're not using
/// nodes that have been GC'd?
let gc_check = ref false

/// refine_disj decides if we perform lazy disjunction refinement.
let refine_disj = ref true

/// Tree/Graph constructon representing the state of the safety proof procedure.  Back edges
/// in the "covering" relations represent induction checks.  At the end of a successful proof
/// search this graph should represent a valid proof of safety which could be spit out to a
/// theorem prover.  Note that for performance there is A LOT of redundency in this graph. Its
/// RIDDLED with invariants. Fun.
type Graph =
    {
    (* ------- Things relating to the input program ------- *)
    /// Error location we're trying to prove unreachable
      loc_err : int

    /// Initial location.
    ; loc_init : int

    /// Transition relation, mapping each location to a list of (relation, successor location) pairs.
    ; transition : Programs.TransitionFunction

    /// Priority of each node in the original program.  Used to choose which node to take during DFS
    ; priority : Map<int,int>

    /// commands of the form assume(x>0 || y>0) get abstracted to, essentially, skip (in fact, they get translated to
    /// a weird assignment statement like __disjvr_42 := __disjvr_42.
    /// This maps the weird variable name to the original disjunction that we can pull out if needed
    ; abstracted_disjunctions : Map<string, Programs.command list>
    
    (* ------- State of the abstract reachability graph ------- *)
    /// Counter tracking how many nodes we have in the system
    ; cnt : int ref

    /// Current nodes in the system
    ; V : Set<int> ref

    /// Edge relation
    ; E : SetDictionary<int,int>

    /// parents in the graph
    ; parent : DefaultDictionary<int, int>

    /// Set of interpolants (understood as conjunction) for each node
    ; psi : DefaultDictionary<int, Set<Formula.formula>>

    /// Current leaves in the execution tree
    ; leaves : Set<int> ref

    /// Mapping from edges in the execution tree to the commands in the original program
    ; abs_edge_to_program_commands : System.Collections.Generic.Dictionary<int * int, Programs.command list>

    /// Mapping from nodes in the execution tree to the original program
    ; abs_node_to_program_loc : DefaultDictionary<int, int>

    /// A node n\in representatives(k) if n in the graph maps back to k in the original program.
    /// i.e. if n\in representatives(k) then node_map n = k
    ; program_loc_to_abs_nodes : SetDictionary<int,int>

    /// Induction coverings
    ; covering : Map<int, int> ref

    /// Per-node list of candidates that we should search for when looking for a force cover
    ; fc_candidates : DefaultDictionary<int, int list option>

    /// Node numbers do not quite represent the order that we've "visited" them. dfs_map maps each node number to its dfs number
    ; dfs_map : DefaultDictionary<int, int>
    /// Helper to create dfs numbers
    ; dfs_cnt : int ref

    /// The stack used during DFS.
    ; stack : PrioStack ref

    /// Nodes that have been deemed as garbage but havent been GC'd yet.
    ; garbage : Set<int> ref

    /// Nodes that were in the system but have now been dead and GC'd
    ; dead : Set<int> ref
    }

let rec push_priostack_abs_many (abs:Graph) vs  =
    let mutable sr = !abs.stack
    for v in List.rev vs do
        let prio = Map.findWithDefault abs.abs_node_to_program_loc.[v] 0 abs.priority
        sr <- push_priostack prio v sr
    abs.stack := sr

let make_abs_pgm init_loc error_loc transition priority_opt abstracted_disjunctions =
    {
      loc_err = error_loc
    ; loc_init = init_loc
    ; transition = transition
    ; V = ref Set.empty
    ; E = new SetDictionary<int,int>()
    ; parent = new DefaultDictionary<int,int>(fun _ -> -1)
    ; psi = new DefaultDictionary<int,Set<Formula.formula>>(fun _ -> Set.empty)
    ; abs_node_to_program_loc = new DefaultDictionary<int,int>(fun _ -> -1)
    ; program_loc_to_abs_nodes = new SetDictionary<int,int>()
    ; fc_candidates = new DefaultDictionary<int,int list option>(fun _ -> None)
    ; leaves = ref Set.empty
    ; abs_edge_to_program_commands = new System.Collections.Generic.Dictionary<int * int, Programs.command list>()
    ; cnt = ref 0
    ; covering = ref Map.empty
    ; dfs_map = DefaultDictionary<int, int>(fun _ -> -1)
    ; dfs_cnt = ref 0
    ; priority = defaultArg priority_opt Map.empty
    ; stack = ref empty_priostack
    ; abstracted_disjunctions = abstracted_disjunctions
    ; garbage = ref Set.empty
    ; dead = ref Set.empty
    }

let dfs_map abs x = abs.dfs_map.[x]
let dfs_add abs x =
    if not (abs.dfs_map.ContainsKey x) then
        abs.dfs_map.[x] <- !abs.dfs_cnt
        incr abs.dfs_cnt
let dfs_visited abs x = abs.dfs_map.ContainsKey(x)

let psi abs v = abs.psi.[v] |> Set.toList |> Formula.conj
let abs_node_to_program_loc abs v = abs.abs_node_to_program_loc.[v]
let program_loc_to_abs_nodes abs v = abs.program_loc_to_abs_nodes.[v]
let get_same_pc abs v = abs_node_to_program_loc abs v |> program_loc_to_abs_nodes abs
let abs_edge_to_program_commands abs x y = abs.abs_edge_to_program_commands.[x,y]
let parent abs v = if v=0 then None else Some(abs.parent.[v])
let leaf abs v = Set.contains v !abs.leaves
let remove_leaf abs v = abs.leaves := Set.remove v !abs.leaves
let add_leaf abs v = abs.leaves := Set.add v !abs.leaves
let rm_from_covering abs f =
    let the_filter x y =
        if not (f (x, y)) then true
        else inc_stat "uncovered vertex"; false
    abs.covering := Map.filter the_filter !abs.covering

let add_covering abs a b =
    abs.covering := Map.add a b !abs.covering
let rm_from_leaves abs f =
    abs.leaves := Set.filter (f >> not) !abs.leaves

let rec descendents abs t = [
    for c in abs.E.[t] do
        yield c
        yield! descendents abs c
    ]

/// Sanity check to be used before using a node
let check_not_removed abs x =
    if !gc_check then
         if Set.contains x !abs.dead then
             printf "CHECK_NOT_REMOVED FAILED"
             assert(false);

/// dump abstraction graph to file for debugging
let db (pars : Parameters.parameters) abs =
    let dot_abs_state abs =
        let pp_psi_nl abs v =
            let mutable st = "\\n\\n"
            for s in abs.psi.[v] do
                st <- st ^ (sprintf "%s\\n" (Formula.pp s))
            st
        let vertex_list = Set.map (fun v -> sprintf "%d [label=\"%d (node %d): %s\"]\n" v (abs_node_to_program_loc abs v) v (pp_psi_nl abs v)) !abs.V
        let vertices = Set.fold (fun x s -> x ^ s) "" vertex_list
        //let edges = abs.E.Fold (fun s (x, y) -> s ^ (sprintf "%d -> %d [label=\"%s\"]\n" x y (Programs.commands2pp (edge_map abs x y)))) ""
        let edges = abs.E.Fold (fun s (x, y) -> s ^ (sprintf "%d -> %d\n" x y)) ""
        let covering = Map.fold (fun s x y -> (sprintf "%d -> %d [style=dotted, constraint=false]\n" x y) ^ s) "" !abs.covering
        sprintf "\ndigraph program {\n%s\n%s\n\n%s}" vertices edges covering

    let write_to_fresh_file (s : string) =
        let mutable n = 0
        let mutable filename = sprintf "impact%03d.dot" n

        while System.IO.File.Exists filename do
            n <- n+1
            filename <- sprintf "impact%03d.dot" n

        Log.log pars <| sprintf "Reachability graph dumped to file %s" filename

        let f = System.IO.File.CreateText filename
        f.Write s
        f.Close()

    if pars.dottify_reachability  then
        dot_abs_state abs |> write_to_fresh_file
        ()

/// Procedure for removing from the graph. I'm being pretty aggressive right now
/// because in early days I was seeing lots of performance bugs due to reasoning about dead
/// nodes.
let delete_tree abs t =
    let desc = descendents abs t |> Set.ofList
    abs.dead := Set.union !abs.dead desc

    rm_from_covering abs (fun (x, y) -> desc.Contains x || desc.Contains y)
    let edges_to_remove = abs.abs_edge_to_program_commands.Keys |> Seq.filter (fun (x, y) -> (desc.Contains x) || (desc.Contains y)) |> List.ofSeq
    for edge_to_remove in edges_to_remove do
        abs.abs_edge_to_program_commands.Remove edge_to_remove |> ignore
    abs.V := Set.difference (!abs.V) desc
    abs.leaves := Set.difference (!abs.leaves) desc

    for n in desc do
        abs.parent.[n] <- -1
        abs.psi.[n] <- Set.empty
        abs.program_loc_to_abs_nodes.RemoveKeyVal abs.abs_node_to_program_loc.[n] n
        abs.abs_node_to_program_loc.[n] <- -1
        abs.fc_candidates.[n] <- None

    // We're cleaning out abs.fc_candidates in the get_force_cover_candidates routine
    let keep x = not (Set.contains x desc)
    abs.stack := filter_priostack keep !abs.stack
    abs.leaves := Set.difference !abs.leaves desc

    for d in (desc.Add t) do
        while abs.E.ContainsKey d do
            abs.E.Remove d |> ignore

///Delete everything from the graph that used/used some program transition:
let delete_program_transition abs ((k, cmds, k') : (int * Programs.command list * int)) =
    //For each transition to remove, get the representatives of the source, fish out those out-edges that correspond to the trans, remove those children:
    if not(abs.program_loc_to_abs_nodes.ContainsKey k) || not(abs.program_loc_to_abs_nodes.ContainsKey k') then
        ()
    else
    let k_reps = program_loc_to_abs_nodes abs k
    let k'_reps = program_loc_to_abs_nodes abs k'
    for k_rep in k_reps do
        if (abs.parent.[k_rep] <> -1) then //Avoid accessing things we removed
            for k_rep_succ in abs.E.[k_rep] do
                if (abs.parent.[k_rep_succ] <> -1) then //Avoid accessing things we removed
                    if k'_reps.Contains k_rep_succ then
                        //Check that we have the right commands here:
                        if (abs.abs_edge_to_program_commands.[k_rep, k_rep_succ] = cmds) then
                            //Delete everything that was created using this transition:
                            delete_tree abs k_rep_succ

/// Garbage collection procedure.  Roots of trees become garbage when their interpolant becomes "false".
/// The procedure for strengthening interpolants checks for unsat and puts nodes in !abs.garbage when this
/// condition is met.
let gc abs =
    if !do_gc then
        for v in !abs.garbage do
            if Set.contains v !abs.V then
                delete_tree abs v
        abs.garbage := Set.empty

let garbage_add abs v =
    if !do_gc then
        abs.garbage := Set.add v !abs.garbage

let garbage_check abs v =
    if !do_gc then
        if Formula.unsat (psi abs v) then
            abs.garbage := Set.add v !abs.garbage

/// Strengthen the invariant at a node.
let conjoin_with_psi abs l psi =
    let add n xs =
       if Formula.is_true_formula n then
           xs
       else if Formula.is_false_formula n then
           Set.singleton n
       else if Formula.unsat (n::Set.toList xs |> Formula.conj) then
           Set.singleton Formula.falsec
       else
           let p x = Formula.entails n x |> not
           let xs' = Set.filter p xs
           Set.add n xs'

    abs.psi.[l] <- add psi abs.psi.[l]

    garbage_check abs l

let add_V abs w = abs.V := Set.add w !abs.V
let add_E abs v w = abs.E.Add (v, w); abs.parent.[w] <- v

let new_vertex abs =
    inc_stat "created new vertex"
    let v = !abs.cnt
    let new_v = v + 1
    assert (new_v > v);
    abs.cnt := new_v
    v

/// x is y, parent of y, grandparent of y, etc.
let rec sq_eq abs x y =
    check_not_removed abs x
    check_not_removed abs y
    if x = y then
        true
    else
        match parent abs y with
        | Some(v) -> sq_eq abs x v
        | None -> false

/// x is parent of y, grandparent of y, etc.
let sq abs x y = x <> y && sq_eq abs x y

/// Compute ancestors
let ancestors abs v =
    let rec compute_ancestors abs v =
        check_not_removed abs v
        match parent abs v with
        | Some(w) -> w :: (compute_ancestors abs w)
        | None -> []
    compute_ancestors abs v

/// Returns true if the node is covered by an induction covering, or if its parent is.
let rec is_covered abs v =
    check_not_removed abs v
    if Map.containsKey v (!abs.covering) then
        true
    else if Formula.unsat (psi abs v) then
        true
    else
        match parent abs v with
        | Some(w) -> is_covered abs w
        | None -> false
let not_covered abs v = not (is_covered abs v)


/// This computes candidates for coverings (it uses abs.fc_candidates to cache results
/// -- the set of candidates can never grow, as we are only considering things that were computed before)
let get_force_cover_candidates abs v =
    check_not_removed abs v
    let dfs_v = dfs_map abs v
    let candidates =
        match abs.fc_candidates.[v] with
        | Some(candidates) -> candidates

        // We look at nodes at the same location the original program
        | None ->
            get_same_pc abs v
            // We have to filter out nodes that are in in the DFS stack but haven't actually
            // been visited yet
            |> Set.filter (dfs_visited abs)
            // We can only be covered by nodes less than us in the DFS order
            // (otherwise we could great circular/unsound induction arguments)
            |> Set.filter (fun w -> dfs_map abs w < dfs_v)
            // We don't want our children, obviously
            |> Set.filter (fun w -> not (sq_eq abs v w))
            // Sort in reverse dfs-search order
            |> Set.toList |> List.sortBy (dfs_map abs) |> List.rev

    // We're gc-ing here, as it's a little faster.
    let cleaned = List.filter (fun x -> (!abs.dead).Contains x |> not) candidates
    abs.fc_candidates.[v] <- Some(cleaned)
    List.filter (not_covered abs) cleaned

/// Find the path from node x to node y in the tree, given that x sqeq y
let find_path_from abs x y =
    let commands = ref []
    let curNode = ref y
    while !curNode <> x do
        let parentNode = parent abs !curNode
        assert (parentNode.IsSome)
        let parentNode = parentNode.Value
        let curCommands = [for c in abs_edge_to_program_commands abs parentNode !curNode -> (parentNode, c, !curNode)]
        commands := curCommands @ !commands
        curNode := parentNode
    !commands

/// Find the path from the root of the tree to x
let find_path abs x =
    // 0 is root
    assert ((parent abs 0).IsNone)
    find_path_from abs 0 x

let entails_psi abs x y =
    check_not_removed abs x
    check_not_removed abs y
    Formula.entails  (Formula.conj abs.psi.[x]) (Formula.conj abs.psi.[y])

let entails1_psi abs x f =
    check_not_removed abs x
    Formula.entails  (Formula.conj abs.psi.[x]) f

/// Make a new node "w" and add the edge expandedNode---commandsOnEdge--->newNode,
/// where newNode maps to location newNodeLoc from the original program
let make_node abs expandedNode commandsOnEdge newNodeLoc =
    let newNode = new_vertex abs
    add_V abs newNode
    add_E abs expandedNode newNode
    abs.abs_node_to_program_loc.[newNode] <- newNodeLoc
    abs.program_loc_to_abs_nodes.Add (newNodeLoc, newNode)
    let commandsOnEdge = if commandsOnEdge = [] then [Programs.skip] else commandsOnEdge
    assert (not <| abs.abs_edge_to_program_commands.ContainsKey (expandedNode, newNode))
    abs.abs_edge_to_program_commands.[(expandedNode, newNode)] <- commandsOnEdge
    add_leaf abs newNode
    newNode

/// Expand the graph for DFS search
let expand (pars : Parameters.parameters) abs v =
    assert (leaf abs v)
    db pars abs
    check_not_removed abs v

    inc_stat "expand vertex"
    if pars.print_log then
        Log.log pars <| sprintf "Expanding leaf %d (loc %d)" v abs.abs_node_to_program_loc.[v]

    if not (is_covered abs v) then
        remove_leaf abs v
        [for (T, m) in abs.transition (abs_node_to_program_loc abs v) do
            let to_add = ref true
            let psi = psi abs v
            if (not <| Formula.unsat psi) && !to_add then
                yield make_node abs v T m
        ] |> List.rev
    else
        []

let rec path_to_locs pi =
    match pi with
    | (l1, _, _) :: next :: rest -> l1 :: (path_to_locs (next :: rest))
    | (l1, _, l2) :: [] -> [l1; l2]
    | [] -> []

/// Try to cover v with w.  That is, v entails w, where v is later in the execution and the cover
/// represents the induction check
let cover (pars : Parameters.parameters) abs v w =
    assert (abs_node_to_program_loc abs v = abs_node_to_program_loc abs w)
    db pars abs
    if entails_psi abs v w then
        rm_from_covering abs (fun (_, y) -> sq_eq abs v y)
        add_covering abs v w
        true
    else
        false

/// If cover doesnt work, we can try to force it to work by (in a sense) merging paths
/// and finding necessary interpolants along the way
let force_cover (pars : Parameters.parameters) abs v w =
    db pars abs

    check_not_removed abs v
    check_not_removed abs w
    assert (abs_node_to_program_loc abs v = abs_node_to_program_loc abs w)

    if (Formula.unsat (psi abs v)) then
            garbage_add abs v
            false
    else if (Formula.unsat (psi abs w)) then
            garbage_add abs w
            false
    else

    let x_nearest =
        let v_ancestors = v :: (ancestors abs v) |> Set.ofList
        let w_ancestors = w :: (ancestors abs w) |> Set.ofList
        let common = Set.intersect v_ancestors w_ancestors |> Set.toList
        List.maxBy (dfs_map abs) common
    assert (sq_eq abs x_nearest v && sq_eq abs x_nearest w)

    let psi_w =
        let psi_v_cs = abs.psi.[v]
        let psi_w_cs = abs.psi.[w]
        let common_cs = Set.intersect psi_w_cs psi_v_cs
        let psi_w_uncommon = Set.difference psi_w_cs common_cs
        Formula.conj psi_w_uncommon

    let get_formulae x path =
        let (formulae, var_map) =
            let assume_psi_x = (-1, Programs.assume (psi abs x), x)
            let assume_not_psi_w = (v, Programs.assume (Formula.Not (psi_w)), -1)
            let augmented_path = assume_psi_x :: path @ [assume_not_psi_w]
            let sliced_path = Symex.slice_path (collapse_path augmented_path) []
            let filtered_path = sliced_path |> List.tail |> List.all_but_last
            Symex.path_to_transitions_and_var_map filtered_path Map.empty
        let initial = abs.psi.[x] |> Set.toList
        let var_map = Symex.add_vars_to_map initial var_map
        let initial = List.map (Symex.substitute_map_in_formula Map.empty) initial
        let final = Symex.substitute_map_in_formula var_map psi_w
        initial, formulae, final, var_map

    let do_interpolants initial formulae final x path =
        let find_path_interpolant =
            if x = w || not (sq abs w v) then 
                Symex.find_path_interpolant_old pars (not pars.fc_unsat_core) 0 []
            else
                let (initial, formulae, _, var_map) = get_formulae x path
                let distance =
                    let rec distance_from w v =
                        if w = v then 0
                        else
                            match parent abs v with
                            | None -> assert false; 0
                            | Some pv -> 1 + (distance_from w pv)
                    distance_from w v
                let initial = Formula.conj initial
                let formulae = [for (_, fs, _) in formulae -> Formula.conj fs]
                let final =
                    let zero = Term.constant 0
                    let var v p = Term.var (Var.prime_var v p)
                    let gen_dummy_assign (v,p) = Formula.Eq(var v p, zero)
                    List.map gen_dummy_assign (Map.toList var_map) |> Formula.conj
                Symex.find_path_interpolant_old pars false distance ((initial::formulae)@[final; Formula.falsec])

        match find_path_interpolant formulae (Formula.conj initial) final with
        | Some(A) ->
            let update (loc,intp) =
                if not (entails1_psi abs loc intp) then
                    let split = Formula.split_conjunction  intp
                    List.iter (conjoin_with_psi abs loc) split
                    rm_from_covering abs (fun (x,y) -> y=loc && not (entails_psi abs x loc))
            List.zip (path_to_locs formulae) A |> List.iter update

            let covered = cover pars abs v w
            assert(covered)
            true
        | None ->
            Log.log pars <| "Failed to find path interpolant!"
            false

    let try_unsat_get_formulae x path =
        let (initial, formulae, final, _) = get_formulae x path
        let fs =
            [
                yield! initial

                for (_,y,_) in formulae do
                    yield! y

                yield (Formula.negate final)
            ] |> Formula.conj
        if Formula.unsat fs then
            Some (initial,formulae,final)
        else
            None

    let try_unsat_core_get_formulae x path =
        let (initial, formulae, final, _) = get_formulae x path
        let fs =
            [|
                yield! List.map Formula.z3 initial

                for (_,y,_) in formulae do
                    yield! List.map Formula.z3 y

                yield Formula.z3 (Formula.negate final)
            |]

        match Z.unsat_core fs with
        | None -> None
        | Some core ->
            let rec reduce fs core accum =
                match fs with
                | [] -> List.rev accum
                | f::fs_tail ->
                    match core with
                    | [] -> die ()
                    | c::core_tail ->
                        if c then reduce fs_tail core_tail (f::accum)
                        else reduce fs_tail core_tail accum

            let initial' = reduce initial core []
            let core = List.drop initial.Length core

            let formulae' =
                let rec reduce_formulae formulae core accum =
                    match formulae with
                    | [] -> assert (List.length core = 1); List.rev accum
                    | (n1,fs,n2)::formulae_tail ->
                        let fs' = reduce fs core []
                        reduce_formulae formulae_tail (List.drop fs.Length core) ((n1,fs',n2)::accum)
                reduce_formulae formulae core []

            let final' = if List.last core then final else Formula.falsec

            Some (initial',formulae',final')

    let result =
        let try_from_x =
            if pars.fc_unsat_core then try_unsat_core_get_formulae else try_unsat_get_formulae

        let nearest_path = find_path_from abs x_nearest v

        if pars.fc_look_back && x_nearest <> 0 then
            let root_path = (find_path_from abs 0 x_nearest)@nearest_path

            match try_from_x 0 root_path with
            | None -> false
            | Some (initial, formulae, final) ->
                match try_from_x x_nearest nearest_path with
                | None ->  do_interpolants initial formulae final 0 root_path
                | Some (initial, formulae, final) -> do_interpolants initial formulae final x_nearest nearest_path
        else
        match try_from_x x_nearest nearest_path with
        | None ->  false
        | Some (initial, formulae, final) -> do_interpolants initial formulae final x_nearest nearest_path

    if result then inc_stat "force cover succeeded"
    else inc_stat "force cover failed"

    result

/// Apply force_cover procedure as appropriate to the nodes in the graph.
let try_force_cover (pars : Parameters.parameters) abs v =
    check_not_removed abs v

    if not (dfs_visited abs v) then false
    else if is_covered abs v then true
    else

    let rec try_force_cover_candidates candidates failed_candidates changed =
        match candidates with
        | [] -> false, (List.rev failed_candidates), changed
        | w::t ->
            check_not_removed abs w
            if cover pars abs v w || force_cover pars abs v w then (true, (List.rev failed_candidates)@candidates, changed)
            else
                if sq abs w v then
                    // because w is ancestor of v, it is possible we failed but when invar(w) is refined we will succeed
                    // therefore we do not remove w from the candidates list
                    try_force_cover_candidates t (w::failed_candidates) changed
                else
                    try_force_cover_candidates t failed_candidates true

    let covered, candidates, changed = try_force_cover_candidates (get_force_cover_candidates abs v) [] false

    // most of the times the candidates do not change so we write back only when needed (i.e. when 'changed' is true)
    if changed && pars.fc_remove_on_fail then abs.fc_candidates.[v] <- Some candidates

    covered

/// This procedure attempts to find a cover for v.
let close (pars : Parameters.parameters) abs v =
    db pars abs
    check_not_removed abs v
    assert (dfs_visited abs v)

    if is_covered abs v then
        true
    else
        try_force_cover pars abs v

/// Try to find coverings on all of the nodes above v
let close_all_ancestors (pars : Parameters.parameters) abs v =
    check_not_removed abs v
    let l = ancestors abs v |> List.rev |> ref
    let d = ref false
    while !l<>[] && not !d do
        d := close pars abs (List.head !l)
        l := List.tail !l
    done

/// If an error path was spurious, refine abstraction and return None.
/// Otherwise, return true (almost) error path.
let refine (pars : Parameters.parameters) abs v =
    db pars abs

    assert (abs_node_to_program_loc abs v = abs.loc_err)
    check_not_removed abs v

    if pars.print_log then
        Log.log pars <| sprintf "Refining %d (loc %d)..." v abs.abs_node_to_program_loc.[v]

    if Formula.unsat (psi abs v) then
        // In this case the error location is just not satisfible.
        // No interpolant needed.
        None
    else
        let pi = find_path abs v
        let pi' = Symex.slice_path (collapse_path pi) []
        let formulae = pi' |> Symex.path_to_formulae

        // Try to find interpolants (this may fail if we cannot find an interpolant for a true error)
        match Symex.find_unsat_path_interpolant pars formulae with
        | None ->
            let translate (k1, cmd, k2) = (abs_node_to_program_loc abs k1, cmd, abs_node_to_program_loc abs k2)
            Some(List.map translate pi,pi)

        | Some(interpolants) ->
            // Found a strengthening.  Now we apply it by conjoining the pieces along the states
            // in the Tree/Graph. This may make some coverings invalid, so we have to re-evaluate them
            // Note also that if we make some of the states unsatisfiable then this will eventually trigger
            // a GC on the subtree underneath them.
            let interpolants = Formula.truec::interpolants@[Formula.falsec]
            for loc, intp in List.zip (path_to_locs formulae) interpolants do
                check_not_removed abs loc
                if not (entails1_psi abs loc intp) then
                    if pars.print_log then
                        Log.log pars <| sprintf " Adding interpolant %s to %i (loc %i)" intp.pp loc abs.abs_node_to_program_loc.[loc]
                    conjoin_with_psi abs loc intp
                    rm_from_covering abs (fun (x,y) -> y=loc && not (entails_psi abs x loc))

            conjoin_with_psi abs v (Formula.falsec)
            None

/// <summary>
/// Depth first search:  in this procedure we start building the tree in a DFS manner until we hit
/// what we think might be an error.
/// </summary>
///
/// <remarks>
/// Things get a little complex.
/// We're trying to approximate a convex analysis as much as possible.  If we see some transition
/// cmd1;cmd2;cmd3 where cmd2 is a disjunction (e.g. assume(x &gt; 0 || y &lt; 2) or  assume(x!=y)),
/// then we will have replaced that with a cmd2' which is an overapproximation.
/// We now need to make it possible to refine this again. For this, we return a thunk in a
/// callback to the caller.  It may be that they (e.g. the termination prover) can still find
/// a ranking function even with the spurious approximation cmd1;cmd2';cmd3.
/// </remarks>
///
let dfs (pars : Parameters.parameters) abs start =
    db pars abs
    // Start the ball rolling.  The priority doesn't matter, since we're just going
    // to pop it below.
    abs.stack := singleton_priostack 0 start

    let ret = ref None
    while not(isempty_priostack !abs.stack) && (!ret).IsNone do
        let (v, s') = pop_priostack !abs.stack
        abs.stack := s'

        // The call to dfs_add gives v its DFS ordering number.
        dfs_add abs v

        if not (close pars abs v) then
            // v isn't covered as a result of closing it, so we need to
            // refine it if it's an error location or expand it otherwise.
            if abs_node_to_program_loc abs v = abs.loc_err then
                match refine pars abs v with
                | Some(pi, abs_pi) ->
                    // This is a real error, and the path pi witnesses it.
                    // Due to incrementality we need to add v back as a leaf, as we may be back here.
                    add_leaf abs v

                    let used_disjs =
                        if !refine_disj then
                            List.fold
                                (fun used_disjs (x, cmd, y) ->
                                    match cmd with
                                    | Assign(_,v,_) when Formula.is_disj_var v ->
                                      (x,v,y) :: used_disjs
                                    | _ -> used_disjs)
                                []
                                abs_pi
                        else
                            []

                    match used_disjs with
                    | [] ->
                        // No abstracted disjunction used.
                        ret := Some (pi, [])
                    | _ ->
                        // Found a disjunction. Make thunks that will refine the Tree/Graph
                        let make_disj_refinement_callback (k,v,k') () =
                            let abstracted_disjunction = Map.find v abs.abstracted_disjunctions
                            match abstracted_disjunction with
                            | (first_disjunct::disjunctions) ->
                                Log.log pars <| sprintf "Lazy disjunction expansion for %s" v
                                //Replace existing edge (with abstract label) by the first disjunct
                                abs.abs_edge_to_program_commands.[(k,k')] <- [first_disjunct]
                                //Add new edges for the other disjuncts
                                for other_disjunct in disjunctions do
                                    make_node abs k [other_disjunct] (abs_node_to_program_loc abs k') |> ignore
                            | _ -> die()
                        let disjunctive_refinements = List.map make_disj_refinement_callback used_disjs

                        ret := Some (pi, disjunctive_refinements)
                | None ->
                    // In this case we haven't hit an error node (yet).
                    ignore (close pars abs v)
                    close_all_ancestors pars abs v
            else
                let children = expand pars abs v
                push_priostack_abs_many abs children

    !ret

/// pick uncovered leaf that
///   a) preferably corresponds to error loc
///   b) is earliest in dfs order
let pick_vertex abs =
    let error_nodes, other_nodes =
        !abs.leaves
        |> Seq.filter (not_covered abs)
        |> Seq.toList
        |> List.partition (fun v -> abs_node_to_program_loc abs v = abs.loc_err)

    if not error_nodes.IsEmpty then
        List.minBy (dfs_map abs) error_nodes
    elif not other_nodes.IsEmpty then
        List.minBy (dfs_map abs) other_nodes
    else
        die()

let unwind (pars : Parameters.parameters) abs =
    db pars abs
    let v = pick_vertex abs
    Log.log pars <| sprintf "Unwinding node %d (loc %d)" v abs.abs_node_to_program_loc.[v]
    close_all_ancestors pars abs v
    dfs pars abs v

//
// Sanity checks
//

let sanity_check abs =
    if Map.exists (fun x y -> entails_psi abs x y |> not) !abs.covering then
        printf "BIG PROBLEM!\n"

    if Map.exists (fun _ y -> ancestors abs y |> List.forall (fun a -> not (Map.containsKey a !abs.covering)) |> not) !abs.covering then
        printf "BIG PROBLEM 2x!\n"

/// Return path to loc_err or None if it's unreachable
let reachable (pars : Parameters.parameters) abs =
    db pars abs
    let path = ref None
    while Set.exists (not_covered abs) !abs.leaves && (!path).IsNone do
        match unwind pars abs with
        | Some(pi, disjunction_refinements) ->
                let (_, _, l2) = List.last pi
                assert (l2 = abs.loc_err)
                path := Some(pi, disjunction_refinements)
        | None -> ()

        gc abs
    done

    // Check that we we've constructed a consistent proof graph
    if pars.sanity_checking then
        sanity_check abs

    db pars abs
    !path

/// For incrementality, we sometimes need to delete a subtree within the proof graph
let reset abs s =
    let nodes = Set.filter (fun x -> abs_node_to_program_loc abs x = s) !abs.V |> ref
    while !nodes<>Set.empty do
        let t = Set.minElement !nodes
        nodes := Set.remove t !nodes
        delete_tree abs t
        add_leaf abs t

        // The deleted tree might have made nodes disappear
        nodes := Set.intersect !nodes !abs.V

/// Great an initial reachability Tree/Graph
let init init_loc error_loc transition prio abstracted_disjunctions =
    let abs = make_abs_pgm init_loc error_loc transition prio abstracted_disjunctions
    let newNode = new_vertex abs
    add_V abs newNode
    add_leaf abs newNode
    abs.abs_node_to_program_loc.[newNode] <- init_loc
    abs.program_loc_to_abs_nodes.Add (init_loc, newNode)
    abs

/// Prove that location err is unreachable in p
let prover (pars : Parameters.parameters) p err =
    Utils.timeout pars.timeout

    assert (not pars.lazy_disj && not pars.abstract_disj); //Overapproximations are very uncool for reachability

    // Create new initial location with transition assume(_const_100 > _const_32) for all
    // abstracted const variables.
    Programs.symbconsts_init p

    // The connection between programs and Graph is a little bit messy
    // at the moment. We have to marshal a little bit of data between them
    let transition = Programs.transitions_from p
    let abs = init !p.initial err transition None !p.abstracted_disjunctions

    if pars.dottify_input_pgms then
        Output.print_dot_program p "input.dot"

    // Try to disprove/prove the error location in abs to be unreachable
    let r = reachable pars abs

    // If the flag is set, produce a counterexample file
    if pars.safety_counterexample && r.IsSome then
        let stem = Some (List.map (fun (x,y,z) -> (x,[y],z)) (fst r.Value))
        let cex = Counterexample.make stem None
        Counterexample.print_defect pars [cex] "defect.tt"
        Counterexample.print_program pars [cex] "defect.t2"
        Utils.run_clear()

    Utils.reset_timeout()

    r