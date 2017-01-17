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


module Microsoft.Research.T2.Impact

open Utils
open Log
open PriorityQueue

let private make_prio_map (p: Programs.Program) (error_loc: int) =
    //bfs from error location on reversed transition relation, assigned prio is inverted minimal distance
    let in_trans = SetDictionary()
    let all_nodes = System.Collections.Generic.HashSet()
    for (k, cmds, k') in p.Transitions do
        in_trans.Add (k', (k, cmds, k'))
        all_nodes.Add k |> ignore
        all_nodes.Add k' |> ignore

    let res = System.Collections.Generic.Dictionary()
    let todo = new System.Collections.Generic.Queue<int * int>()
    todo.Enqueue(error_loc, 0)

    while todo.Count > 0 do
        let (node, dist) = todo.Dequeue()
        if not (res.ContainsKey node) then
            res.[node] <- dist
            for (pred, _, _) in in_trans.[node] do
                todo.Enqueue(pred, dist - 1)

    //Whoever has no weight does not even reach error_loc. Make them go last:
    for node in all_nodes do
        if not (res.ContainsKey node) then
            res.[node] <- System.Int32.MinValue

    res

/// Should we perform garbage collection on the abstraction graph?
let private do_gc = true

/// Should we perform some sanity checks to make sure that we're not using
/// nodes that have been GC'd?
let private gc_check = false

type ImpactARG(parameters : Parameters.parameters,
               program : Programs.Program,
               loc_err : int) =
    /// Initial program location
    let loc_init = program.Initial

    /// Transition relation, mapping each location to a list of (relation, successor location) pairs.
    /// Note that this reflects changes to program that are done while this is ARG is instantiated.
    let transition loc = List.rev <| program.TransitionsFrom loc

    /// Priority of each node in the original program.  Used to choose which node to take during DFS
    let priority = make_prio_map program loc_err

    /// Tree/Graph constructon representing the state of the safety proof procedure.  Back edges
    /// in the "covering" relations represent induction checks.  At the end of a successful proof
    /// search this graph should represent a valid proof of safety which could be spit out to a
    /// theorem prover.  Note that for performance there is A LOT of redundency in this graph. Its
    /// RIDDLED with invariants. Fun.
    (* ------- State of the abstract reachability graph ------- *)
    /// Counter tracking how many nodes we have in the system
    let mutable cnt = 0

    /// Current nodes in the system
    let V = System.Collections.Generic.HashSet<int>()

    /// Edge relation
    let E = new SetDictionary<int,int>()

    /// parents in the graph
    let parent = new DefaultDictionary<int,int>(fun _ -> -1)

    /// Set of interpolants (understood as conjunction) for each node
    let psi = new DefaultDictionary<int,Set<Formula.formula>>(fun _ -> Set.empty)

    /// Current leaves in the execution tree
    let leaves = System.Collections.Generic.HashSet<int>()

    /// Mapping from edges in the execution tree to the commands in the original program
    let abs_edge_to_program_commands = System.Collections.Generic.Dictionary<int * int, int * Programs.Command list>()

    /// Mapping from nodes in the execution tree to the original program
    let abs_node_to_program_loc = DefaultDictionary<int,int>(fun _ -> -1)

    /// A node n\in representatives(k) if n in the graph maps back to k in the original program.
    /// i.e. if n\in representatives(k) then node_map n = k
    let program_loc_to_abs_nodes = SetDictionary<int,int>()

    /// Induction coverings
    let covering = System.Collections.Generic.Dictionary<int, int>()

    /// Per-node list of candidates that we should search for when looking for a force cover
    let fc_candidates = new DefaultDictionary<int,int list option>(fun _ -> None)

    /// Node numbers do not quite represent the order that we've "visited" them. dfs_map maps each node number to its dfs number
    let dfs_map = DefaultDictionary<int, int>(fun _ -> -1)
    /// Helper to create dfs numbers
    let mutable dfs_cnt = 0

    let init_node = 0

    /// The priority queue used during DFS.
    let stack = PriorityQueue<int>()

    /// Nodes that have been deemed as garbage but havent been GC'd yet.
    let garbage = System.Collections.Generic.HashSet<int>()

    /// Nodes that were in the system but have now been dead and GC'd
    let dead = System.Collections.Generic.HashSet<int>()

    let new_vertex () =
        Stats.incCounter "Impact - Created vertices"
        let v = cnt
        cnt <- cnt + 1
        v
    let add_V w = V.Add w |> ignore
    let add_E v w =
        E.Add (v, w)
        parent.[w] <- v
    let add_leaf v = leaves.Add v |> ignore

    do
        let newNode = new_vertex ()
        add_V newNode
        add_leaf newNode
        abs_node_to_program_loc.[newNode] <- loc_init
        program_loc_to_abs_nodes.Add (loc_init, newNode)

    member private __.dfs_add x =
        if not (dfs_map.ContainsKey x) then
            dfs_map.[x] <- dfs_cnt
            dfs_cnt <- dfs_cnt + 1
    member private __.dfs_visited x = dfs_map.ContainsKey(x)

    member private __.psi v = psi.[v] |> Formula.conj
    member private __.get_same_pc v = program_loc_to_abs_nodes.[abs_node_to_program_loc.[v]]
    member private __.parent v = if v = 0 then None else Some parent.[v]
    member private __.leaf v = leaves.Contains v
    member private __.remove_leaf v = leaves.Remove v |> ignore
    member private __.rm_from_covering f =
        let mutable toRemove = []
        for kv in covering do
            if f (kv.Key, kv.Value) then
                Stats.incCounter "Impact - Uncovered vertices"
                toRemove <- kv.Key :: toRemove
        covering.RemoveAll toRemove

    member private __.add_covering a b = covering.Add (a, b)

    member private self.descendents t = [
        for c in E.[t] do
            yield c
            yield! self.descendents c
        ]

    /// Sanity check to be used before using a node
    member private __.check_not_removed x =
        if gc_check then
             if dead.Contains x then
                 printf "CHECK_NOT_REMOVED FAILED"
                 assert(false);

    /// dump abstraction graph to file for debugging
    member private self.db () =
        let write_to_fresh_file (s : string) =
            let mutable n = 0
            let mutable filename = sprintf "impact%03d.dot" n

            while System.IO.File.Exists filename do
                n <- n+1
                filename <- sprintf "impact%03d.dot" n

            Log.debug parameters <| sprintf "Reachability graph dumped to file %s" filename

            let f = System.IO.File.CreateText filename
            f.Write s
            f.Close()

        if parameters.dottify_reachability  then
            let dot_abs_state =
                let pp_psi_nl v =
                    let mutable st = "\\n\\n"
                    for s in psi.[v] do
                        st <- st + (sprintf "%s\\n" (Formula.pp s))
                    st
                let vertex_list = Seq.map (fun v -> sprintf "%d [label=\"%d (node %d): %s\"]\n" v abs_node_to_program_loc.[v] v (pp_psi_nl v)) V
                let vertices = Seq.fold (fun x s -> x + s) "" vertex_list
                let edges = E.Fold (fun res sourceLoc targetLocs -> Set.fold (fun res targetLoc -> sprintf "%s%d -> %d\n" res sourceLoc targetLoc) res targetLocs) ""
                let covering = Seq.fold (fun s (t : System.Collections.Generic.KeyValuePair<int,int>) -> (sprintf "%d -> %d [style=dotted, constraint=false]\n" t.Key t.Value) + s) "" covering
                sprintf "\ndigraph program {\n%s\n%s\n\n%s}" vertices edges covering
            dot_abs_state |> write_to_fresh_file
            ()

    /// Procedure for removing from the graph. I'm being pretty aggressive right now
    /// because in early days I was seeing lots of performance bugs due to reasoning about dead
    /// nodes.
    member private self.delete_tree t =
        let desc = self.descendents t |> Set.ofList
        dead.AddAll desc

        self.rm_from_covering (fun (x, y) -> desc.Contains x || desc.Contains y)
        let edges_to_remove = abs_edge_to_program_commands.Keys |> Seq.filter (fun (x, y) -> (desc.Contains x) || (desc.Contains y)) |> List.ofSeq //Otherwise, we run into a concurrent modification
        for edge_to_remove in edges_to_remove do
            abs_edge_to_program_commands.Remove edge_to_remove |> ignore
        V.RemoveAll desc
        leaves.RemoveAll desc

        for n in desc do
            parent.[n] <- -1
            psi.[n] <- Set.empty
            program_loc_to_abs_nodes.RemoveKeyVal abs_node_to_program_loc.[n] n
            abs_node_to_program_loc.[n] <- -1
            fc_candidates.[n] <- None

        // We're cleaning out fc_candidates in the get_force_cover_candidates routine
        stack.RemoveWhere (fun v -> Set.contains v desc)
        leaves.RemoveAll desc

        for d in (desc.Add t) do
            while E.ContainsKey d do
                E.Remove d |> ignore

    /// Garbage collection procedure.  Roots of trees become garbage when their interpolant becomes "false".
    /// The procedure for strengthening interpolants checks for unsat and puts nodes in garbage when this
    /// condition is met.
    member private self.gc () =
        if do_gc then
            for v in garbage do
                if V.Contains v then
                    self.delete_tree v
            garbage.Clear()

    member private __.garbage_add v =
        if do_gc then
            garbage.Add v |> ignore

    member private self.garbage_check v =
        if do_gc then
            if Formula.unsat (self.psi v) then
                garbage.Add v |> ignore

    /// Strengthen the invariant at a node.
    member private self.conjoin_with_psi l newPsi =
        let add n xs =
           if Formula.is_true_formula n then
               xs
           else if Formula.is_false_formula n then
               Set.singleton n
           else if Formula.unsat (Formula.conj (Seq.append [n] xs)) then
               Set.singleton Formula.falsec
           else
               let p x = Formula.entails n x |> not
               let xs' = Set.filter p xs
               Set.add n xs'

        psi.[l] <- add newPsi psi.[l]

        self.garbage_check l

    /// x is y, parent of y, grandparent of y, etc.
    member private self.sq_eq x y =
        self.check_not_removed x
        self.check_not_removed y
        if x = y then
            true
        else
            match self.parent y with
            | Some v -> self.sq_eq x v
            | None -> false

    /// x is parent of y, grandparent of y, etc.
    member private self.sq x y = x <> y && self.sq_eq x y

    /// Compute ancestors
    member private self.ancestors v =
        let rec compute_ancestors v =
            self.check_not_removed v
            match self.parent v with
            | Some w -> w :: (compute_ancestors w)
            | None -> []
        compute_ancestors v

    /// Returns true if the node is covered by an induction covering, or if its parent is.
    member private self.is_covered v =
        self.check_not_removed v
        if covering.ContainsKey v then
            true
        else if Formula.unsat (self.psi v) then
            true
        else
            match self.parent v with
            | Some w -> self.is_covered w
            | None -> false
    member private self.not_covered v = not (self.is_covered v)


    /// This computes candidates for coverings (it uses fc_candidates to cache results
    /// -- the set of candidates can never grow, as we are only considering things that were computed before)
    member private self.get_force_cover_candidates v =
        self.check_not_removed v
        let dfs_v = dfs_map.[v]
        let candidates =
            match fc_candidates.[v] with
            | Some candidates -> candidates

            // We look at nodes at the same location the original program
            | None ->
                [
                    for v' in self.get_same_pc v do
                        // We have to filter out nodes that are in in the DFS stack but haven't actually
                        // been visited yet
                        if self.dfs_visited v' then
                        // We can only be covered by nodes less than us in the DFS order
                        // (otherwise we could great circular/unsound induction arguments)
                            if dfs_map.[v'] < dfs_v then
                                // We don't want our children, obviously
                                if not (self.sq_eq v v') then
                                    yield v'
                // Sort in reverse dfs-search order
                ] |> List.sortBy (fun v -> -dfs_map.[v])

        // We're gc-ing here, as it's a little faster.
        let cleaned = List.filter (fun x -> dead.Contains x |> not) candidates
        fc_candidates.[v] <- Some cleaned
        List.filter self.not_covered cleaned

    /// Find the path from node x to node y in the tree, given that x sqeq y
    member private self.find_path_from x y =
        let mutable commands = []
        let curNode = ref y
        while !curNode <> x do
            let parentNode = self.parent !curNode
            assert (parentNode.IsSome)
            let parentNode = parentNode.Value
            let curCommands = [for c in snd abs_edge_to_program_commands.[parentNode, !curNode] -> (parentNode, c, !curNode)]
            commands <- curCommands @ commands
            curNode := parentNode
        commands

    /// Find the path from the root of the tree to x
    member private self.find_path x =
        // 0 is root
        assert ((self.parent 0).IsNone)
        self.find_path_from 0 x

    member private self.entails_psi x y =
        self.check_not_removed x
        self.check_not_removed y
        Formula.entails  (Formula.conj psi.[x]) (Formula.conj psi.[y])

    member private self.entails1_psi x f =
        self.check_not_removed x
        Formula.entails  (Formula.conj psi.[x]) f

    /// Make a new node "w" and add the edge expandedNode---commandsOnEdge--->newNode,
    /// where newNode maps to location newNodeLoc from the original program
    member private __.make_node expandedNode transId commandsOnEdge newNodeLoc =
        let newNode = new_vertex ()
        add_V newNode
        add_E expandedNode newNode
        abs_node_to_program_loc.[newNode] <- newNodeLoc
        program_loc_to_abs_nodes.Add (newNodeLoc, newNode)
        let commandsOnEdge = if commandsOnEdge = [] then [Programs.skip] else commandsOnEdge
        assert (not <| abs_edge_to_program_commands.ContainsKey (expandedNode, newNode))
        abs_edge_to_program_commands.[(expandedNode, newNode)] <- (transId, commandsOnEdge)
        add_leaf newNode
        newNode

    /// Expand the graph for DFS search
    member private self.expand v =
        assert (self.leaf v)
        self.db ()
        self.check_not_removed v

        Stats.incCounter "Impact - Expanded vertices"
        if parameters.print_debug then
            Log.debug parameters <| sprintf "Expanding leaf %d (loc %d)" v abs_node_to_program_loc.[v]

        if not (self.is_covered v) then
            self.remove_leaf v
            [for (id, (_, T, m)) in transition abs_node_to_program_loc.[v] do
                if (not <| Formula.unsat (self.psi v)) then
                    let new_node = self.make_node v id T m
                    Log.debug parameters <| sprintf "  Expanded to %d (loc %d)" new_node m
                    yield new_node
            ] |> List.rev
        else
            []

    member private self.path_to_locs pi =
        match pi with
        | (l1, _, _) :: next :: rest -> l1 :: (self.path_to_locs (next :: rest))
        | (l1, _, l2) :: [] -> [l1; l2]
        | [] -> []

    /// Try to cover v with w.  That is, v entails w, where v is later in the execution and the cover
    /// represents the induction check
    member private self.cover v w =
        assert (abs_node_to_program_loc.[v] = abs_node_to_program_loc.[w])
        self.db ()
        if self.entails_psi v w then
            self.rm_from_covering (fun (_, y) -> self.sq_eq v y)
            self.add_covering v w
            true
        else
            false

    /// If cover doesnt work, we can try to force it to work by (in a sense) merging paths
    /// and finding necessary interpolants along the way
    member private self.force_cover v w =
        self.db ()

        self.check_not_removed v
        self.check_not_removed w
        assert (abs_node_to_program_loc.[v] = abs_node_to_program_loc.[w])

        if (Formula.unsat (self.psi v)) then
                self.garbage_add v
                false
        else if (Formula.unsat (self.psi w)) then
                self.garbage_add w
                false
        else

        let x_nearest =
            let v_ancestors = v :: (self.ancestors v) |> Set.ofList
            let w_ancestors = w :: (self.ancestors w) |> Set.ofList
            let common = Set.intersect v_ancestors w_ancestors
            Seq.maxBy (fun v -> dfs_map.[v]) common
        assert (self.sq_eq x_nearest v && self.sq_eq x_nearest w)

        let psi_w =
            let psi_v_cs = psi.[v]
            let psi_w_cs = psi.[w]
            let common_cs = Set.intersect psi_w_cs psi_v_cs
            let psi_w_uncommon = Set.difference psi_w_cs common_cs
            Formula.conj psi_w_uncommon

        let get_formulae x path =
            let (formulae, var_map) =
                let assume_psi_x = (-1, Programs.assume (self.psi x), x)
                let assume_not_psi_w = (v, Programs.assume (Formula.Not psi_w), -1)
                let augmented_path = assume_psi_x :: path @ [assume_not_psi_w]
                let sliced_path = Symex.slice_path (Programs.collapse_path augmented_path) []
                let filtered_path = sliced_path |> List.tail |> List.all_but_last
                Programs.cmdPathToFormulaPathAndVarMap filtered_path Map.empty
            let initial = psi.[x] |> Set.toList
            let var_map = Programs.addVarsToVarMap initial var_map
            let initial = List.map (Symex.substitute_map_in_formula Map.empty) initial
            let final = Symex.substitute_map_in_formula var_map psi_w
            initial, formulae, final, var_map

        let do_interpolants initial formulae final x path =
            let find_path_interpolant =
                if x = w || not (self.sq w v) then
                    Symex.find_path_interpolant_old parameters (not parameters.fc_unsat_core) 0 []
                else
                    let (initial, formulae, _, var_map) = get_formulae x path
                    let distance =
                        let rec distance_from w v =
                            if w = v then 0
                            else
                                match self.parent v with
                                | None -> assert false; 0
                                | Some pv -> 1 + (distance_from w pv)
                        distance_from w v
                    let initial = Formula.conj initial
                    let formulae = [for (_, fs, _) in formulae -> Formula.conj fs]
                    let final =
                        let zero = Term.constant 0
                        let var v p = Term.var (Var.prime_var v p)
                        let gen_dummy_assign (v, p) = Formula.Eq(var v p, zero)
                        List.map gen_dummy_assign (Map.toList var_map) |> Formula.conj
                    Symex.find_path_interpolant_old parameters false distance ((initial::formulae)@[final; Formula.falsec])

            match find_path_interpolant formulae (Formula.conj initial) final with
            | Some A ->
                let update (loc, intp) =
                    if not (self.entails1_psi loc intp) then
                        let split = intp.SplitConjunction()
                        List.iter (self.conjoin_with_psi loc) split
                        self.rm_from_covering (fun (x, y) -> y=loc && not (self.entails_psi x loc))
                List.zip (self.path_to_locs formulae) A |> List.iter update

                let covered = self.cover v w
                assert (covered)
                true
            | None ->
                Log.log parameters <| "Failed to find path interpolant!"
                false

        let try_unsat_get_formulae x path =
            let (initial, formulae, final, _) = get_formulae x path
            let fs =
                [
                    yield! initial

                    for (_, y, _) in formulae do
                        yield! y

                    yield (Formula.negate final)
                ] |> Formula.conj
            if Formula.unsat fs then
                Some (initial, formulae, final)
            else
                None

        let try_unsat_core_get_formulae x path =
            let (initial, formulae, final, _) = get_formulae x path
            let fs =
                [|
                    yield! List.map Formula.z3 initial

                    for (_, y, _) in formulae do
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
                        | (n1, fs, n2)::formulae_tail ->
                            let fs' = reduce fs core []
                            reduce_formulae formulae_tail (List.drop fs.Length core) ((n1, fs', n2)::accum)
                    reduce_formulae formulae core []

                let final' = if List.last core then final else Formula.falsec

                Some (initial', formulae', final')

        let result =
            let try_from_x =
                if parameters.fc_unsat_core then try_unsat_core_get_formulae else try_unsat_get_formulae

            let nearest_path = self.find_path_from x_nearest v

            if parameters.fc_look_back && x_nearest <> 0 then
                let root_path = (self.find_path_from 0 x_nearest)@nearest_path

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

        if result then
            Stats.incCounter "Impact - Successful force covers"
        else
            Stats.incCounter "Impact - Failed force covers"

        result

    /// Apply force_cover procedure as appropriate to the nodes in the graph.
    member private self.try_force_cover v =
        self.check_not_removed v

        if not (self.dfs_visited v) then false
        else if self.is_covered v then true
        else

        let rec try_force_cover_candidates candidates failed_candidates changed =
            match candidates with
            | [] -> false, (List.rev failed_candidates), changed
            | w::t ->
                self.check_not_removed w
                if self.cover v w || self.force_cover v w then (true, (List.rev failed_candidates)@candidates, changed)
                else
                    if self.sq w v then
                        // because w is ancestor of v, it is possible we failed but when invar(w) is refined we will succeed
                        // therefore we do not remove w from the candidates list
                        try_force_cover_candidates t (w::failed_candidates) changed
                    else
                        try_force_cover_candidates t failed_candidates true

        let covered, candidates, changed = try_force_cover_candidates (self.get_force_cover_candidates v) [] false


        // most of the times the candidates do not change so we write back only when needed (i.e. when 'changed' is true)
        if changed && parameters.fc_remove_on_fail then fc_candidates.[v] <- Some candidates

        covered

    /// This procedure attempts to find a cover for v.
    member private self.close v =
        self.db ()
        self.check_not_removed v
        assert (self.dfs_visited v)

        if self.is_covered v then
            true
        else
            self.try_force_cover v

    /// Try to find coverings on all of the nodes above v
    member private self.close_all_ancestors v =
        self.check_not_removed v
        let mutable l = self.ancestors v |> List.rev
        let mutable d = false
        while l <> [] && not d do
            d <- self.close (List.head l)
            l <- List.tail l
        done

    /// If an error path was spurious, refine abstraction and return None.
    /// Otherwise, return true (almost) error path.
    member private self.refine v =
        self.db ()

        assert (abs_node_to_program_loc.[v] = loc_err)
        self.check_not_removed v

        if parameters.print_debug then
            Log.debug parameters <| sprintf "Refining %d (loc %d)..." v abs_node_to_program_loc.[v]

        if Formula.unsat (self.psi v) then
            // In this case the error location is just not satisfible.
            // No interpolant needed.
            None
        else
            let pi = self.find_path v
            let pi' = Symex.slice_path (Programs.collapse_path pi) []
            let formulae = pi' |> Programs.cmdPathToFormulaPath

            // Try to find interpolants (this may fail if we cannot find an interpolant for a true error)
            match Symex.find_unsat_path_interpolant parameters formulae with
            | None ->
                let translate (k1, cmd, k2) = (abs_node_to_program_loc.[k1], cmd, abs_node_to_program_loc.[k2])
                Some (List.map translate pi)

            | Some interpolants ->
                // Found a strengthening.  Now we apply it by conjoining the pieces along the states
                // in the Tree/Graph. This may make some coverings invalid, so we have to re-evaluate them
                // Note also that if we make some of the states unsatisfiable then this will eventually trigger
                // a GC on the subtree underneath them.
                let interpolants = Formula.truec::interpolants@[Formula.falsec]
                for loc, intp in List.zip (self.path_to_locs formulae) interpolants do
                    self.check_not_removed loc
                    if not (self.entails1_psi loc intp) then
                        if parameters.print_debug then
                            Log.debug parameters <| sprintf " Adding interpolant %s to %i (loc %i)" intp.pp loc abs_node_to_program_loc.[loc]
                        self.conjoin_with_psi loc intp
                        self.rm_from_covering (fun (x, y) -> y=loc && not (self.entails_psi x loc))

                self.conjoin_with_psi v Formula.falsec
                None

    /// <summary>
    /// Depth first search:  in this procedure we start building the tree in a DFS manner until we hit
    /// what we think might be an error.
    /// </summary>
    member private self.dfs start =
        self.db ()
        // Start the ball rolling.  The priority doesn't matter, since we're just going
        // to pop it below.
        stack.Clear()
        stack.Push start 0

        let mutable ret = None
        while not stack.IsEmpty && ret.IsNone do
            let v = stack.Pop()

            // The call to dfs_add gives v its DFS ordering number.
            self.dfs_add v

            if not (self.close v) then
                // v isn't covered as a result of closing it, so we need to
                // refine it if it's an error location or expand it otherwise.
                if abs_node_to_program_loc.[v] = loc_err then
                    match self.refine v with
                    | Some pi ->
                        // This is a real error, and the path pi witnesses it.
                        // Due to incrementality we need to add v back as a leaf, as we may be back here.
                        add_leaf v
                        ret <- Some pi
                    | None ->
                        // In this case we haven't hit an error node (yet).
                        ignore (self.close v)
                        self.close_all_ancestors v
                else
                    let children = self.expand v
                    for child in children do
                        let prio = priority.GetWithDefault abs_node_to_program_loc.[child] 0
                        stack.Push child prio

        ret

    /// pick uncovered leaf that
    ///   a) preferably corresponds to error loc
    ///   b) is earliest in dfs order
    member private self.pick_vertex () =
        let mutable errorNodes = []
        let mutable otherNodes = []
        for v in leaves do
           if self.not_covered v then
                if abs_node_to_program_loc.[v] = loc_err then
                    errorNodes <- v :: errorNodes
                else
                    otherNodes <- v :: otherNodes

        if not (List.isEmpty errorNodes) then
            List.minBy (fun v -> dfs_map.[v]) errorNodes
        elif not (List.isEmpty otherNodes) then
            List.minBy (fun v -> dfs_map.[v]) otherNodes
        else
            die()

    member private self.unwind () =
        self.db ()
        let v = self.pick_vertex ()
        Log.debug parameters <| sprintf "Unwinding node %d (loc %d)" v abs_node_to_program_loc.[v]
        self.close_all_ancestors v
        self.dfs v

    member __.GetCetaFilteredARGNodes (locationToCertRepr : System.Collections.Generic.Dictionary<int, Programs.CoopProgramLocation> option) =
        let res = System.Collections.Generic.HashSet()
        let seen = System.Collections.Generic.HashSet()
        let rec dfs nodeId =
            if seen.Add nodeId then
                let isDead = garbage.Contains nodeId || dead.Contains nodeId
                let progLocId = abs_node_to_program_loc.[nodeId]
                let isInstrumentation =
                    if locationToCertRepr.IsSome then
                        match locationToCertRepr.Value.[progLocId] with
                        | Programs.InstrumentationLocation _ -> true
                        | _ -> false
                    else
                        false
                if not isDead && not isInstrumentation then
                    res.Add nodeId |> ignore
                    Seq.iter dfs E.[nodeId]
        dfs init_node
        res

    // Returns a list of formulas that are proven invariants for a program location, to be understood as a disjunction of conjunctions.
    // Note: The result only makes sense for an ARG that has been proven safe.
    member self.GetLocationInvariant (locationToCertRepr : System.Collections.Generic.Dictionary<int, Programs.CoopProgramLocation> option) progLoc : (Formula.formula list) list =
        let nodesToReport = self.GetCetaFilteredARGNodes locationToCertRepr
        program_loc_to_abs_nodes.[progLoc]
        |> Seq.filter nodesToReport.Contains
        |> List.ofSeq
        |> List.map (fun node -> psi.[node] |> List.ofSeq)

    member self.ToCeta
      (writer : System.Xml.XmlWriter)
      (locationToCertRepr : System.Collections.Generic.Dictionary<int, Programs.CoopProgramLocation> option)
      (transWriter : (System.Xml.XmlWriter -> int -> unit) option)
      (filterInstrumentationVars : bool) =
        let getLocationRepr location =
            if locationToCertRepr.IsSome then
                locationToCertRepr.Value.[location]
            else
                Programs.OriginalLocation location

        //Fun story. As allow to filter some nodes, whole parts of the ART may become unreachable.
        //Thus, first compute set of nodes to print overall
        let artNodesToPrint = self.GetCetaFilteredARGNodes locationToCertRepr

        let writeTransId transId =
            match transWriter with
            | Some f -> f writer transId
            | None -> writer.WriteElementString ("transitionId", string transId)

        let exportNode nodeId =
            writer.WriteStartElement "node"
            writer.WriteElementString ("nodeId", string nodeId)
            //We are not using Formula.conj here because we absolutely want to control the order of formulas...
            let psiLinearTerms =
                Formula.formula.FormulasToLinearTerms (psi.[nodeId] :> _)
                |> Formula.maybe_filter_instr_vars filterInstrumentationVars
            writer.WriteStartElement "invariant"
            Formula.linear_terms_to_ceta writer Var.plainToCeta psiLinearTerms filterInstrumentationVars
            writer.WriteEndElement () //end element
            let progLocRepr = getLocationRepr abs_node_to_program_loc.[nodeId]
            //printfn "ARG node to export: %i (%A)" nodeId progLocRepr
            writer.WriteStartElement "location"
            Programs.exportLocation writer progLocRepr
            writer.WriteEndElement () //end location
            match covering.TryGetValue nodeId with
            | (true, coverTarget) ->
                writer.WriteStartElement "coverEdge"
                writer.WriteElementString ("nodeId", string coverTarget)

                writer.WriteStartElement "hints"
                for lt in Formula.formula.FormulasToLinearTerms (psi.[coverTarget] :> _) |> Formula.maybe_filter_instr_vars filterInstrumentationVars do
                    SparseLinear.writeCeTALinearImplicationHints writer psiLinearTerms lt
                writer.WriteEndElement () //hints end

                writer.WriteEndElement () //coverEdge end
            | (false, _) ->
                writer.WriteStartElement "children"
                for childId in E.[nodeId] |> Seq.filter artNodesToPrint.Contains do
                    let (transId, cmds) = abs_edge_to_program_commands.[(nodeId, childId)]
                    //printfn "  ARG child: %i (%A) for trans %i" childId childNodeRepr transId
                    let (transFormula, varToMaxSSAIdx) = Programs.cmdsToCetaFormula program.Variables cmds
                    let varToPre var = Var.prime_var var 0
                    let varToPost var =
                        match Map.tryFind var varToMaxSSAIdx with
                        | Some idx -> Var.prime_var var idx
                        | None -> var
                    let transLinearTerms =
                        Formula.formula.FormulasToLinearTerms (transFormula :> _)
                        |> Formula.maybe_filter_instr_vars filterInstrumentationVars
                    let nodePsiAndTransLinearTerms = Seq.append (Seq.map (SparseLinear.alpha varToPre) psiLinearTerms) transLinearTerms
                    let childPsiLinearTerms =
                        Formula.formula.FormulasToLinearTerms (psi.[childId] :> _)
                        |> Formula.maybe_filter_instr_vars filterInstrumentationVars
                    writer.WriteStartElement "child"
                    writeTransId transId
                    writer.WriteElementString ("nodeId", string childId)
                    writer.WriteStartElement "hints"
                    for lt in childPsiLinearTerms do
                        SparseLinear.writeCeTALinearImplicationHints writer nodePsiAndTransLinearTerms (SparseLinear.alpha varToPost lt)
                    writer.WriteEndElement () //hints end

                    writer.WriteEndElement () //child end
                writer.WriteEndElement () //children end
            writer.WriteEndElement () //node end
        writer.WriteStartElement "impact"
        writer.WriteElementString ("initial", string init_node)
        writer.WriteStartElement "nodes"
        V |> Seq.filter artNodesToPrint.Contains |> Seq.iter exportNode
        writer.WriteEndElement () //nodes end

        let errNodes = V |> Seq.filter (fun v -> abs_node_to_program_loc.[v] = loc_err && artNodesToPrint.Contains v)
        if not <| Seq.isEmpty errNodes then
            writer.WriteStartElement "errorHints"
            let falseLinTerm = List.head (Formula.falsec.ToLinearTerms())
            for errNode in errNodes do
                writer.WriteStartElement "errorHint"
                writer.WriteElementString ("nodeId", string errNode)
                writer.WriteStartElement "hints"
                let errNodeLinTerms = Formula.formula.FormulasToLinearTerms (psi.[errNode] :> _) |> Formula.maybe_filter_instr_vars filterInstrumentationVars
                SparseLinear.writeCeTALinearImplicationHints writer errNodeLinTerms falseLinTerm
                writer.WriteEndElement () //hints end
                writer.WriteEndElement ()
            writer.WriteEndElement () //errorHints end
        writer.WriteEndElement () //impact end

    //
    // Sanity checks
    //

    member private self.sanity_check =
        if Seq.exists (function KeyValue(x, y) -> self.entails_psi x y |> not) covering then
            printf "BIG PROBLEM!\n"

        if Seq.exists (function KeyValue(_, y) -> self.ancestors y |> List.forall (fun a -> not (covering.ContainsKey a)) |> not) covering then
            printf "BIG PROBLEM 2x!\n"

    /// Returns true iff all node invariants are either true or false.
    member __.IsTrivial () =
        psi.Values
        |> Seq.forall
            (fun invs -> invs |> Set.forall (fun inv -> inv = Formula.formula.True || inv = Formula.formula.False))

    interface SafetyInterface.SafetyProver with
        /// Return path to loc_err or None if it's unreachable
        member self.ErrorLocationReachable () =
            program.CacheTransitionsFrom() |> ignore
            self.db ()

            let mutable path = None
            Stats.startTimer "Impact"
            try
                while Seq.exists self.not_covered leaves && path.IsNone do
                    match self.unwind () with
                    | Some pi ->
                            let (_, _, l2) = List.last pi
                            assert (l2 = loc_err)
                            path <- Some pi
                    | None -> ()

                    self.gc()
                done
            finally
                Stats.endTimer "Impact"

            // Check that we we've constructed a consistent proof graph
            if parameters.sanity_checking then
                self.sanity_check

            self.db ()
            path

        /// For incrementality, we sometimes need to delete a subtree within the proof graph
        member self.ResetFrom locationToReset =
            if parameters.iterative_reachability then
                let nodes_to_remove = Seq.filter (fun x -> abs_node_to_program_loc.[x] = locationToReset) V |> List.ofSeq
                for t in nodes_to_remove do
                    if V.Contains t then
                        self.delete_tree t
                        add_leaf t
            else
                //Get rid of _everything_
                V.Clear()
                E.Clear()
                parent.Clear()
                psi.Clear()
                abs_node_to_program_loc.Clear()
                program_loc_to_abs_nodes.Clear()
                fc_candidates.Clear()
                leaves.Clear()
                abs_edge_to_program_commands.Clear()
                cnt <- 0
                covering.Clear()
                stack.Clear()

                //Start anew:
                let newNode = new_vertex ()
                add_V newNode
                add_leaf newNode
                abs_node_to_program_loc.[newNode] <- loc_init
                program_loc_to_abs_nodes.Add (loc_init, newNode)


        ///Delete everything from the graph that used/used some program transition:
        member self.DeleteProgramTransition ((id, (k, cmds, k')) : (int * (int * Programs.Command list * int))) =
            //For each transition to remove, get the representatives of the source, fish out those out-edges that correspond to the trans, remove those children:
            if not(program_loc_to_abs_nodes.ContainsKey k) || not(program_loc_to_abs_nodes.ContainsKey k') then
                ()
            else
            let k_reps = program_loc_to_abs_nodes.[k]
            let k'_reps = program_loc_to_abs_nodes.[k']
            for k_rep in k_reps do
                if (parent.[k_rep] <> -1) then //Avoid accessing things we removed
                    for k_rep_succ in E.[k_rep] do
                        if (parent.[k_rep_succ] <> -1) then //Avoid accessing things we removed
                            if k'_reps.Contains k_rep_succ then
                                //Check that we have the right commands here:
                                if (fst abs_edge_to_program_commands.[k_rep, k_rep_succ] = id) then
                                    //Delete everything that was created using this transition:
                                    self.delete_tree k_rep_succ