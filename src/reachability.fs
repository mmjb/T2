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


module Microsoft.Research.T2.Reachability

open Utils
open Log
open Programs
open Stats
open PrioStack

type Reachability =
    abstract Initialize : Programs.Program -> int -> Reachability
    abstract GetCounterExample : unit -> Counterexample.cex option

type ImpactARG(parameters : Parameters.parameters,
               loc_init : int, 
               loc_err : int, 
               transition : Programs.TransitionFunction, 
               priority : Map<int,int>) =
    /// Should we perform garbage collection on the abstraction graph?
    let do_gc = ref true

    /// Should we perform some sanity checks to make sure that we're not using
    /// nodes that have been GC'd?
    let gc_check = ref false

    /// Tree/Graph constructon representing the state of the safety proof procedure.  Back edges
    /// in the "covering" relations represent induction checks.  At the end of a successful proof
    /// search this graph should represent a valid proof of safety which could be spit out to a
    /// theorem prover.  Note that for performance there is A LOT of redundency in this graph. Its
    /// RIDDLED with invariants. Fun.
    (* ------- State of the abstract reachability graph ------- *)
    /// Counter tracking how many nodes we have in the system
    let cnt = ref 0 

    /// Current nodes in the system
    let V = ref Set.empty

    /// Edge relation
    let E = new SetDictionary<int,int>()

    /// parents in the graph
    let parent = new DefaultDictionary<int,int>(fun _ -> -1)

    /// Set of interpolants (understood as conjunction) for each node
    let psi = new DefaultDictionary<int,Set<Formula.formula>>(fun _ -> Set.empty)

    /// Current leaves in the execution tree
    let leaves = ref Set.empty

    /// Mapping from edges in the execution tree to the commands in the original program
    let abs_edge_to_program_commands = new System.Collections.Generic.Dictionary<int * int, Programs.command list>()

    /// Mapping from nodes in the execution tree to the original program
    let abs_node_to_program_loc = new DefaultDictionary<int,int>(fun _ -> -1)

    /// A node n\in representatives(k) if n in the graph maps back to k in the original program.
    /// i.e. if n\in representatives(k) then node_map n = k
    let program_loc_to_abs_nodes = new SetDictionary<int,int>()

    /// Induction coverings
    let covering = ref Map.empty

    /// Per-node list of candidates that we should search for when looking for a force cover
    let fc_candidates = new DefaultDictionary<int,int list option>(fun _ -> None)

    /// Node numbers do not quite represent the order that we've "visited" them. dfs_map maps each node number to its dfs number
    let dfs_map = DefaultDictionary<int, int>(fun _ -> -1)
    /// Helper to create dfs numbers
    let dfs_cnt = ref 0

    /// The stack used during DFS.
    let stack = ref empty_priostack

    /// Nodes that have been deemed as garbage but havent been GC'd yet.
    let garbage = ref Set.empty

    /// Nodes that were in the system but have now been dead and GC'd
    let dead = ref Set.empty

    let new_vertex () =
        inc_stat "created new vertex"
        let v = !cnt
        incr cnt
        v
    let add_V w = V := Set.add w !V
    let add_E v w = E.Add (v, w); parent.[w] <- v
    let add_leaf v = leaves := Set.add v !leaves

    do
        let newNode = new_vertex ()
        add_V newNode
        add_leaf newNode
        abs_node_to_program_loc.[newNode] <- loc_init
        program_loc_to_abs_nodes.Add (loc_init, newNode)

    member private __.push_priostack_abs_many vs  =
        let mutable sr = !stack
        for v in List.rev vs do
            let prio = Map.findWithDefault abs_node_to_program_loc.[v] 0 priority
            sr <- push_priostack prio v sr
        stack := sr

    member private __.dfs_add x =
        if not (dfs_map.ContainsKey x) then
            dfs_map.[x] <- !dfs_cnt
            incr dfs_cnt
    member private __.dfs_visited x = dfs_map.ContainsKey(x)

    member private __.psi v = psi.[v] |> Set.toList |> Formula.conj
    member private __.get_same_pc v = program_loc_to_abs_nodes.[abs_node_to_program_loc.[v]]
    member private __.parent v = if v = 0 then None else Some parent.[v]
    member private __.leaf v = Set.contains v !leaves
    member private __.remove_leaf v = leaves := Set.remove v !leaves
    member private __.rm_from_covering f =
        let the_filter x y =
            if not (f (x, y)) then true
            else inc_stat "uncovered vertex"; false
        covering := Map.filter the_filter !covering

    member private __.add_covering a b =
        covering := Map.add a b !covering
    member private __.rm_from_leaves f =
        leaves := Set.filter (f >> not) !leaves

    member private self.descendents t = [
        for c in E.[t] do
            yield c
            yield! self.descendents c
        ]

    /// Sanity check to be used before using a node
    member private __.check_not_removed x =
        if !gc_check then
             if Set.contains x !dead then
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

            Log.log parameters <| sprintf "Reachability graph dumped to file %s" filename

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
                let vertex_list = Set.map (fun v -> sprintf "%d [label=\"%d (node %d): %s\"]\n" v (abs_node_to_program_loc.[v]) v (pp_psi_nl v)) !V
                let vertices = Set.fold (fun x s -> x + s) "" vertex_list
                let edges = E.Fold (fun res sourceLoc targetLocs -> Set.fold (fun res targetLoc -> sprintf "%s%d -> %d\n" res sourceLoc targetLoc) res targetLocs) ""
                let covering = Map.fold (fun s x y -> (sprintf "%d -> %d [style=dotted, constraint=false]\n" x y) + s) "" !covering
                sprintf "\ndigraph program {\n%s\n%s\n\n%s}" vertices edges covering
            dot_abs_state |> write_to_fresh_file
            ()

    /// Procedure for removing from the graph. I'm being pretty aggressive right now
    /// because in early days I was seeing lots of performance bugs due to reasoning about dead
    /// nodes.
    member private self.delete_tree t =
        let desc = self.descendents t |> Set.ofList
        dead := Set.union !dead desc

        self.rm_from_covering (fun (x, y) -> desc.Contains x || desc.Contains y)
        let edges_to_remove = abs_edge_to_program_commands.Keys |> Seq.filter (fun (x, y) -> (desc.Contains x) || (desc.Contains y)) |> List.ofSeq
        for edge_to_remove in edges_to_remove do
            abs_edge_to_program_commands.Remove edge_to_remove |> ignore
        V := Set.difference (!V) desc
        leaves := Set.difference (!leaves) desc

        for n in desc do
            parent.[n] <- -1
            psi.[n] <- Set.empty
            program_loc_to_abs_nodes.RemoveKeyVal abs_node_to_program_loc.[n] n
            abs_node_to_program_loc.[n] <- -1
            fc_candidates.[n] <- None

        // We're cleaning out fc_candidates in the get_force_cover_candidates routine
        let keep x = not (Set.contains x desc)
        stack := filter_priostack keep !stack
        leaves := Set.difference !leaves desc

        for d in (desc.Add t) do
            while E.ContainsKey d do
                E.Remove d |> ignore

    ///Delete everything from the graph that used/used some program transition:
    member self.DeleteProgramTransition ((k, cmds, k') : (int * Programs.command list * int)) =
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
                            if (abs_edge_to_program_commands.[k_rep, k_rep_succ] = cmds) then
                                //Delete everything that was created using this transition:
                                self.delete_tree k_rep_succ

    /// Garbage collection procedure.  Roots of trees become garbage when their interpolant becomes "false".
    /// The procedure for strengthening interpolants checks for unsat and puts nodes in !garbage when this
    /// condition is met.
    member private self.gc () =
        if !do_gc then
            for v in !garbage do
                if Set.contains v !V then
                    self.delete_tree v
            garbage := Set.empty

    member private __.garbage_add v =
        if !do_gc then
            garbage := Set.add v !garbage

    member private self.garbage_check v =
        if !do_gc then
            if Formula.unsat (self.psi v) then
                garbage := Set.add v !garbage

    /// Strengthen the invariant at a node.
    member private self.conjoin_with_psi l newPsi =
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
        if Map.containsKey v (!covering) then
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
            | Some(candidates) -> candidates

            // We look at nodes at the same location the original program
            | None ->
                self.get_same_pc v
                // We have to filter out nodes that are in in the DFS stack but haven't actually
                // been visited yet
                |> Set.filter (self.dfs_visited)
                // We can only be covered by nodes less than us in the DFS order
                // (otherwise we could great circular/unsound induction arguments)
                |> Set.filter (fun w -> dfs_map.[w] < dfs_v)
                // We don't want our children, obviously
                |> Set.filter (fun w -> not (self.sq_eq v w))
                // Sort in reverse dfs-search order
                |> Set.toList |> List.sortBy (fun v -> dfs_map.[v]) |> List.rev

        // We're gc-ing here, as it's a little faster.
        let cleaned = List.filter (fun x -> (!dead).Contains x |> not) candidates
        fc_candidates.[v] <- Some(cleaned)
        List.filter (self.not_covered) cleaned

    /// Find the path from node x to node y in the tree, given that x sqeq y
    member private self.find_path_from x y =
        let commands = ref []
        let curNode = ref y
        while !curNode <> x do
            let parentNode = self.parent !curNode
            assert (parentNode.IsSome)
            let parentNode = parentNode.Value
            let curCommands = [for c in abs_edge_to_program_commands.[parentNode, !curNode] -> (parentNode, c, !curNode)]
            commands := curCommands @ !commands
            curNode := parentNode
        !commands

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
    member private __.make_node expandedNode commandsOnEdge newNodeLoc =
        let newNode = new_vertex ()
        add_V newNode
        add_E expandedNode newNode
        abs_node_to_program_loc.[newNode] <- newNodeLoc
        program_loc_to_abs_nodes.Add (newNodeLoc, newNode)
        let commandsOnEdge = if commandsOnEdge = [] then [Programs.skip] else commandsOnEdge
        assert (not <| abs_edge_to_program_commands.ContainsKey (expandedNode, newNode))
        abs_edge_to_program_commands.[(expandedNode, newNode)] <- commandsOnEdge
        add_leaf newNode
        newNode

    /// Expand the graph for DFS search
    member private self.expand v =
        assert (self.leaf v)
        self.db ()
        self.check_not_removed v

        inc_stat "expand vertex"
        if parameters.print_log then
            Log.log parameters <| sprintf "Expanding leaf %d (loc %d)" v abs_node_to_program_loc.[v]

        if not (self.is_covered v) then
            self.remove_leaf v
            [for (T, m) in transition (abs_node_to_program_loc.[v]) do
                let to_add = ref true
                let psi = self.psi v
                if (not <| Formula.unsat psi) && !to_add then
                    yield self.make_node v T m
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
            let common = Set.intersect v_ancestors w_ancestors |> Set.toList
            List.maxBy (fun v -> dfs_map.[v]) common
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
                let assume_not_psi_w = (v, Programs.assume (Formula.Not (psi_w)), -1)
                let augmented_path = assume_psi_x :: path @ [assume_not_psi_w]
                let sliced_path = Symex.slice_path (collapse_path augmented_path) []
                let filtered_path = sliced_path |> List.tail |> List.all_but_last
                Symex.path_to_transitions_and_var_map filtered_path Map.empty
            let initial = psi.[x] |> Set.toList
            let var_map = Symex.add_vars_to_map initial var_map
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
                        let gen_dummy_assign (v,p) = Formula.Eq(var v p, zero)
                        List.map gen_dummy_assign (Map.toList var_map) |> Formula.conj
                    Symex.find_path_interpolant_old parameters false distance ((initial::formulae)@[final; Formula.falsec])

            match find_path_interpolant formulae (Formula.conj initial) final with
            | Some(A) ->
                let update (loc,intp) =
                    if not (self.entails1_psi loc intp) then
                        let split = Formula.split_conjunction  intp
                        List.iter (self.conjoin_with_psi loc) split
                        self.rm_from_covering (fun (x,y) -> y=loc && not (self.entails_psi x loc))
                List.zip (self.path_to_locs formulae) A |> List.iter update

                let covered = self.cover v w
                assert(covered)
                true
            | None ->
                Log.log parameters <| "Failed to find path interpolant!"
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

        if result then inc_stat "force cover succeeded"
        else inc_stat "force cover failed"

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
        let l = self.ancestors v |> List.rev |> ref
        let d = ref false
        while !l<>[] && not !d do
            d := self.close (List.head !l)
            l := List.tail !l
        done

    /// If an error path was spurious, refine abstraction and return None.
    /// Otherwise, return true (almost) error path.
    member private self.refine v =
        self.db () 

        assert (abs_node_to_program_loc.[v] = loc_err)
        self.check_not_removed v

        if parameters.print_log then
            Log.log parameters <| sprintf "Refining %d (loc %d)..." v abs_node_to_program_loc.[v]

        if Formula.unsat (self.psi v) then
            // In this case the error location is just not satisfible.
            // No interpolant needed.
            None
        else
            let pi = self.find_path v
            let pi' = Symex.slice_path (collapse_path pi) []
            let formulae = pi' |> Symex.path_to_formulae

            // Try to find interpolants (this may fail if we cannot find an interpolant for a true error)
            match Symex.find_unsat_path_interpolant parameters formulae with
            | None ->
                let translate (k1, cmd, k2) = (abs_node_to_program_loc.[k1], cmd, abs_node_to_program_loc.[k2])
                Some (List.map translate pi)

            | Some(interpolants) ->
                // Found a strengthening.  Now we apply it by conjoining the pieces along the states
                // in the Tree/Graph. This may make some coverings invalid, so we have to re-evaluate them
                // Note also that if we make some of the states unsatisfiable then this will eventually trigger
                // a GC on the subtree underneath them.
                let interpolants = Formula.truec::interpolants@[Formula.falsec]
                for loc, intp in List.zip (self.path_to_locs formulae) interpolants do
                    self.check_not_removed loc
                    if not (self.entails1_psi loc intp) then
                        if parameters.print_log then
                            Log.log parameters <| sprintf " Adding interpolant %s to %i (loc %i)" intp.pp loc abs_node_to_program_loc.[loc]
                        self.conjoin_with_psi loc intp
                        self.rm_from_covering (fun (x,y) -> y=loc && not (self.entails_psi x loc))

                self.conjoin_with_psi v (Formula.falsec)
                None

    /// <summary>
    /// Depth first search:  in this procedure we start building the tree in a DFS manner until we hit
    /// what we think might be an error.
    /// </summary>
    member private self.dfs start =
        self.db ()
        // Start the ball rolling.  The priority doesn't matter, since we're just going
        // to pop it below.
        stack := singleton_priostack 0 start

        let ret = ref None
        while not(isempty_priostack !stack) && (!ret).IsNone do
            let (v, s') = pop_priostack !stack
            stack := s'

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
                        ret := Some pi
                    | None ->
                        // In this case we haven't hit an error node (yet).
                        ignore (self.close v)
                        self.close_all_ancestors v
                else
                    let children = self.expand v
                    self.push_priostack_abs_many children

        !ret

    /// pick uncovered leaf that
    ///   a) preferably corresponds to error loc
    ///   b) is earliest in dfs order
    member private self.pick_vertex () =
        let error_nodes, other_nodes =
            !leaves
            |> Seq.filter self.not_covered
            |> Seq.toList
            |> List.partition (fun v -> abs_node_to_program_loc.[v] = loc_err)

        if not error_nodes.IsEmpty then
            List.minBy (fun v -> dfs_map.[v]) error_nodes
        elif not other_nodes.IsEmpty then
            List.minBy (fun v -> dfs_map.[v]) other_nodes
        else
            die()

    member private self.unwind () =
        self.db () 
        let v = self.pick_vertex ()
        Log.log parameters <| sprintf "Unwinding node %d (loc %d)" v abs_node_to_program_loc.[v]
        self.close_all_ancestors v
        self.dfs v

    //
    // Sanity checks
    //

    member private self.sanity_check =
        if Map.exists (fun x y -> self.entails_psi x y |> not) !covering then
            printf "BIG PROBLEM!\n"

        if Map.exists (fun _ y -> self.ancestors y |> List.forall (fun a -> not (Map.containsKey a !covering)) |> not) !covering then
            printf "BIG PROBLEM 2x!\n"

    /// Return path to loc_err or None if it's unreachable
    member self.ErrorLocationReachable () =
        self.db ()
        let path = ref None
        while Set.exists self.not_covered !leaves && (!path).IsNone do
            match self.unwind () with
            | Some pi ->
                    let (_, _, l2) = List.last pi
                    assert (l2 = loc_err)
                    path := Some pi
            | None -> ()

            self.gc()
        done

        // Check that we we've constructed a consistent proof graph
        if parameters.sanity_checking then
            self.sanity_check

        self.db ()
        !path

    /// For incrementality, we sometimes need to delete a subtree within the proof graph
    member self.ResetFrom (_ : Programs.Program) locationToReset =
        let to_reset = 
            if parameters.iterative_reachability then
                locationToReset
            else
                loc_init
        let nodes = Set.filter (fun x -> abs_node_to_program_loc.[x] = to_reset) !V |> ref
        while !nodes<>Set.empty do
            let t = Set.minElement !nodes
            nodes := Set.remove t !nodes
            self.delete_tree t
            add_leaf t

            // The deleted tree might have made nodes disappear
            nodes := Set.intersect !nodes !V
 /// Prove that location err is unreachable in p
let prover (pars : Parameters.parameters) p err =
    Utils.timeout pars.timeout

    // Create new initial location with transition assume(_const_100 > _const_32) for all
    // abstracted const variables.
    Programs.symbconsts_init p

    // The connection between programs and Graph is a little bit messy
    // at the moment. We have to marshal a little bit of data between them
    let transition = Programs.transitions_from p
    let abs = ImpactARG(pars, !p.initial, err, transition, Map.empty)

    if pars.dottify_input_pgms then
        Output.print_dot_program p "input.dot"

    // Try to disprove/prove the error location in abs to be unreachable
    let r = abs.ErrorLocationReachable ()

    // If the flag is set, produce a counterexample file
    if pars.safety_counterexample && r.IsSome then
        let stem = Some (List.map (fun (x,y,z) -> (x,[y],z)) r.Value)
        let cex = Counterexample.make stem None
        Counterexample.print_defect pars [cex] "defect.tt"
        Counterexample.print_program pars [cex] "defect.t2"
        Utils.run_clear()

    Utils.reset_timeout()

    r