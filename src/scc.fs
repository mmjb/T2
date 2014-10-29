////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      Scc
//
//  Abstract:
//
//      Strongly connected components
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

module SCC

open Utils

//
// compute the strongly-connected components of a directed, rooted graph
// Lemma. If G(i) = (V(i), E(i) ) is a strongly connected component of a
// directed graph G and S = (V,T) is a depth-first spanning forest for G,
// then the vertices of G(i), with the edges common to T and E(i) form a
// tree.
//

// LOWLINK[v] = min (label of v, label of w, where w is in the set such
// that there is a cross edge or back edge from a descendant of v to w
// and the root of the strongly connected component containing w is an
// ancestor of v.

// Lemma. If G is a directed graph, then a vertex v is the root of a
// strongly connected component of G if and only if LOWLINK[v] = v.

let find_sccs_aux (graph : SetDictionary<int,int>) entry (visited : Set<int> ref) count=
  let sccs = ref []
  // dfs_no: dfs_no.(i) is the DFS number of vertex i in DFS spanning tree
  let dfs_no = ref Map.empty
  let low = ref Map.empty
  let stack = ref [] in
  let on_stack = ref Set.empty
  // compute DFS tree
  let rec dfs v =
    visited := Set.add v !visited
    dfs_no := Map.add v !count !dfs_no
    low := Map.add v !count !low
    incr count;
    on_stack := Set.add v !on_stack
    stack := v::!stack;
    let visit_node w =
        if not (Set.contains w !visited) then
            // tree edge
            dfs w;
            if (Map.findWithDefault w 0 !low) < (Map.findWithDefault v 0 !low) then 
                low := Map.add v (Map.findWithDefault w 0 !low) !low
        else if (Map.findWithDefault w 0 !dfs_no) < (Map.findWithDefault v 0 !dfs_no) && (Set.contains w !on_stack) then
            // ignore forward edges and only consider vertices
            // that have been processed but not been put in a SCC yet
            if (Map.findWithDefault w 0 !dfs_no) < (Map.findWithDefault v 0 !low) then 
                low := Map.add v (Map.findWithDefault w 0 !dfs_no) !low
    Set.iter visit_node graph.[v];

    if (Map.findWithDefault v 0 !low) = (Map.findWithDefault v 0 !dfs_no) then
        let scc = ref []
        // stack cannot be empty
        while (List.head !stack) <> v do
            let top = List.head !stack in
            scc := top::!scc;
            stack := (List.tail !stack);
            on_stack := Set.remove top !on_stack
        // make sure to get v
        scc := v::!scc;
        stack := (List.tail !stack);
        on_stack := Set.remove v !on_stack
        sccs := !scc::!sccs
  in
  dfs entry;
  !sccs

let find_sccs (graph : SetDictionary<int,int>) entry =
    let count = ref 0
    let visited = ref Set.empty
    find_sccs_aux graph entry visited count