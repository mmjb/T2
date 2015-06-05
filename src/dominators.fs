////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      Dom
//
//  Abstract:
//
//      Compute dominators using Lengaur/Tarjan algorithm
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

module Microsoft.Research.T2.Dominators

open Utils

type dominatorTree = DefaultDictionary<int,int>

/// Compute dominator tree, following the sophisticated method from Lengauer & Tarjan '79:
let find_dominators (succ : ListDictionary<int, 'a * ('b * 'c * int)>) entry =
  // Step 1: Initialize data structures, assign DFS numbers:
  let dfsNumber = ref -1
  let pred = new SetDictionary<int, int>()
  let semi = new DefaultDictionary<int, int>(fun _ -> -1)
  let vertex = new DefaultDictionary<int, int>(fun _ -> -1)
  let parent = new DefaultDictionary<int, int>(fun _ -> -1)
  let rec dfs v =
    incr dfsNumber
    semi.[v] <- !dfsNumber
    vertex.[!dfsNumber] <- v
    for (_, (_, _, w)) in succ.[v] do
        if semi.[w] = -1 then
            parent.[w] <- v
            dfs w
        pred.Add (w, v)
  dfs entry

  // Steps 2, 3, together:
  let ancestor = new DefaultDictionary<int, int>(fun _ -> -1)
  let label = new DefaultDictionary<int, int>(fun k -> k)
  let size = DefaultDictionary<int,int>(fun _ -> 1)
  let child = DefaultDictionary<int,int>(fun _ -> -1)
  let rec compress v =
    if ancestor.[ancestor.[v]] > -1 then
        compress ancestor.[v]
        if semi.[label.[ancestor.[v]]] < semi.[label.[v]] then
            label.[v] <- label.[ancestor.[v]]
        ancestor.[v] <- ancestor.[ancestor.[v]]
  let eval v =
    if ancestor.[v] = -1 then
        label.[v]
    else
        if semi.[label.[ancestor.[v]]] >= semi.[label.[v]] then
            label.[v]
        else
            label.[ancestor.[v]]
  size.[-1] <- 0
  label.[-1] <- -1
  semi.[-1] <- -1
  let link v w =
    let mutable s = w
    while semi.[label.[w]] < semi.[label.[child.[s]]] do
        if size.[s] + size.[child.[child.[s]]] >= 2 * size.[child.[s]] then
            parent.[child.[s]] <- s
            child.[s] <- child.[child.[s]]
        else
            size.[child.[s]] <- size.[s]
            let t = parent.[s]
            parent.[s] <- child.[s]
            s <- t
        label.[s] <- label.[w]
        size.[v] <- size.[v] + size.[w]
        if size.[v] < 2 * size.[w] then
            let t = s
            s <- child.[v]
            child.[v] <- t
        while s <> -1 do
            parent.[s] <- v
            s <- child.[s]

  let bucket = new SetDictionary<int, int>()
  let dom = new DefaultDictionary<int,int>(fun _ -> -1)
  for i = !dfsNumber downto 1 do
    let w = vertex.[i]
    //Step2:
    for v in pred.[w] do
        let u = eval v
        if semi.[u] < semi.[w] then
            semi.[w] <- semi.[u]
    bucket.Add (vertex.[semi.[w]], w)
    link parent.[w] w
    //Step3 (we do not delete from bucket inbetween, but just drop it all after the loop):
    for v in bucket.[parent.[w]] do
        let u = eval v
        dom.[v] <- if semi.[u] < semi.[v] then u else parent.[w]
    bucket.[parent.[w]] <- Set.empty

    // Step 4:
    for i = 1 to !dfsNumber do
        let w = vertex.[i]
        if dom.[w] <> vertex.[semi.[w]] then
            dom.[w] <- dom.[dom.[w]]
    dom.[entry] <- -1

  dom

/// Return true if a dominates b and false otherwise
let rec dominates (dom : dominatorTree) a b =
  if b = -1 then
    false
  else if a = b then
    true
  else
    dominates dom a dom.[b]

let rec dominator_path (dom : dominatorTree) x =
   if x = -1 then []
   else x :: dominator_path dom (dom.[x])

let headers dt xs = Set.map (dominator_path dt >> Set.ofList) xs
                  |> Set.intersectMany

/// Are all elements of the set dominated by one element?
/// Equivalenthly, does set have single entry point?
let well_formed dt xs = (Set.intersect xs (headers dt xs)).IsEmpty |> not
