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

module Microsoft.Research.T2.SCC

open Utils

let find_sccs (graph : ListDictionary<int, 'a * ('b * 'c * int)>) entry =
    let lowlink = System.Collections.Generic.Dictionary()
    let number = System.Collections.Generic.Dictionary()

    let stack = System.Collections.Generic.Stack()
    let stackContents = System.Collections.Generic.HashSet()

    let sccs = ref []
    let i = ref 1
    let rec strongconnect v =
        number.[v] <- !i
        lowlink.[v] <- !i
        i := !i + 1
        stack.Push v
        stackContents.Add v |> ignore

        for (_, (_, _, w)) in graph.[v] do
            if not(number.ContainsKey w) then
                strongconnect w
                lowlink.[v] <- min lowlink.[v] lowlink.[w]
            else if number.[w] < number.[v] then
                if stackContents.Contains w then
                    lowlink.[v] <- min lowlink.[v] number.[w]
        if lowlink.[v] = number.[v] then
            let mutable newComponent = Set.empty
            let numberV = number.[v]
            while stack.Count > 0 && number.[stack.Peek()] >= numberV do
                let w = stack.Pop ()
                stackContents.Remove w |> ignore
                newComponent <- Set.add w newComponent

            //Add to result, but remove trivial SCCs without self-cycles:
            if newComponent.Count > 1 || (Seq.exists (fun (_, (_, _, w)) -> v = w) graph.[v]) then
                sccs := newComponent :: !sccs

    strongconnect entry
    !sccs