////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      PrioStack
//
//  Abstract:
//
//      Priority Stack
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


module PrioStack

open Utils

///
/// List of lists of pairs (priority, value).
/// Priorities in each list are the same.
/// Lists with greater priority come first.
///
type PrioStack = (int * int) list list

let empty_priostack = ([]:PrioStack)

let singleton_priostack pr v = [[(pr, v)]]  : PrioStack

let rec push_priostack pr v (s:PrioStack) =
    match s with
    | []::l -> push_priostack pr v l
    | ((n,_)::_)::_ when pr>n -> [(pr,v)]::s
    | ((n,e)::l)::l' when pr=n -> ((pr,v)::(n,e)::l)::l'
    | l::l' -> l::push_priostack pr v l'
    | [] -> ([[(pr,v)]]:PrioStack)

let rec pop_priostack (s:PrioStack) : (int*PrioStack)=
    match s with | []::l' -> pop_priostack l'
                 | ((_,e)::l)::l' -> (e,l::l')
                 | [] -> dieWith "Empty stack"

let rec filter_priostack f (s:PrioStack) =
    [
    for line in s do
        let x = [
            for pr, e in line do
                if f e then
                    yield pr, e
            ]
        if x <> [] then
            yield x
    ]

let rec isempty_priostack (s:PrioStack) =
    match s with | [] -> true
                 | []::l -> isempty_priostack l
                 | (_::_)::_ -> false
