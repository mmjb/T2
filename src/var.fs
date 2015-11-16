////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      var.fs
//
//  Abstract:
//
//      Variables API
//
//  Environment:
//
//
//  Notes:
//
//      * TODO: Currently this is very simple.  Eventually I'd like to move to a int-based representaton with
//        a mapping for pretty printing, but this has not been implemented yet.
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

module Microsoft.Research.T2.Var

open Utils

type var = string
let idx2str = id
let var = id
let var2str x = sprintf "\" %s \"" (idx2str x)
let pp = idx2str

let private splitPrimedVar (v : var) =
    let i = v.LastIndexOf "^"
    if i < 0 then
        dieWith ("Unpriming non-primed var " + v)
    else
        (v.[0 .. i-1], v.[i + 1 ..])

/// Assuming that SSA information is after ^
let unprime_var (v : string) = fst (splitPrimedVar v)

/// Assuming that SSA information is after ^
let get_prime_idx (v : string) = int (snd (splitPrimedVar v))

///
/// Encoding SSA using numbers after "^"
///
let prime_var v (primes:int) = v + "^" + primes.ToString()

