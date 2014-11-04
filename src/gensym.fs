////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      gensym.fs
//
//  Abstract:
//
//      Maintains unique names and mappings
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

module Gensym

open Utils

let n = ref 0l
let fresh_num() = let k = !n in n := k+1l; k
let fresh_var() = let k = fresh_num() in "__" + string(k) + "_gensym__"

//
// We memoize gensym-based functions, thus giving us mappings that last the
// lifetime of the program (or until clear is called).  This gives the
// appearance of a unique mapping for any string to a fresh set of
// strings.  Not that composible........
//
let (clear1,premapping) = memoize (fun x -> "'" + x + "_" + fresh_var())
let (clear2,postmapping) = memoize (fun x -> x + "'_" + fresh_var())
let (clear3,pairmapping) = memoize (fun (x,y) -> x + sprintf ",%d" y + "_" + fresh_var())

//
// Figuring that the clear() function isn't needed, as the system
// will just GC the mapping when its done.
//
let make_mapping f = memoize (fun x -> f x + "_" + fresh_var()) |> snd

let clear() =
   clear1()
   clear2()
   clear3()
   n := 0l

Utils.add_clear clear
