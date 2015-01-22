////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      parseError.fs
//
//  Abstract:
//
//       * Helper functions used in the parser
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

module ParseError

exception Error

type info =
    { linenum:  int      ;
      linepos:  int list ;
      fileName: string   ;
      errors:   bool     }

let current : info ref =
  ref
    { linenum  = 1 ;
      linepos  = [1] ;
      fileName = "" ;
      errors   = false }

let fileName i = i.fileName

let startFile fname =
  current := { linenum  = 1 ;
               linepos  = [0] ;
               fileName = fname ;
               errors   = false ; }

let getLine () = (!current).linenum
let getFilename () = (!current).fileName

let restartFile fname l =
  current :=
      { linenum  = l ;
        linepos  = [1] ;
        fileName = fname ;
        errors   = false }

let noteNewline n =
  current :=
    { !current with linenum = (!current).linenum + 1 ;
                    linepos = n :: (!current).linepos }
 
let getLineCol (i : info) pos =
  let rec look n = function
      a::_ when (a<=pos) -> (n, pos - a)
    | _::rest -> look (n - 1) rest
    | _ -> (0, 0)
  in
  let (lin,col) = look i.linenum i.linepos in
  sprintf "%s: %d.%d" i.fileName lin col


let theLexbuf = ref (Microsoft.FSharp.Text.Lexing.LexBuffer<byte>.FromBytes [||])