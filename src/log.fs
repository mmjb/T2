///////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      log.fs
//
//  Abstract:
//
//      Central mechanism for controlling spew
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

module Log

///
/// Time when T2 execution began
///
let start_time = ref System.DateTime.Now

///
/// Return true if logging is turned on
///

let do_logging () = !Arguments.print_log
let do_debugging () = !Arguments.print_debug

///
/// "log s" records message s to the log
///
let previous_time = ref System.DateTime.Now

let log s = if do_logging() then
                //printf "%A: %s\n" System.DateTime.Now s
                let now = System.DateTime.Now
                let diff = now.Subtract(!previous_time)
                //previous_time := now
                printf "%d:%d:%d %s\n" diff.Minutes diff.Seconds diff.Milliseconds s

//                printf "%s\n" s
                System.Console.Out.Flush ()

let debug s = if do_debugging() then log ("DEBUG: " ^ s) else ()
