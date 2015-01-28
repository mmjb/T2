////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      stats.fs
//
//  Abstract:
//
//      Statistical measurement
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


module Microsoft.Research.T2.Stats

///
/// Set of counters
///
let counters : Map<string, int> ref = ref Map.empty

let start_times : Map<string, System.DateTime> ref = ref Map.empty
let total_times : Map<string, int> ref = ref Map.empty

let start_time s =
    match Map.tryFind s !start_times with
    | Some(_) -> Utils.dieWith "Unexpected start_time use of timer %s" s
    | None -> start_times := Map.add s System.DateTime.Now !start_times

let end_time s =
    match Map.tryFind s !start_times with
    | Some(start_time) ->
        let current_time = System.DateTime.Now
        let elapsed = (current_time - start_time).Milliseconds
        start_times := Map.remove s !start_times
        match Map.tryFind s !total_times with
        | Some(old_elapsed) ->
            total_times := Map.add s (old_elapsed+elapsed) !total_times
        | None ->
            total_times := Map.add s (elapsed) !total_times
    | None -> Utils.dieWith "Unexpected end_time use of timer %s" s

///
/// add_stat s x updates stats counter s with x
///
let add_stat s x =
    match Map.tryFind s !counters with
    | Some(i) ->
        counters := Map.add s (i+x) !counters
    | None ->
        counters := Map.add s x !counters

///
/// Increment a stats counter by 1
///
let inc_stat s = add_stat s 1

///
/// Print out the current stats state
///
let print_stats () =
    printfn "Statistics:"
    Map.iter (fun k v -> printfn "  %s: %d" k v) !counters

let print_times () =
    Map.iter (fun k v -> printfn "%s time: %.3fs" k (float(v)/1000.)) !total_times
