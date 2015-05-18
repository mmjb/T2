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

open Utils
open System.Collections.Generic

// Set of counters / timers. Should be transitioned into a context object, to become thread safe.
let counters : Dictionary<string, int> = Dictionary()
let startTimes : Dictionary<string, System.DateTime> = Dictionary()
let totalTimes : Dictionary<string, float> = Dictionary()

/// Record start time of some timer.
let startTimer s =
    (*
    match startTimes.TryGetValue s with
    | (true, _) ->
        Utils.dieWith "Tried to restart running timer '%s'." s
    | _ -> *)
        startTimes.[s] <- System.DateTime.Now

/// Note end time of some timer.
let endTimer s =
    match startTimes.TryGetValue s with
    | (true, startTime) ->
        startTimes.Remove s |> ignore
        let currentTime = System.DateTime.Now
        let elapsed = (currentTime - startTime).TotalSeconds
        match totalTimes.TryGetValue s with
        | (true, oldTime) ->
            totalTimes.[s] <- oldTime + elapsed
        | _ ->
            totalTimes.[s] <- elapsed
    | _ -> Utils.dieWith "Tried to stop inactive '%s'." s

/// Add x to the counter s
let addToCounter s x =
    match counters.TryGetValue s with
    | (true, oldCounter) ->
        counters.[s] <- oldCounter + x
    | _ ->
        counters.[s] <- x

/// Increment counter s
let incCounter s = addToCounter s 1

/// Print out statistics
let printStatistics () =
    printfn "Statistics:"
    Seq.iter (function KeyValue(k, v) -> printfn "  Timer '%s': %.3fs" k v) totalTimes
    Seq.iter (function KeyValue(k, v) -> printfn "  %s: %d" k v) counters