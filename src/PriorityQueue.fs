////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      PriorityQueue
//
//  Abstract:
//
//      Priority queue implementation based on a binary heap
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

module PriorityQueue

/// A priority queue backed by an array-based binary heap. Larger priorities come first.
type PriorityQueue<'T> () =
    /// The backing array actually containing all of our beautiful data
    let mutable data = Array.zeroCreate<int * 'T> 8
    /// The next index to be used for insertion.
    //To simplify the remaining implementation, we start with 1, and data[0] will always stay empty.
    let mutable nextIndex = 1

    member private __.Swap i j =
        let temp = data.[i]
        data.[i] <- data.[j]
        data.[j] <- temp

    member private __.DoubleCapacity() =
        let oldData = data
        data <- Array.zeroCreate<int * 'T> (oldData.Length * 2)
        System.Array.Copy (oldData, data, oldData.Length)

    ///Restore heap property, which might be violated by data.[index] being larger than its "parent"
    member private self.Heapify index =
        //We are done for index <= 1, so only consider the others:
        if index > 1 then
            if fst data.[index / 2] < fst data.[index] then
                self.Swap (index / 2) index
                self.Heapify (index / 2)

    ///Restore heap property, which might be violated by data.[index] being smaller that its "children"
    member private self.Trickle index =
        let mutable swapIndex = index
        if 2 * index < nextIndex && fst data.[index] < fst data.[2 * index] then
            swapIndex <- 2 * index
        if 2 * index + 1 < nextIndex && fst data.[swapIndex] < fst data.[2 * index + 1] then
            swapIndex <- 2 * index + 1
        if index <> swapIndex then
            self.Swap index swapIndex
            self.Trickle swapIndex

    member self.Peek () : 'T = 
        if self.IsEmpty then
            invalidOp "Can't peek into empty queue."
        snd data.[1]

    member self.Pop () : 'T=
        if self.IsEmpty then
            invalidOp "Can't pop from empty queue."
        let resultValue = snd data.[1]
        data.[1] <- data.[nextIndex - 1]
        data.[nextIndex - 1] <- Unchecked.defaultof<int * 'T> //Think of the garbage collector, so destroy link.
        nextIndex <- nextIndex - 1
        self.Trickle 1
        resultValue

    member self.Push (value : 'T) (priority : int) =
        //Enlarge backing data structure if needed
        if nextIndex = data.Length then
            self.DoubleCapacity()
        data.[nextIndex] <- (priority, value)
        self.Heapify nextIndex
        nextIndex <- nextIndex + 1

    member __.Clear () =
        data <- Array.zeroCreate<int * 'T> (data.Length)
        nextIndex <- 1

    /// Remove all elements of the priority queue for which pred holds
    member self.RemoveWhere (pred : 'T -> bool) =
        //This is almost like the usual pop, in that we just insert the last element and then restore the heap property.
        //However, that can mean Heapify() (i.e., bubbling up in the heap) or TrickleDown()
        //The invariant is that data.[1..curIdx-1] has already been filtered.
        let mutable curIdx = 1
        while curIdx < nextIndex do
            //Termination argument: Every iteration decreases (nextIndex - curIdx):
            //  We remove nothing, and curIdx is incremented, or we remove something and decrement nextIndex
            let curElement = data.[curIdx]
            if pred (snd curElement) then
                //Remove stuff from the end until we find an element we want to keep:
                let mutable replacementElement = None
                while nextIndex - 1 > curIdx && replacementElement.IsNone do
                    let lastElement = data.[nextIndex - 1]
                    data.[nextIndex] <- Unchecked.defaultof<int * 'T>
                    nextIndex <- nextIndex - 1
                    if not(pred (snd lastElement)) then
                        replacementElement <- Some lastElement

                match replacementElement with
                | Some replacementElement ->
                    //There is a replacement! Insert it, and decide if we need to tricke or heapify.
                    //We've definitely made progress, as nextIndex was decremented at least once.
                    data.[curIdx] <- replacementElement
                    if curIdx > 1 && fst data.[curIdx / 2] < fst replacementElement then
                        self.Heapify curIdx
                        curIdx <- curIdx + 1 //In this case, we swap an already filtered element into curIdx, and we don't need to look at it again
                    else
                        self.Trickle curIdx 
                        //In this case, we swap an unfiltered element into curIdx, and we need to examine it. 
                | None ->
                    //No replacement: This is the new end. Remove that element, and bump the next pointer
                    data.[curIdx] <- Unchecked.defaultof<int * 'T>
                    nextIndex <- nextIndex - 1
            else
                curIdx <- curIdx + 1
        ()


    member __.Count with get () = nextIndex - 1
    member __.IsEmpty with get () = nextIndex <= 1
    
    static member inline peek (queue : PriorityQueue<'T>) : 'T = queue.Peek()
    static member inline pop (queue : PriorityQueue<'T>) : 'T = queue.Pop()
    static member inline push (value : 'T) (priority : int) (queue : PriorityQueue<'T>) : unit = queue.Push value priority
    static member inline count (queue : PriorityQueue<'T>) : int = queue.Count
    static member inline isEmpty (queue : PriorityQueue<'T>) : bool = queue.IsEmpty