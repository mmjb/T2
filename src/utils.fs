////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      utils.fs
//
//  Abstract:
//
//      Various basic functions
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

module Microsoft.Research.T2.Utils

type KeyValueAsPairEnumerator<'Key, 'Value> (backingEnumerator : System.Collections.Generic.IEnumerator<System.Collections.Generic.KeyValuePair<'Key, 'Value>>) =
    interface System.Collections.Generic.IEnumerator<'Key * 'Value> with
        member __.Current with get () = (backingEnumerator.Current.Key, backingEnumerator.Current.Value)
    interface System.Collections.IEnumerator with
        member __.MoveNext () = backingEnumerator.MoveNext ()
        member __.Current with get() = backingEnumerator.Current |> box
        member __.Reset () = backingEnumerator. Reset ()
    interface System.IDisposable with
        member __.Dispose () = backingEnumerator.Dispose ()

type ListDictionary<'Key, 'Value when 'Key : equality>() =
    let backingDict = new System.Collections.Generic.Dictionary<'Key, 'Value list>()

    ///// Accessing entries:
    member __.Item
        with get key       =
            let mutable res = []
            if backingDict.TryGetValue (key, &res) then
                res
            else
                []
        and  set key value = backingDict.[key] <- value

    ///// Adding, removing and replacing single entries or full entry seqs:
    member __.Add (key, value) =
        let mutable res = []
        if backingDict.TryGetValue (key, &res) then
            backingDict.[key] <- value :: res
        else
            backingDict.[key] <- [value]
    member self.AddMany keyValuePairs =
        Seq.iter self.Add keyValuePairs
    member self.Union (otherDict : ListDictionary<'Key, 'Value>) =
        self.AddMany otherDict.Bindings
    member __.Remove key =
        backingDict.Remove key
    member __.Replace key value =
        backingDict.[key] <- [value]
    member __.ReplaceList key valueList =
        backingDict.[key] <- valueList
    member __.Clear () =
        backingDict.Clear()

    member __.ContainsKey key =
       backingDict.ContainsKey key

    ///// Functional basics:
    member __.Map (f : 'Value list -> 'Value list) =
        for key in backingDict.Keys do
            backingDict.[key] <- f backingDict.[key]
    member __.Iter (action : 'Key -> 'Value list -> Unit) =
        backingDict |> Seq.iter (fun t -> action t.Key t.Value)
    member __.Fold (folder : 'T -> 'Key -> 'Value list -> 'T) initialState =
        backingDict |> Seq.fold (fun state t -> folder state t.Key t.Value) initialState

    ///// Helpers to iterate over contents:
    member __.Keys = backingDict.Keys
    member __.Values = backingDict.Values
    member __.Bindings = seq { for KeyValue(k,vs) in backingDict do for v in vs do yield (k,v) }
    interface System.Collections.Generic.IEnumerable<'Key * ('Value list)> with
        member __.GetEnumerator () = new KeyValueAsPairEnumerator<'Key, 'Value list>(backingDict.GetEnumerator()) :> _
    interface System.Collections.IEnumerable with
        member __.GetEnumerator () = new KeyValueAsPairEnumerator<'Key, 'Value list>(backingDict.GetEnumerator()) :> _

type SetDictionary<'Key,'Value when 'Key : equality and 'Value : comparison>() =
    let backingDict = new System.Collections.Generic.Dictionary<'Key, Set<'Value>>()

    ///// Accessing entries:
    member __.Item
        with get key       =
            let mutable res = Set.empty
            if backingDict.TryGetValue (key, &res) then
                res
            else
                Set.empty
        and  set key value = backingDict.[key] <- value

    ///// Adding, removing and replacing single entries or full entry seqs:
    member __.Add (key, value) =
        let mutable res = Set.empty
        if backingDict.TryGetValue (key, &res) then
            backingDict.[key] <- Set.add value res
        else
            backingDict.[key] <- Set.singleton value
    member self.AddMany keyValuePairs =
        Seq.iter self.Add keyValuePairs
    member self.Union (otherDict : SetDictionary<'Key, 'Value>) =
        self.AddMany otherDict.Bindings
    member __.Remove key =
        backingDict.Remove key
    member __.RemoveKeyVal key value =
        backingDict.[key] <- Set.remove value backingDict.[key]
    member __.Replace key value =
        backingDict.[key] <- Set.singleton value
    member __.ReplaceSet key valueSet =
        backingDict.[key] <- valueSet
    member __.Clear () =
        backingDict.Clear()

    member __.ContainsKey key =
       backingDict.ContainsKey key

    ///// Functional basics:
    member __.Map (f : Set<'Value> -> Set<'Value>) =
        for key in backingDict.Keys do
            backingDict.[key] <- f backingDict.[key]
    member __.Iter (action : 'Key -> Set<'Value> -> Unit) =
        backingDict |> Seq.iter (fun t -> action t.Key t.Value)
    member __.Fold (folder : 'T -> 'Key -> Set<'Value> -> 'T) initialState =
        backingDict |> Seq.fold (fun state t -> folder state t.Key t.Value) initialState

    ///// Helpers to iterate over contents:
    member __.Keys = backingDict.Keys
    member __.Values = backingDict.Values
    member __.Bindings = seq { for KeyValue(k,vs) in backingDict do for v in vs do yield (k,v) }
    interface System.Collections.Generic.IEnumerable<'Key * Set<'Value>> with
        member __.GetEnumerator () = new KeyValueAsPairEnumerator<'Key, Set<'Value>>(backingDict.GetEnumerator()) :> _
    interface System.Collections.IEnumerable with
        member __.GetEnumerator () = new KeyValueAsPairEnumerator<'Key, Set<'Value>>(backingDict.GetEnumerator()) :> _

type DefaultDictionary<'Key,'Value when 'Key : equality>(defaultVal : ('Key -> 'Value)) =
    let backingDict = new System.Collections.Generic.Dictionary<'Key, 'Value>()

    member __.ContainsKey key =
        backingDict.ContainsKey key

    member __.Item
        with get key =
            if backingDict.ContainsKey key then
                backingDict.[key]
            else
                defaultVal key
        and  set key value = backingDict.[key] <- value
    member __.Clear () =
        backingDict.Clear()

///
/// List of functions that should be called when T2 is ending some
/// reasoning and moving to a new problem.  Caches, Gensym, etc can add reset functions
/// here. Use the "add_clear" function
///
let clear_functions = ref []

///
/// Add a function to be called at an "end event"
///
let add_clear (f:unit -> unit) = clear_functions := f :: !clear_functions

///
/// Trigger an "end event"
///
let run_clear () = List.iter (fun f -> f()) !clear_functions

///
/// Return true if the input looks like its saying "yes/true/etc"
///
let true_string (b : string) =
    match b.ToLower() with
    | "true" | "t" | "1" | "y" | "yes" | "on" ->  true
    | "false" | "f" | "0" | "n" | "no" | "off" ->  false
    | _ -> failwith "Couldn't parse Boolean option parameter"

///
/// Uses .NET tricks to find out the location from which dieWith has been called.
///
let inline dieWith s =
    let sf = new System.Diagnostics.StackFrame(true)
    let st = new System.Diagnostics.StackTrace(sf)
    let cf = st.GetFrame(0)
    let mName = cf.GetMethod().Name
    let lineNo = cf.GetFileLineNumber()
    let colNo = cf.GetFileColumnNumber()
    let fn = cf.GetFileName()
    let fs =
        if s = "" then
            sprintf "Internal T2 error (%s, method %s, line %d, col %d). Please contact mabrocks@microsoft.com or bycook@microsoft.com" fn mName lineNo colNo
        else
            sprintf "Internal T2 error (%s, method %s, line %d, col %d): %s. Please contact mabrocks@microsoft.com or bycook@microsoft.com" fn mName lineNo colNo s

    failwith fs

///
/// Uses .NET tricks to find out the location from which die has been called.
///
let inline die () =
    dieWith ""

///
/// Maybe monad.  Lightweight exception-like handling (.NET exceptions are too expensive)
///
type MaybeMonad() =
    let succeed x = Some(x)
    let fail = None
    let bind p rest =
        match p with
        | None -> fail
        | Some r -> rest r
    let delay f = f()
    member b.Return(x)  = succeed x
    member b.Bind(p, rest) = bind p rest
    member b.Delay(f)   = delay f
    member b.Let(p,rest) = rest p

let maybe = MaybeMonad()

//
// Common operations on List that I dont see in F#
//
module List =

    let rec take n xs =
        if n<=0 then []
        else match xs with
             | (h::t) -> h::take (n-1) t
             | [] -> []

    let rec drop n xs =
        match xs with
        | (h::t) -> if n>0 then drop (n-1) t
                    else h::drop n t
        | [] -> []

    let rec last xs =
        match xs with
        | [x] -> x
        | (_::xs) -> last xs
        | [] -> die()

    let rec all_but_last xs =
        match xs with
        | [_] -> []
        | (x::xs) -> x::all_but_last xs
        | [] -> die()

    let rec concatMap f xs =
        match xs with
        | [] -> []
        | (x::xs) -> (f x) @ (concatMap f xs)

///
/// Make a cached-version of f
///
let memoize f =
    let tbl = System.Collections.Generic.Dictionary ()
    let clear =  tbl.Clear
    let mf x = match tbl.TryGetValue x with
               | (true, a) -> a
               | (false, _)-> let a = f x
                              tbl.Add(x, a)
                              a
    (clear,mf)

//
// Map extended with some additional operations
//
type Map<'Key,'Value when 'Key : comparison> with
    member m.Keys = seq {for kv in m -> kv.Key}
    member m.Items = seq {for kv in m -> (kv.Key, kv.Value)}
    member m.FindWithDefault key def = defaultArg (m.TryFind key) def
    static member findWithDefault key def (m: Map<'Key, 'Value>) = defaultArg (m.TryFind key) def
    static member Concat (ms: Map<'Key, 'Value> list) =
        let mutable result = Map.empty
        for m in List.rev ms do
            for KeyValue(k, v) in m do
                result <- result.Add(k, v :: result.FindWithDefault k [])
        result

type Set<'T when 'T : comparison> with
    member m.addMany o = Set.union m (Set.ofSeq o)
    ///Returns the set s1 \setminus set_of(s2)
    static member removeAll s1 s2 =
        Seq.fold (fun res ele -> Set.remove ele res) s1 s2
    ///Returns the set s1 \cup set_of(s2)
    static member addAll s1 s2 =
        Seq.fold (fun res ele -> Set.add ele res) s1 s2

type List<'T> with
    static member contains element list =
        List.exists ((=) element) list 
//
// Euclid's GCD algorithm
//
let rec gcd a b =
    let a = abs a
    let b = abs b

    if b = bigint.Zero then
        a
    else
        gcd b (a % b)

let lcm x y = abs ((x * y) / (gcd x y))

///
/// Call to see if timeout threshold has been exceeded
///
let check_timeout = ref (fun () -> ())

///
/// Set/reset the T2 timeout mechanism
///
let timeout t =
    let time_to_stop = System.DateTime.Now + System.TimeSpan.FromSeconds(t)
    let checker () =
        if (System.DateTime.Now > time_to_stop) then
            Printf.printf "Timeout after %f seconds\n" t
            raise (System.TimeoutException "T2 timeout")
        else ()
    check_timeout := checker

let reset_timeout () =
    check_timeout := (fun () -> ())
