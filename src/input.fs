////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      input.fs
//
//  Abstract:
//
//      Interface for loading input programs.
//
//  Notes:
//
//      * We define a simple T2 input file format, with parser, etc.
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

module Input

///
/// Parse from a file, returning a program
///
let parse (filename : string) =
    let inreader = new System.IO.BinaryReader (System.IO.File.OpenRead filename)
    let res =
        try ParseError.startFile filename
            let lexbuf = Microsoft.FSharp.Text.Lexing.LexBuffer<byte>.FromBinaryReader inreader
            ParseError.theLexbuf := lexbuf
            Absparse.program Absflex.token lexbuf
        with _ ->
            inreader.Dispose ()
            let f = ParseError.getFilename()
            let n = ParseError.getLine()
            printf "Parse error at line %d in %s\n" n f
            raise ParseError.Error
    inreader.Dispose ()
    res

///
/// replace edges x->y->z with x->z if there are
/// no other edges from/to y.
///
let simplify_chains blocks dont_chain =
    let nodes' =
        [for s, _, e in blocks do
            yield s
            yield e
        ] |> Set.ofList
    let nodes = ref nodes'

    let mutable incoming = [for n in !nodes -> (n, Set.empty)] |> Map.ofList
    let mutable outgoing = [for n in !nodes -> (n, Set.empty)] |> Map.ofList

    for s, T, e in blocks do
        incoming <- incoming.Add(e, incoming.[e].Add (s, T))
        outgoing <- outgoing.Add(s, outgoing.[s].Add (T, e))

    let as_singleton set =
        (Set.toList set).Head

    for n in !nodes do
        if not <| Set.contains n dont_chain then
            if Set.count incoming.[n] = 1 && Set.count outgoing.[n] = 1 then
                let s, T1 = as_singleton incoming.[n]
                let T2, e = as_singleton outgoing.[n]
                let T = T1@T2

                // don't do this for self-loops:
                if (s <> n && e <> n) then
                    incoming <- incoming.Add(e, (incoming.[e].Remove(n, T2)).Add(s, T))
                    outgoing <- outgoing.Add(s, (outgoing.[s].Remove(T1, n)).Add(T, e))

                    incoming <- incoming.Remove n
                    outgoing <- outgoing.Remove n

    let outgoing = outgoing

    let result =
        [for KeyValue(s, out) in outgoing do
            for T, e in out do
                yield s, T, e]

    Stats.add_stat "simplify_chains - total" (List.length blocks)
    Stats.add_stat "simplify_chains - eliminated" (List.length result)

    //Now get rid of self loops:
    let cleaned_result = ref []
    let i = ref 0
    let rec get_new_node nodes =
        let name = "tmp_" + (!i).ToString()
        i := !i + 1
        if not (Set.contains name !nodes) then
           nodes := Set.add name !nodes
           name
        else
            get_new_node nodes

    for e in result do
        let (k, l, k') = e
        if (k <> k') then
            cleaned_result := e::!cleaned_result
        else
            let new_node = get_new_node nodes
            cleaned_result := (k,l,new_node)::(new_node,[],k')::!cleaned_result

    !cleaned_result

///
/// Load a program in T2 format
///
let load_t2 (pars : Parameters.parameters) avoid_chaining filename =
    Absparse.annotate := true
    let (start,cp,blocks,_,incomplete_abstraction) = parse filename
    let make_label loc = 
        match loc with
        | Absparse.NumLoc i ->
            sprintf "loc_%d" i
        | Absparse.NameLoc n ->
            n
    let blocks = [for s, T, e in blocks -> (make_label s), T, (make_label e)]
    let blocks =
        (*
            Merging block chains is not sound for AG proofs. Consider
                START:0;
                FROM:0;
                assume (x > 0);
                TO:1;
                FROM:1;
                x := -1;
                TO:2;
                FROM:2;
                x := 1;
                TO:3;
            and AG (x > 0). False for the original program, but if we do the chaining, we consider this instead:
                START:0;
                FROM:0;
                assume (x > 0);
                x := -1;
                x := 1;
                TO:3;
            Here, at all non-initial program points the property holds and we prove that the formula holds.
        *)
        if avoid_chaining then
            blocks
        else
            simplify_chains blocks (Set.singleton (make_label start))
    let p = Programs.make pars avoid_chaining (make_label start) blocks incomplete_abstraction
    let cp' = Programs.map p (make_label cp)
    (p,cp')
