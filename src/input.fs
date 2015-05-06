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

module Microsoft.Research.T2.Input

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
let simplify_chains (blocks : (string * Programs.command list * string) list) dont_chain =
    let nodes = Seq.collect (fun (s, _, e) -> [s ; e]) blocks |> Set.ofSeq |> ref
    let incoming = Utils.SetDictionary()
    let outgoing = Utils.SetDictionary()

    for (s, commands, e) in blocks do
        incoming.Add (e, (s, commands)) |> ignore
        outgoing.Add (s, (commands, e)) |> ignore

    //Search for nodes with one incoming and one outgoing transition. Connect pred/succ directly
    for n in !nodes do
        if not <| Set.contains n dont_chain then
            if incoming.[n].Count = 1 && outgoing.[n].Count = 1 then
                let (s, T1) = incoming.[n].MinimumElement //singleton -> minimum only ele
                let (T2, e) = outgoing.[n].MinimumElement

                //Don't do this for self-loops
                if s <> n && e <> n then
                    let T = T1@T2
                    incoming.RemoveKeyVal e (n, T2)
                    incoming.Add (e, (s, T))
                    outgoing.RemoveKeyVal s (T1, n)
                    outgoing.Add (s, (T, e))
                    incoming.Remove n |> ignore
                    outgoing.Remove n |> ignore

    [for (s, out) in outgoing do
        for (T, e) in out do
            yield (s, T, e)]

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
    let blocks = blocks |> List.map (fun (start, commands, target) -> (make_label start, commands, make_label target)) 
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
    let p = Programs.make pars avoid_chaining (make_label start) (blocks |> Seq.ofList) incomplete_abstraction
    let cp' = Programs.map p (make_label cp)
    (p,cp')
