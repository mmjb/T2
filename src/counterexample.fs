//////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      counterexample.fs
//
//  Abstract:
//
//      Tools for counterexamples
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

module Microsoft.Research.T2.Counterexample

open Programs

///
/// Counterexample to safety property ---> cycle = None.
/// Counterexample to liveness property ---> stem might be equal to None.
///
type cex =
    { stem : (int * command list* int) list option
    ; cycle : (int * command list *int) list option
    }

    override self.ToString () =
        let stringWriter = new System.IO.StringWriter();
        self.ToString stringWriter
        stringWriter.ToString()

    member self.ToString (outWriter : System.IO.TextWriter) =
        let outputPath pi =
            for ((k,cmds,k') : (int * Programs.command list * int)) in pi do
                outWriter.WriteLine("FROM: {0:D};", k)
                for cmd in cmds do
                    outWriter.WriteLine("  {0}", Programs.command2pp cmd)
                outWriter.WriteLine("TO: {0:D};", k')
        if self.stem.IsSome then
            outWriter.WriteLine("Stem of the counterexample:")
            outputPath self.stem.Value
        if self.cycle.IsSome then
            outWriter.WriteLine("Cycle of the counterexample:")
            outputPath self.cycle.Value

let make stem cycle = { stem = stem ; cycle = cycle }

let pos2cex (pos:pos) =
    match pos with
    | None -> "? 0"
    | Some(k,file) -> sprintf "%s %d" file k

///
/// Print SDV defect tool input in "fname"
///
let print_defect (pars : Parameters.parameters) cexs fname =
    if pars.create_defect_files then
        printf "Creating defect file %s\n" fname
        let h = new System.IO.StreamWriter(fname)
        let cnt = ref 0
        let line() = let k = !cnt in cnt := k+1; k
        let print_cmd (cmd:command) =
             match cmd.Position with
             | None -> ()
             | Some(loc,file) when cmd.Is_Assign
                  -> fprintf h "%d %s %d false ^^ Atomic Assignment\n"
                                      (line()) file loc
             | Some(loc,file)
                  -> fprintf h "%d %s %d false ^^ Atomic Conditional\n"
                                      (line()) file loc
        let print_cmds (_,cmds,_) = List.iter print_cmd cmds
        let print_cex k cex =
             fprintf h "%d ? %d true ^^ Call counterexamples cex%d\n"
                              (line()) k k

             // Process the stem
             begin match cex.stem with
             | None -> ()
             | Some(is) -> fprintf h "%d ? %d true ^^ Call cex%d stem\n"
                                          (line()) k k
                           List.iter print_cmds is
                           fprintf h "0 ? 0 false ^^ Return\n"
             end

             // Process the cycle
             begin match cex.cycle with
             | None -> ()
             | Some(is) -> fprintf h "%d ? %d true ^^ Call cex%d cycle\n"
                                          (line()) k k
                           List.iter print_cmds is
                           fprintf h "%d ? 0 false ^^ Return\n" (line())
                           fprintf h "%d ? 0 true ^^ Return\n" (line())
             end
        fprintf h "0 ? 0 true ^^ Call OS counterexamples\n"
        List.iteri print_cex cexs
        fprintf h "0 ? 0 false ^^ Return\n"
        fprintf h "Error Possibly non-terminating path found\n"
        h.Dispose()

let print_program (pars : Parameters.parameters) cexs fname =
    if pars.create_defect_files then
        printf "Creating T2 program file %s\n" fname
        let h = new System.IO.StreamWriter(fname)
        let print_cmd cmd = fprintf h "%s\n" (Programs.command2pp cmd)
        let print_cmds (k,cmds,k') = List.iter print_cmd cmds
        let print_cex k cex =
             // Process the stem
             fprintf h "\n\n// STEM %d ----------------------------------------------\n\n\n" k
             begin match cex.stem with
             | None -> ()
             | Some(is) ->
                           fprintf h "START: 0;\n"
                           fprintf h "FROM: 0;\n"
                           List.iter print_cmds (is)
                           fprintf h "TO: 1;\n"
             end

             fprintf h "\n\n// CYCLE %d ----------------------------------------------\n\n\n" k

             // Process the cycle
             begin match cex.cycle with
             | None -> ()
             | Some(is) ->
                           fprintf h "FROM: 1;\n"
                           List.iter print_cmds is
                           fprintf h "TO: 1;\n"
             end

        List.iteri print_cex cexs
        h.Dispose()
