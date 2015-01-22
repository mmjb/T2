////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      main.fs
//
//  Abstract:
//
//      Top level for T2 program prover.  Parses arguments and executes accordingly
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

if !Arguments.print_log then
    printf "T2 program prover/analysis tool.\n"

Stats.start_time "T2"

// Perform the arguments parsing
ArgParser.Parse Arguments.args

if (!Arguments.mode).IsNone then
    eprintfn "No valid action option (-tests, -termination, -safety, -CTL, -output_as) given"
    exit 3

let mode = (!Arguments.mode).Value
//only run the tests, if this is wanted:
if mode = Arguments.Test then
    ProgramTests.register_tests()
    Arguments.create_defect_files := false
    Test.run_tests()
    exit 0;

if !Arguments.t2_input_file = "" then
    eprintfn "You have to specify an input file for T2 with '-input_t2 foo.t2'."
    exit 3

let protectLocations =
    match mode with
        | Arguments.CTL _
        | Arguments.Safety _ -> true
        | _ -> false

let (p, loc) =
    try
        Input.load_t2 protectLocations !Arguments.t2_input_file
    with ParseError.Error ->
        eprintfn "Could not parse input file '%s'" !Arguments.t2_input_file
        exit 3

match mode with
    | Arguments.Test -> () //Handled above, so this is never reached...
    | Arguments.Output ->
        let out_file = !Arguments.output_file

        //Turn off tricks in the program representation that change the input program
        Arguments.abstract_disj := false
        Arguments.lazy_disj := false
        Arguments.elim_constants := false
        match (!Arguments.output_type).Value with
        | Arguments.Dot ->
          Output.print_dot_program p out_file
          printfn "Printing dot to %s completed" out_file
        | Arguments.Java ->
          let java_class = System.IO.Path.GetFileNameWithoutExtension out_file
          let directory = System.IO.Path.GetDirectoryName out_file
          Output.print_java_program p java_class directory
          printfn "Printing Java program to %s completed" out_file
        | Arguments.C ->
          Output.print_c_program p out_file
          printfn "Printing C program to %s completed" out_file
        | Arguments.HSF ->
          Output.print_clauses p out_file
          printfn "Printing clauses to %s completed" out_file
        | Arguments.SMTPushdown ->
          Output.print_smtpushdown p out_file
          printfn "Printing SMTLIB Pushdown Automaton to %s completed" out_file
    | Arguments.Safety inputLoc ->
        let loc =
            match Map.tryFind (sprintf "loc_%d" inputLoc) !p.labels with
            | None ->
              eprintfn "Could not find location %d in program" inputLoc
              exit 3
            | Some loc -> loc
        match Reachability.prover p loc with
        | None -> printfn "Safety proof succeeded"
        | Some _ -> printfn "Safety proof failed"
        
    | Arguments.Termination
    | Arguments.CTL _ ->
        let fairness_constraint =
            if !Arguments.fairness_constraint_string <> "" then
                let lexbuf = Microsoft.FSharp.Text.Lexing.LexBuffer<byte>.FromBytes (System.Text.Encoding.ASCII.GetBytes !Arguments.fairness_constraint_string)
                Some (Absparse.Fairness_constraint Absflex.token lexbuf)
            else
                None

        match mode with 
        | Arguments.Termination ->
            let formula = CTL.AF(CTL.Atom(Formula.falsec))
            match Termination.bottomUpProver p formula true fairness_constraint with
            | Some (true, proof_printer) -> 
                printfn "Termination proof succeeded"
                if !Arguments.print_proof then proof_printer ()
            | Some (false, proof_printer) -> 
                printfn "Nontermination proof succeeded"
                if !Arguments.print_proof then proof_printer ()
            | None -> printfn "Termination/nontermination proof failed"
        | Arguments.CTL formulaString ->
            let formula = CTL_Parser.parse_CTL formulaString
            match Termination.bottomUpProver p formula false fairness_constraint with
            | Some (true, proof_printer) ->
                printfn "Temporal proof succeeded"
                if !Arguments.print_proof then proof_printer ()
            | Some (false, proof_printer) ->
                printfn "Temporal proof failed"
                if !Arguments.print_proof then proof_printer ()
            | None -> printfn "Temporal proof failed"
        | _ -> assert(false); //This cannot happen, but we need this fallthrough to avoid a warning.

Stats.end_time "T2"

// Print stats/times and exit
if !Arguments.print_stats then
    Stats.print_times ()
    Stats.print_stats ()

Z.finished()
