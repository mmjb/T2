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

module Microsoft.Research.T2.Main

Stats.start_time "T2"
printfn "T2 program prover/analysis tool."

// Perform the arguments parsing
let (t2_input_file, runMode, parameters, fairness_constraint_string, output_type, output_file, imperative_style, java_nondet_style) = Arguments.parseArguments

//only run the tests, if this is wanted:
if runMode = Arguments.Test then
    ProgramTests.register_tests parameters
    parameters.create_defect_files <- false
    Test.run_tests parameters.timeout
    exit 0;

if t2_input_file = "" then
    eprintfn "You have to specify an input file for T2 with '-input_t2 foo.t2'."
    exit 3

let protectLocations =
    match runMode with
        | Arguments.CTL _
        | Arguments.Safety _ -> true
        | _ -> false

//Turn off tricks that don't always work for sepcific cases (this influences the input, thus we do it now) in the program representation that change the input program when just outputting
match runMode with
    | Arguments.Output ->
        parameters.abstract_disj <- false
        parameters.lazy_disj <- false
        parameters.elim_constants <- false
    | Arguments.Safety _ ->
        parameters.abstract_disj <- false
        parameters.lazy_disj <- false
    | _ -> ()

let (p, loc) =
    try
        Input.load_t2 parameters protectLocations t2_input_file
    with ParseError.Error ->
        eprintfn "Could not parse input file '%s'" t2_input_file
        exit 3

match runMode with
    | Arguments.Test -> () //Handled above, so this is never reached...
    | Arguments.Output ->
        match output_type.Value with
        | Parameters.Dot ->
          Output.print_dot_program p output_file
          printfn "Printing dot to %s completed" output_file
        | Parameters.Java ->
          let java_class = System.IO.Path.GetFileNameWithoutExtension output_file
          let directory = System.IO.Path.GetDirectoryName output_file
          Output.print_java_program p imperative_style java_nondet_style java_class directory
          printfn "Printing Java program to %s completed" output_file
        | Parameters.C ->
          Output.print_c_program p imperative_style output_file
          printfn "Printing C program to %s completed" output_file
        | Parameters.HSF ->
          Output.print_clauses p output_file
          printfn "Printing clauses to %s completed" output_file
        | Parameters.SMTPushdown ->
          Output.print_smtpushdown p output_file
          printfn "Printing SMTLIB Pushdown Automaton to %s completed" output_file
    | Arguments.Safety inputLoc ->
        let loc =
            match Map.tryFind (sprintf "loc_%d" inputLoc) !p.labels with
            | None ->
              eprintfn "Could not find location %d in program" inputLoc
              exit 3
            | Some loc -> loc
        match Reachability.prover parameters p loc with
        | None -> printfn "Safety proof succeeded"
        | Some _ -> printfn "Safety proof failed"
        
    | Arguments.Termination
    | Arguments.CTL _ ->
        let fairness_constraint =
            if fairness_constraint_string <> "" then
                let lexbuf = Microsoft.FSharp.Text.Lexing.LexBuffer<byte>.FromBytes (System.Text.Encoding.ASCII.GetBytes fairness_constraint_string)
                Some (Absparse.Fairness_constraint Absflex.token lexbuf)
            else
                None

        match runMode with 
        | Arguments.Termination ->
            let formula = CTL.AF(CTL.Atom(Formula.falsec))
            match Termination.bottomUpProver parameters p formula true fairness_constraint with
            | Some (true, proof_printer) -> 
                printfn "Termination proof succeeded"
                if parameters.print_proof then proof_printer System.Console.Out
            | Some (false, proof_printer) -> 
                printfn "Nontermination proof succeeded"
                if parameters.print_proof then proof_printer System.Console.Out
            | None -> printfn "Termination/nontermination proof failed"
        | Arguments.CTL formulaString ->
            let formula = CTL_Parser.parse_CTL formulaString
            match Termination.bottomUpProver parameters p formula false fairness_constraint with
            | Some (true, proof_printer) ->
                printfn "Temporal proof succeeded"
                if parameters.print_proof then proof_printer System.Console.Out
            | Some (false, proof_printer) ->
                printfn "Temporal proof failed"
                if parameters.print_proof then proof_printer System.Console.Out
            | None -> printfn "Temporal proof failed"
        | _ -> assert(false); //This cannot happen, but we need this fallthrough to avoid a warning.

Stats.end_time "T2"

// Print stats/times and exit
if parameters.print_stats then
    Stats.print_times ()
    Stats.print_stats ()

Z.finished()
