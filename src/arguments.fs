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

module Microsoft.Research.T2.Arguments
open Microsoft.FSharp.Reflection

type runMode =
    | Output of Parameters.outputFormat
    | Test
    | Safety of int
    | Termination
    | CTL of string
    | CTLStar of string

let parseArguments arguments =
    let pars = Parameters.defaultParameters
    let t2_input_file = ref ""
    let mode = ref None
    let output_file = ref "out"
    let imperative_style = ref Parameters.Goto
    let java_nondet_style = ref Parameters.Aprove
    let fairness_constraint_string = ref ""

    let setMode m =
        if (!mode).IsSome then
            eprintf "Conflicting run modes %A and %A. Please only select one.\n" (!mode).Value m
            exit 1
        else
            mode := Some m

    let parse_output_type_string (s : string) =
        let output_type =
            match s.ToLower () with
            | "dot"
            | "dotty" ->
                Parameters.Dot
            | "java" ->
                Parameters.Java
            | "c" ->
                Parameters.C
            | "clauses"
            | "hsf" ->
                Parameters.HSF
            | "smt"
            | "smtlib"
            | "pushdown"
            | "smtpushdown" ->
                Parameters.SMTPushdown
            | _ ->
                eprintf "Cannot parse output type '%s' (known: dot, java, c, hsf, smtpushdown). Giving up.\n" s
                exit 1
        setMode (Output output_type)

    let safetyImplementations = FSharpType.GetUnionCases typeof<Parameters.SafetyImplementation>
    let knownSafetyImplementationsString = String.concat ", " (Array.map (fun (i : UnionCaseInfo) -> i.Name) safetyImplementations)
    let knownOutputFormats = String.concat ", " (Array.map (fun (i : UnionCaseInfo) -> i.Name) (FSharpType.GetUnionCases typeof<Parameters.outputFormat>))
    let knownAbstractDomains = String.concat ", " (Array.map (fun (i : UnionCaseInfo) -> i.Name) (FSharpType.GetUnionCases typeof<Parameters.numAbsDomain>))
    let knownImperativeProgramStyle = String.concat ", " (Array.map (fun (i : UnionCaseInfo) -> i.Name) (FSharpType.GetUnionCases typeof<Parameters.imperativeProgramStyle>))
    let knownJavaNondetStyle = String.concat ", " (Array.map (fun (i : UnionCaseInfo) -> i.Name) (FSharpType.GetUnionCases typeof<Parameters.javaNondetStyle>))

    let parse_safety_implementation_string (s : string) =
        let s = s.ToLower()
        let chosen : Parameters.SafetyImplementation option ref = ref None
        for safetyImplementation in safetyImplementations do
            if s = safetyImplementation.Name.ToLower() then
                chosen := Some (FSharpValue.MakeUnion (safetyImplementation, [||]) :?> Parameters.SafetyImplementation)
        match !chosen with
        | Some i -> i
        | None ->
            failwithf "Cannot parse safety implementation '%s' (known: %s). Giving up.\n" s knownSafetyImplementationsString

    let optionSet = Mono.Options.OptionSet()
    optionSet
             .Add( "tests"
                 , "Run unit tests"
                 , fun _ -> setMode Test)
             .Add( "input_t2="
                 , "Input file (in T2 syntax)"
                 , fun s -> t2_input_file := s)
             .Add( "safety="
                 , "Run safety prover, checking reachability of given location"
                 , fun n -> setMode (Safety (int n)))
             .Add( "termination"
                 , "Run termination prover"
                 , fun _ -> setMode Termination)
             .Add( "CTL="
                 , "Run CTL temporal prover on given formula"
                 , fun s -> setMode (CTL s))
             .Add( "CTLStar="
                 , "Run CTL* temporal prover on given formula"
                 , fun s -> setMode (CTLStar s))
             .Add( "fairness="
                 , "Only consider program runs satisfying the given fairness constraint (p, q)"
                 , fun s -> fairness_constraint_string := s)
             .Add( "output_as="
                 , sprintf "Output input file in given format [known: %s]" knownOutputFormats
                 , parse_output_type_string)
             .Add( "output_file="
                 , sprintf "Choose output file name (default '%s', use in conjunction with -output_as)" !output_file
                 , fun s -> output_file := s)
             .Add( "timeout="
                 , "Timeout for the overall proof attempt"
                 , fun s -> pars.timeout <- float s)
             .Add( "log"
                 , "Turn on verbose logging"
                 , fun _ -> pars.print_log <- true)
             .Add( "print_proof"
                 , "Print rank functions / recurrence sets after finishing a proof"
                 , fun _ -> pars.print_proof <- true)
             .Add( "stats"
                 , "Print statistics about T2 internals"
                 , fun _ -> pars.print_stats <- true)
             .Add( "help"
                 , "Print this short help. Use '--full-help' to view all options"
                 , fun _ -> optionSet.WriteOptionDescriptions(System.Console.Error, false); exit 0)
             .Add( "full-help"
                 , "Print help including all options"
                 , fun _ -> optionSet.WriteOptionDescriptions(System.Console.Error, true); exit 0)
             .Add( "debugger"
                 , "Start under VS debugger supervision"
                 , fun _ -> System.Diagnostics.Debugger.Launch() |> ignore
                 , false)

             ///// Output things:
             .Add( "debug"
                 , "Turn on debug logging"
                 , fun _ -> pars.print_debug <- true
                 , true)
             .Add( "dottify_reachability"
                 , "Generate DOT graphs of the impact tree"
                 , fun _ -> pars.dottify_reachability <- true
                 , true)
             .Add( "dottify_input_pgms"
                 , "Generate DOT graphs of the input program and its instrumented variants"
                 , fun _ -> pars.dottify_input_pgms <- true
                 , true)
             .Add( "safety_cex="
                 , "Produce safety counterexamples"
                 , fun s -> pars.safety_counterexample <- Utils.true_string s
                 , true)

             .Add( "imperative_style="
                 , sprintf "Choose style of imperative output program. [known: %s, default %A]" knownImperativeProgramStyle !imperative_style
                 , fun s ->
                       match s with
                       | "loop" -> imperative_style := Parameters.Loop
                       | "goto" -> imperative_style := Parameters.Goto
                       | _ -> Utils.dieWith (sprintf "Do not know imperative program style '%s', use loop/goto" s)
                 , true)
             .Add( "java_nondet_style="
                 , sprintf "Choose implementation of nondet() in Java output. [known: %s, default %A]" knownJavaNondetStyle !java_nondet_style
                 , fun s ->
                       match s with
                       | "aprove" -> java_nondet_style := Parameters.Aprove
                       | "julia" -> java_nondet_style := Parameters.Julia
                       | _ -> Utils.dieWith (sprintf "Do not know nondet style '%s', use aprove/julia" s)
                 , true)

             ///// Parsing / program representation things:
             .Add( "do_ai_threshold="
                 , "Perform numerical abstr. int. before other analyses if we have less than n transitions"
                 , fun n -> pars.do_ai_threshold <- int n
                 , true)
             .Add( "ai_domain="
                 , sprintf "Numerical abstract domain used for abstract interpretation [known: %s, default %A]" knownAbstractDomains pars.ai_domain
                 , fun (s : string) -> 
                        match s.ToLower() with 
                        | "oct" | "octagon" | "octagons" -> pars.ai_domain <- Parameters.Octagon
                        | "box" | "boxes"   | "invervals" -> pars.ai_domain <- Parameters.Box
                        | _ -> Utils.dieWith <| sprintf "Do not know numerical abstract domain %s" s
                 , true)
             .Add( "elim_constants="
                 , "Abstract away unusual constants"
                 , fun s -> pars.elim_constants <- Utils.true_string s
                 , true)
             .Add( "elim_temp_vars="
                 , "Try to eliminate variables that are only in temporary use"
                 , fun s -> pars.elim_temp_vars <- Utils.true_string s
                 , true)

             ///// Safety things:
             .Add( "safety_implementation="
                 , sprintf "Choose safety implementation. [known: %s, default: %A]" knownSafetyImplementationsString pars.safety_implementation
                 , fun (s : string) -> pars.safety_implementation <- parse_safety_implementation_string s)

             .Add( "fc_look_back"
                 , "<Impact> Use path from root when doing force-cover"
                 , fun _ -> pars.fc_look_back <- true
                 , true)
             .Add( "fc_remove_on_fail"
                 , "<Impact> When trying force-cover v by w fails, remove w from the candidates of v"
                 , fun _ -> pars.fc_remove_on_fail <- true
                 , true)
             .Add( "fc_unsat_core"
                 , "<Impact> Use UNSAT core to reduce interpolation constraints"
                 , fun _ -> pars.fc_unsat_core <- true
                 , true)
             .Add( "print_interpolants"
                 , "<Impact> Print interpolants found"
                 , fun _ -> pars.print_interpolants <- true
                 , true)
             .Add( "check_interpolants"
                 , "<Impact> Double check interpolants found"
                 , fun _ -> pars.check_interpolants <- true
                 , true)
             .Add( "interpolant_sequence_ignore_beginning"
                 , "<Impact> Try to ignore constraints from the beginning"
                 , fun _ -> pars.seq_interpolation_ignore_last_constr <- false
                 , true)

             ///// Terminationy things:
             .Add( "try_nonterm="
                 , "Try to prove nontermination (using very simple, cheap methods)"
                 , fun s -> pars.prove_nonterm <- Utils.true_string s
                 , true)
             .Add( "lexicographic="
                 , "Try to find lexicographic ranking functions instead of disjunctive ones"
                 , fun s -> pars.lexicographic <- Utils.true_string s
                 , true)
             .Add( "lex_opt_fewer_rfs="
                 , "Try to choose shorter lexicographic RFs (overrides other -lex_opt options)"
                 , fun s -> pars.lex_opt_fewer_rfs <- Utils.true_string s
                 , true)
             .Add( "lex_opt_max_unaffected="
                 , "Try to maximise the 'unaffecting score' of a lexicographic RF (overrides -lex_opt_scc_unaffected)"
                 , fun s -> pars.lex_opt_max_unaffect <- Utils.true_string s
                 , true)
             .Add( "lex_opt_scc_unaffected="
                 , "Try to find RFs that do not increase on any edge in the SCC"
                 , fun s -> pars.lex_opt_scc_unaffected <- Utils.true_string s
                 , true)
             .Add( "polyrank="
                 , "Try to find lexicographic polyranking functions"
                 , fun s -> pars.polyrank <- Utils.true_string s
                 , true)
             .Add( "lex_term_proof_first="
                 , "lexicographic termination proofs with program simplifications before starting safety proof"
                 , fun s -> pars.lex_term_proof_first <- Utils.true_string s
                 , true)
             .Add( "mcnp_style_bound_decr="
                 , "Use 'anchor' idea from MCNP instead of bounded/decreasing requirement on each edge"
                 , fun s -> pars.mcnp_style_bound_decr <- Utils.true_string s
                 , true)
             .Add( "seq_interpolation="
                 , "Use sequential interpolation"
                 , fun s -> pars.seq_interpolation <- Utils.true_string s
                 , true)
             .Add( "iterative_reachability="
                 , "Use iterative reachability proving"
                 , fun s -> pars.iterative_reachability <- Utils.true_string s
                 , true)
        |> ignore

    let remainingArguments = optionSet.Parse arguments

    //For people who forget to use -input_t2 ...
    if remainingArguments.Count = 1 && System.IO.File.Exists remainingArguments.[0] && !t2_input_file = "" then
        t2_input_file := remainingArguments.[0]
    else if remainingArguments.Count > 0 then
        eprintfn "Arguments %s could not be parsed" (remainingArguments |> Seq.map (fun a -> "'" + a + "'") |> String.concat ", ")
        optionSet.WriteOptionDescriptions(System.Console.Error, false)
        exit 3
       
    if (!mode).IsNone then
        eprintfn "No valid action option (--tests, --termination, --safety, --CTL, --CTLStar, --output_as) given. Usage:"
        optionSet.WriteOptionDescriptions(System.Console.Error, false)
        exit 3

    (!t2_input_file, (!mode).Value, pars, !fairness_constraint_string, !output_file, !imperative_style, !java_nondet_style)
