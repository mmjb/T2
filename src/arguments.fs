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
    | Output
    | Test
    | Safety of int
    | Termination
    | CTL of string

let parseArguments =
    let pars = Parameters.defaultParameters
    let t2_input_file = ref ""
    let mode = ref None
    let output_type = ref None
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
        match s.ToLower () with
            | "dot"
            | "dotty" ->
                output_type := Some Parameters.Dot
            | "java" ->
                output_type := Some Parameters.Java
            | "c" ->
                output_type := Some Parameters.C
            | "clauses"
            | "hsf" ->
                output_type := Some Parameters.HSF
            | "smt"
            | "smtlib"
            | "pushdown"
            | "smtpushdown" ->
                output_type := Some Parameters.SMTPushdown
            | _ ->
                eprintf "Cannot parse output type '%s' (known: dot, java, c, hsf, smtpushdown). Giving up.\n" s
                exit 1
        setMode Output

    let safetyImplementations = FSharpType.GetUnionCases typeof<Parameters.SafetyImplementation>
    let knownSafetyImplementationsString = String.concat ", " (Array.map (fun (i : UnionCaseInfo) -> i.Name) safetyImplementations)

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

    let args = 
        [
             new ArgInfo( "-log"
             , ArgType.Unit (fun () -> pars.print_log <- true)
             , "Turn on verbose logging"
             )

           ; new ArgInfo( "-safety_implementation"
             , ArgType.String (fun s -> pars.safety_implementation <- parse_safety_implementation_string s)
             , sprintf "Choose safety implementation. [known: %s, default: %A]" knownSafetyImplementationsString pars.safety_implementation
             )
           ; new ArgInfo( "-dottify_reachability"
             , ArgType.Unit (fun () -> pars.dottify_reachability <- true)
             , "Generate DOT graphs of the impact tree"
             )
           ; new ArgInfo( "-dottify_input_pgms"
             , ArgType.Unit (fun () -> pars.dottify_input_pgms <- true)
             , "Generate DOT graphs of the input program and its instrumented variants"
             )
           ; new ArgInfo( "-safety_cex"
             , ArgType.String (fun s -> pars.safety_counterexample <- Utils.true_string s)
             , "Produce safety counterexamples"
             )
           ; new ArgInfo( "-fc_look_back"
             , ArgType.Unit (fun () -> pars.fc_look_back <- true)
             , "Use path from root when doing force-cover"
             )
           ; new ArgInfo( "-fc_remove_on_fail"
             , ArgType.Unit (fun () -> pars.fc_remove_on_fail <- true)
             , "When trying force-cover v by w fails, remove w from the candidates of v"
             )
           ; new ArgInfo( "-fc_unsat_core"
             , ArgType.Unit (fun () -> pars.fc_unsat_core <- true)
             , "Use UNSAT core to reduce interpolation constraints"
             )

           ; new ArgInfo( "-print_interpolants"
             , ArgType.Unit (fun () -> pars.print_interpolants <- true)
             , "Print interpolants found"
             )
           ; new ArgInfo( "-check_interpolants"
             , ArgType.Unit (fun () -> pars.check_interpolants <- true)
             , "Double check interpolants found"
             )
           ; new ArgInfo( "-interpolant_sequence_ignore_beginning"
             , ArgType.Unit (fun () -> pars.seq_interpolation_ignore_last_constr <- false)
             , "Try to ignore constraints from the beginning"
             )

           ; new ArgInfo( "-print_proof"
             , ArgType.Unit (fun () -> pars.print_proof <- true)
             , "Print rank functions / recurrence sets after finishing a proof."
             )

           ; new ArgInfo( "-elim_constants"
             , ArgType.String (fun s -> pars.elim_constants <- Utils.true_string s) 
             , "Abstract away unusual constants"
             )

           ; new ArgInfo( "-lexicographic"
             , ArgType.String (fun s -> pars.lexicographic <- Utils.true_string s) 
             , "Try to find lexicographic ranking functions instead of disjunctive ones"
             )
           ; new ArgInfo( "-lex_opt_fewer_rfs"
             , ArgType.String (fun s -> pars.lex_opt_fewer_rfs <- Utils.true_string s) 
             , "Try to choose shorter lexicographic RFs (overrides other -lex_opt options)"
             )
           ; new ArgInfo( "-lex_opt_max_unaffected"
             , ArgType.String (fun s -> pars.lex_opt_max_unaffect <- Utils.true_string s) 
             , "Try to maximise the 'unaffecting score' of a lexicographic RF (overrides -lex_opt_scc_unaffected)"
             )
           ; new ArgInfo( "-lex_opt_scc_unaffected"
             , ArgType.String (fun s -> pars.lex_opt_scc_unaffected <- Utils.true_string s) 
             , "Try to find RFs that do not increase on any edge in the SCC"
             )
           ; new ArgInfo( "-polyrank"
             , ArgType.String (fun s -> pars.polyrank <- Utils.true_string s) 
             , "Try to find lexicographic polyranking functions"
             )
           ; new ArgInfo( "-lex_term_proof_first"
             , ArgType.String (fun s -> pars.lex_term_proof_first <- Utils.true_string s) 
             , "lexicographic termination proofs with program simplifications before starting safety proof"
             )
           ; new ArgInfo( "-do_ai_threshold"
             , ArgType.Int (fun n -> pars.do_ai_threshold <- n)
             , "Perform numerical abstr. int. before other analyses if we have less than n transitions"
             )
           ; new ArgInfo( "-ai_domain"
             , ArgType.String (fun s -> 
                                match s.ToLower() with 
                                | "oct" | "octagon" | "octagons" -> pars.ai_domain <- Parameters.Octagon
                                | "box" | "boxes"   | "invervals" -> pars.ai_domain <- Parameters.Box
                                | _ -> Utils.dieWith <| sprintf "Do not know numerical abstract domain %s" s)
             , sprintf "Numerical abstract domain used for abstract interpretation ('Octagon' or 'Box', default '%A')" pars.ai_domain
             )
           ; new ArgInfo( "-mcnp_style_bound_decr"
             , ArgType.String (fun s -> pars.mcnp_style_bound_decr <- Utils.true_string s) 
             , "Use 'anchor' idea from MCNP instead of bounded/decreasing requirement on each edge"
             )

           ; new ArgInfo( "-termination"
             , ArgType.Unit (fun () -> setMode Termination)
             , "Run refinement termination prover"
             )
           ; new ArgInfo( "-try_nonterm"
             , ArgType.String (fun s -> pars.prove_nonterm <- Utils.true_string s) 
             , "Try to prove nontermination (using very simple, cheap methods)"
             )
           ; new ArgInfo( "-safety"
             , ArgType.Int (fun n -> setMode (Safety n))
             , "Run safety prover, checking reachability of argument"
             )
           ; new ArgInfo( "-CTL"
             , ArgType.String (fun s -> setMode (CTL s))
             , "Run CTL temporal prover"
             )
           ; new ArgInfo( "-fairness"
             , ArgType.String (fun s -> fairness_constraint_string := s)
             , "Only consider program runs satisfying the given fairness constraint (p, q)"
             )
           ; new ArgInfo( "-input_t2"
             , ArgType.String (fun s -> t2_input_file := s)
             , "Give T2 syntax input file"
             )
           ; new ArgInfo( "-output_as"
             , ArgType.String parse_output_type_string
             , "Output input file in given format (known: dot, java, c, hsf, smtpushdown)"
             )
           ; new ArgInfo( "-output_file"
             , ArgType.String (fun s -> output_file := s)
             , sprintf "Choose output file name (default '%s', use in conjunction with -output_as)" !output_file
             )
           ; new ArgInfo( "-imperative_style"
             , ArgType.String (fun s ->
                                match s with
                                | "loop" -> imperative_style := Parameters.Loop
                                | "goto" -> imperative_style := Parameters.Goto
                                | _ -> Utils.dieWith (sprintf "Do not know imperative program style '%s', use loop/goto." s))
             , sprintf "Choose style of imperative program: 'loop' for while loop with switch over pc, 'goto' for explicit jumps. (default '%A')" !imperative_style
             )
           ; new ArgInfo( "-java_nondet_style"
             , ArgType.String (fun s ->
                                match s with
                                | "aprove" -> java_nondet_style := Parameters.Aprove
                                | "julia" -> java_nondet_style := Parameters.Julia
                                | _ -> Utils.dieWith (sprintf "Do not know nondet style '%s', use aprove/julia." s))
             , sprintf "Choose implementation of nondet() in Java output. Supported options are 'aprove' and 'julia'. (default: '%A')" !java_nondet_style
             )
           ; new ArgInfo( "-tests"
             , ArgType.Unit (fun () -> setMode Test)
             , "Run unit tests"
             )
           ; new ArgInfo( "-stats"
             , ArgType.Unit (fun () -> pars.print_stats <- true)
             , "Print stats"
             )
           ; new ArgInfo( "-timeout"
             , ArgType.Float (fun t -> pars.timeout <- t)
             , "Timeout for the overall proof"
             )
           ;
        ]
    
    ArgParser.Parse args

    if (!mode).IsNone then
        eprintfn "No valid action option (-tests, -termination, -safety, -CTL, -output_as) given"
        exit 3

    (!t2_input_file, (!mode).Value, pars, !fairness_constraint_string, !output_type, !output_file, !imperative_style, !java_nondet_style)
