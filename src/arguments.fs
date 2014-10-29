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

module Arguments

// ---------------------------- Logging things ----------------------------

/// Set to true to enable verbose logging spew from across T2
let print_log = ref false

/// Set to true to enable verbose debug logging spew from across T2
let print_debug = ref false

// ---------------------------- Counterexample things ----------------------------

/// When testing we dont want to create a billion defect files, so we
/// can shut this option off by setting create_defect_files to false
let create_defect_files = ref true

// ---------------------------- Reachability things ----------------------------

/// Generate DOT graphs of the impact tree (at each step)
let dottify_reachability = ref false
/// Generate DOT graphs of the input program
let dottify_input_pgms = ref false
/// Check sanity of Impact graphs
let sanity_checking = ref true

/// Produce safety counterexamples
let safety_counterexample = ref false

/// Use path from root when doing force-cover
let fc_look_back = ref false
/// When trying force-cover v by w fails, remove w from the candidates of v
let fc_remove_on_fail = ref false
/// Use UNSAT core to reduce interpolation constraints
let fc_unsat_core = ref false

// ---------------------------- Interpolation things ----------------------------

/// Print interpolants found
let print_interpolants = ref false
/// Double check interpolants found
let check_interpolants = ref true

/// Try to ignore constraints from the beginning
let seq_interpolation_ignore_last_constr = ref true

// ---------------------------- Termination things ----------------------------

/// Print ranking functions / recurrence sets to stdout after the proof?
let print_proof = ref false

/// Try proving non-termination as well as termination?
let prove_nonterm = ref true

/// If lexicographic fails, try detecting initial condition?
let init_cond = ref false

/// If lexicographic fails, try unrolling a bit?
let unrolling = ref true
let unrolling_limit = ref 3

/// Try to find lexicographic rank functions for all cutpoints
let lexicographic = ref true

///Try to find lexicographic RFs of shorter length?
///Don't have this on at the same time as max_unaffect
let lex_opt_fewer_rfs = ref false

///Try to find lexicographic RFs s.t. the relations affect each other's RFs as little as possible?
///Don't have this on at the same time as fewer_rfs
let lex_opt_max_unaffect = ref false

/// Try to find a rf such that the considered relation is strictly decreasing and bounded and all SCC transitions are weakly decreasing
let lex_opt_scc_unaffected = ref false

/// Start looking for polyranking lexicographic rank functions in the event of failure with lexicographic RFs. Does nothing if lexicographic isn't on.
let polyrank = ref true
let polyrank_max_depth = ref 4

/// Try lexicographic termination proofs with program simplifications before starting safety proof?
let lex_term_proof_first = ref true

/// Should we use bounded/decreasing split from Lemma 31 in "SAT-Based Termination Analysis Using Monotonicity Constraints over the Integers" (TPLP)
let mcnp_style_bound_decr = ref false

// ---------------------------- Fairness constraint  ----------------------------
//
let fairness_constraint_string = ref ""

// ---------------------------- Program things ----------------------------

/// Lazily split disjunction within assumes.
/// If it's false, disjunctions are split eagerly.
let lazy_disj = ref true

/// Symbolic abstraction: change constants in the program from 5 to var5.  Constraints are added
/// so that var5<var6,etc. This is needed because otherwise, the reachability graph is unwound
/// (i.e., the program is executed!) until actually reaching the constants. Not so bad for 5, but
/// very bad for 1000.
let elim_constants = ref true

/// Perform numerical abstr. interpretation if we have less than !do_ai_threshold transitions
let do_ai_threshold = ref 50
/// This is flipped to true if we performed AI and enables further optimizations later on
let did_ai_first = ref false

/// Choice of numerical domain for abstract interpretation
type numAbsDomain = Box | Octagon
let ai_domain = ref Box

/// When we see assume(p || q || r), should we just use "assume(true)"?
let abstract_disj = ref false

// ---------------------------- Output things ----------------------------
let c_file = ref ""
type imperativeProgramStyle = Loop | Goto
let imperative_style = ref Goto
type javaNondetStyle = Aprove | Julia
let java_nondet_style = ref Aprove
let clauses_file = ref ""
let dot_file = ref ""

// ---------------------------- Main things ----------------------------

//
// Argument parsing. See args list for description of each of the flags
//

let t2_input_file = ref ""

let print_stats = ref false
let timeout = ref 300.0

type runMode = 
    | Output
    | Test
    | Safety of int
    | Termination
    | CTL of string
let mode = ref None
let setMode m =
    if (!mode).IsSome then
        eprintf "Conflicting run modes %A and %A. Please only select one.\n" (!mode).Value m
        exit 1
    else
        mode := Some m

type outputFormat =
    | Dot
    | Java
    | C
    | HSF
    | SMTPushdown
let output_type : outputFormat option ref = ref None
let parse_output_type_string (s : string) =
    match s.ToLower () with
        | "dot"
        | "dotty" ->
            output_type := Some Dot
        | "java" ->
            output_type := Some Java
        | "c" ->
            output_type := Some C
        | "clauses"
        | "hsf" ->
            output_type := Some HSF
        | "smt"
        | "smtlib"
        | "pushdown"
        | "smtpushdown" ->
            output_type := Some SMTPushdown
        | _ ->
            eprintf "Cannot parse output type '%s' (known: dot, java, c, hsf, smtpushdown). Giving up.\n" s
            exit 1
    setMode Output
let output_file = ref "out"


///////////////////////////////////////////////////////////////////////////////
////////////////////////// The actual argument list ///////////////////////////
///////////////////////////////////////////////////////////////////////////////
let args = [
             ( "-log"
             , ArgType.Unit (fun () -> print_log := true)
             , "Turn on verbose logging"
             )

           ; ( "-dottify_reachability"
             , ArgType.Unit (fun () -> dottify_reachability := true)
             , "Generate DOT graphs of the impact tree"
             )
           ; ( "-dottify_input_pgms"
             , ArgType.Unit (fun () -> dottify_input_pgms := true)
             , "Generate DOT graphs of the input program and its instrumented variants"
             )
           ; ( "-safety_cex"
             , Utils.bool_option safety_counterexample
             , "Produce safety counterexamples"
             )
           ; ( "-fc_look_back"
             , ArgType.Unit (fun () -> fc_look_back := true)
             , "Use path from root when doing force-cover"
             )
           ; ( "-fc_remove_on_fail"
             , ArgType.Unit (fun () -> fc_remove_on_fail := true)
             , "When trying force-cover v by w fails, remove w from the candidates of v"
             )
           ; ( "-fc_unsat_core"
             , ArgType.Unit (fun () -> fc_unsat_core := true)
             , "Use UNSAT core to reduce interpolation constraints"
             )

           ; ( "-print_interpolants"
             , ArgType.Unit (fun () -> print_interpolants := true)
             , "Print interpolants found"
             )
           ; ( "-check_interpolants"
             , ArgType.Unit (fun () -> check_interpolants := true)
             , "Double check interpolants found"
             )
           ; ( "-interpolant_sequence_ignore_beginning"
             , ArgType.Unit (fun () -> seq_interpolation_ignore_last_constr := false)
             , "Try to ignore constraints from the beginning"
             )

           ; ( "-print_proof"
             , ArgType.Unit (fun () -> print_proof := true)
             , "Print rank functions / recurrence sets after finishing a proof."
             )

           ; ( "-lazy_disj"
             , Utils.bool_option lazy_disj
             , "Lazy treatment of disjunctions"
             )
           ; ( "-elim_constants"
             , Utils.bool_option elim_constants
             , "Abstract away unusual constants"
             )
           ; ( "-abstract_disj"
             , Utils.bool_option abstract_disj
             , "Abstract away disjunction in assumes"
             )

           ; ( "-lexicographic"
             , Utils.bool_option lexicographic
             , "Try to find lexicographic ranking functions instead of disjunctive ones"
             )
           ; ( "-lex_opt_fewer_rfs"
             , Utils.bool_option lex_opt_fewer_rfs
             , "Try to choose shorter lexicographic RFs (overrides other -lex_opt options)"
             )
           ; ( "-lex_opt_max_unaffected"
             , Utils.bool_option lex_opt_max_unaffect
             , "Try to maximise the 'unaffecting score' of a lexicographic RF (overrides -lex_opt_scc_unaffected)"
             )
           ; ( "-lex_opt_scc_unaffected"
             , Utils.bool_option lex_opt_scc_unaffected
             , "Try to find RFs that do not increase on any edge in the SCC"
             )
           ; ( "-polyrank"
             , Utils.bool_option polyrank
             , "Try to find lexicographic polyranking functions"
             )
           ; ( "-lex_term_proof_first"
             , Utils.bool_option lex_term_proof_first
             , "lexicographic termination proofs with program simplifications before starting safety proof"
             )
           ; ( "-do_ai_threshold"
             , ArgType.Int (fun n -> do_ai_threshold := n)
             , "Perform numerical abstr. int. before other analyses if we have less than n transitions"
             )
           ; ( "-ai_domain"
             , ArgType.String (fun s -> 
                                match s.ToLower() with 
                                | "oct" | "octagon" | "octagons" -> ai_domain := Octagon
                                | "box" | "boxes"   | "invervals" -> ai_domain := Box
                                | _ -> Utils.dieWith <| sprintf "Do not know numerical abstract domain %s" s)
             , sprintf "Numerical abstract domain used for abstract interpretation ('Octagon' or 'Box', default '%A')" !ai_domain
             )
           ; ( "-mcnp_style_bound_decr"
             , Utils.bool_option mcnp_style_bound_decr
             , "Use 'anchor' idea from MCNP instead of bounded/decreasing requirement on each edge"
             )

           ; ( "-termination"
             , ArgType.Unit (fun () -> setMode Termination)
             , "Run refinement termination prover"
             )
           ; ( "-try_nonterm"
             , Utils.bool_option prove_nonterm
             , "Try to prove nontermination (using very simple, cheap methods)"
             )
           ; ( "-safety"
             , ArgType.Int (fun n -> setMode (Safety n))
             , "Run safety prover, checking reachability of argument"
             )
           ; ( "-CTL"
             , ArgType.String (fun s -> setMode (CTL s))
             , "Run CTL temporal prover"
             )
           ; ( "-fairness"
             , ArgType.String (fun s -> fairness_constraint_string := s)
             , "Only consider program runs satisfying the given fairness constraint (p, q)"
             )
           ; ( "-input_t2"
             , ArgType.String (fun s -> t2_input_file := s)
             , "Give T2 syntax input file"
             )
           ; ( "-output_as"
             , ArgType.String parse_output_type_string
             , "Output input file in given format (known: dot, java, c, hsf, smtpushdown)"
             )
           ; ( "-output_file"
             , ArgType.String (fun s -> output_file := s)
             , "Choose output file name (default 'out', use in conjunction with -output_as)"
             )
           ; ( "-imperative_style"
             , ArgType.String (fun s ->
                                match s with
                                | "loop" -> imperative_style := Loop
                                | "goto" -> imperative_style := Goto
                                | _ -> Utils.dieWith (sprintf "Do not know imperative program style '%s', use loop/goto." s))
             , "Choose style of imperative program: 'loop' for while loop with switch over pc, 'goto' for explicit jumps."
             )
           ; ( "-java_nondet_style"
             , ArgType.String (fun s ->
                                match s with
                                | "aprove" -> java_nondet_style := Aprove
                                | "julia" -> java_nondet_style := Julia
                                | _ -> Utils.dieWith (sprintf "Do not know nondet style '%s', use aprove/julia." s))
             , "Choose implementation of nondet() in Java output. Suported options are 'aprove' and 'julia'."
             )
           ; ( "-tests"
             , ArgType.Unit (fun () -> setMode Test)
             , "Run unit tests"
             )
           ; ( "-stats"
             , ArgType.Unit (fun () -> print_stats := true)
             , "Print stats"
             )
           ; ( "-timeout"
             , ArgType.Float (fun t -> timeout := t)
             , "Timeout for the overall proof"
             )
           ;
           ]
        |> List.map (fun (name, action, help) -> new ArgInfo(name, action, help) )
