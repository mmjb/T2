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

module Microsoft.Research.T2.Parameters

type numAbsDomain = Box | Octagon
type outputFormat =
    | Dot
    | Java
    | C
    | HSF
    | SMTPushdown
type imperativeProgramStyle = Loop | Goto
type javaNondetStyle = Aprove | Julia
type SafetyImplementation = Impact | PDR | Spacer | SpacerBMC

type parameters = {
    /// Time when T2 execution began
    start_time : System.DateTime

    /// Overall timeout per program (in seconds):
    mutable timeout : float

    /// Print ranking functions / recurrence sets to stdout after the proof?
    mutable print_proof : bool

    /// Print some statistics about our efforts, after finishing
    mutable print_stats : bool

    // ---------------------------- Logging things ----------------------------
    /// Set to true to enable verbose logging spew from across T2
    mutable print_log : bool

    /// Set to true to enable verbose debug logging spew from across T2
    mutable print_debug : bool

    // ---------------------------- Program things ----------------------------
    /// Symbolic abstraction: change constants in the program from 5 to var5.  Constraints are added
    /// so that var5<var6,etc. This is needed because otherwise, the reachability graph is unwound
    /// (i.e., the program is executed!) until actually reaching the constants. Not so bad for 5, but
    /// very bad for 1000.
    mutable elim_constants : bool

    /// Perform numerical abstr. interpretation if we have less than !do_ai_threshold transitions
    mutable do_ai_threshold : int
    /// This is flipped to true if we performed AI and enables further optimizations later on
    mutable did_ai_first : bool

    /// Choice of numerical domain for abstract interpretation
    mutable ai_domain : numAbsDomain

    // ---------------------------- Termination things ----------------------------
    /// Try proving non-termination as well as termination?
    mutable prove_nonterm : bool

    /// If lexicographic fails, try detecting initial condition?
    mutable init_cond : bool

    /// If lexicographic fails, try unrolling a bit?
    mutable unrolling : bool
    mutable unrolling_limit : int

    /// Try to find lexicographic rank functions for all cutpoints
    mutable lexicographic : bool

    ///Try to find lexicographic RFs of shorter length?
    ///Don't have this on at the same time as max_unaffect
    mutable lex_opt_fewer_rfs : bool

    ///Try to find lexicographic RFs s.t. the relations affect each other's RFs as little as possible?
    ///Don't have this on at the same time as fewer_rfs
    mutable lex_opt_max_unaffect : bool

    /// Try to find a rf such that the considered relation is strictly decreasing and bounded and all SCC transitions are weakly decreasing
    mutable lex_opt_scc_unaffected : bool

    /// Start looking for polyranking lexicographic rank functions in the event of failure with lexicographic RFs. Does nothing if lexicographic isn't on.
    mutable polyrank : bool
    mutable polyrank_max_depth : int

    /// Try lexicographic termination proofs with program simplifications before starting safety proof?
    mutable lex_term_proof_first : bool

    /// Should we use bounded/decreasing split from Lemma 31 in "SAT-Based Termination Analysis Using Monotonicity Constraints over the Integers" (TPLP)
    mutable mcnp_style_bound_decr : bool

    // ---------------------------- Reachability things ----------------------------
    /// Type of used safety prover.
    mutable safety_implementation : SafetyImplementation


    /// Generate DOT graphs of the impact tree (at each step)
    mutable dottify_reachability : bool
    /// Generate DOT graphs of the input program
    mutable dottify_input_pgms : bool
    /// Check sanity of Impact graphs
    mutable sanity_checking : bool

    /// Produce safety counterexamples
    mutable safety_counterexample : bool

    /// Use path from root when doing force-cover
    mutable fc_look_back : bool
    /// When trying force-cover v by w fails, remove w from the candidates of v
    mutable fc_remove_on_fail : bool
    /// Use UNSAT core to reduce interpolation constraints
    mutable fc_unsat_core : bool

    /// Do iterative reachability proving, where only a part of the graph needs to be recomputed after changes:
    mutable iterative_reachability : bool

    /// Chain transitions that connect via unlabeled nodes.
    mutable chaining : bool

    // ---------------------------- Interpolation things ----------------------------
    /// Print interpolants found
    mutable print_interpolants : bool
    /// Double check interpolants found
    mutable check_interpolants : bool

    /// Try to ignore constraints from the beginning
    mutable seq_interpolation_ignore_last_constr : bool

    /// Do efficient sequential interpolation (generating all interpolants for a path in one go) instead of standard interpolation
    mutable seq_interpolation : bool

    // ---------------------------- Counterexample things ----------------------------
    /// When testing we dont want to create a billion defect files, so we
    /// can shut this option off by setting create_defect_files to false
    mutable create_defect_files : bool
}

let defaultParameters =
    {
        start_time = System.DateTime.Now
        timeout = 300.0
        print_proof = false
        print_stats = true

        print_log = false
        print_debug = false

        elim_constants = true
        do_ai_threshold = 50
        did_ai_first = false
        ai_domain = Box

        prove_nonterm = true
        init_cond = false
        unrolling = true
        unrolling_limit = 3
        lexicographic = true
        lex_opt_fewer_rfs = false
        lex_opt_max_unaffect = false
        lex_opt_scc_unaffected = false
        polyrank = true
        polyrank_max_depth = 4
        lex_term_proof_first = true
        mcnp_style_bound_decr = false

        safety_implementation = Spacer
        dottify_reachability = false
        dottify_input_pgms = false
        sanity_checking = true
        safety_counterexample = false
        fc_look_back = false
        fc_remove_on_fail = false
        fc_unsat_core = false
        iterative_reachability = true
        chaining = true 

        print_interpolants = false
        check_interpolants = true
        seq_interpolation_ignore_last_constr = true
        seq_interpolation = true

        create_defect_files = true
    }
