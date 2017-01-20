////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      ProgramTests
//
//  Abstract:
//
//      Testing program verification tools
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


module Microsoft.Research.T2.ProgramTests

let register_tests (pars : Parameters.parameters) =
    let safety_pars = pars
    let term_pars = pars
    let ctl_pars = pars

    // Utilities for the different types of tests -----------------------------
    let termTestName filename fairnessCond =
        match fairnessCond with
        | Some fairCond ->
            sprintf "Fair termination test %s [fair '%s']" filename fairCond
        | None ->
            sprintf "Termination test %s" filename

    let safetyTestName filename loc =
        sprintf "Safety test %s [loc %i]" filename loc

    let ctlStarTestName filename ctlStarProperty =
        sprintf "CTL* test %s [prop '%s']"filename ctlStarProperty

    let ctlTestName filename ctlProperty fairnessCond =
        match fairnessCond with
        | Some fairCond ->
            sprintf "Fair CTL test %s [prop '%s', fair '%s']" filename ctlProperty fairCond
        | None ->
            sprintf "CTL test %s [prop '%s']" filename ctlProperty

    let t2_run_loc parameters prover s =
        if System.IO.File.Exists s then
            let (p,loc) = Input.load_t2 parameters true s
            prover p loc
        else
            sprintf "Couldn't open file %s\n" s |> failwith

    let t2_run_termination parameters prover input_file expected_result =
        if System.IO.File.Exists input_file then
            let (p, _) = Input.load_t2 parameters false input_file
            match prover p with
            | Some (result, _) when (Some result) = expected_result -> true //project away the proof
            | None when None = expected_result -> true
            | _ -> false
        else
            sprintf "Couldn't open file %s\n" input_file |> failwith
            
    let safety_prover p l =
        match Safety.prover safety_pars p l with
        | Some(_) -> false
        | None -> true
    let inline register_safety_test file =
        Test.register_test true (safetyTestName file 10000) (fun () -> t2_run_loc safety_pars safety_prover file)
    let inline register_safety_testd file =
        Test.register_testd true (fun () -> t2_run_loc safety_pars safety_prover file)
    let inline register_unsafety_test file =
        Test.register_test true (safetyTestName file 10000) (fun () -> t2_run_loc safety_pars safety_prover file |> not)
    let inline register_unsafety_testd file =
        Test.register_testd true (fun () -> t2_run_loc safety_pars safety_prover file |> not)

    let termination_prover p = Termination.bottomUpProver term_pars p 
    let inline register_term_test file =
        Test.register_test true (termTestName file None) (fun () -> t2_run_termination term_pars termination_prover file (Some true))
    let inline register_term_testd file =
        Test.register_testd true (fun () -> t2_run_termination term_pars termination_prover file (Some true))
    let inline register_nonterm_test file =
        Test.register_test true (termTestName file None) (fun () -> t2_run_termination term_pars termination_prover file (Some false))
    let inline register_nonterm_testd file =
        Test.register_testd true (fun () -> t2_run_termination term_pars termination_prover file (Some false))

    // Small, manually crafted examples ---------------------------------------------------
    register_term_test "testsuite/small01.t2"
    register_safety_test "testsuite/small02.t2"
    register_safety_test "testsuite/small03.t2"
    register_safety_test "testsuite/small04.t2"
    register_safety_test "testsuite/small05.t2"
    register_safety_test "testsuite/small06.t2"
    register_unsafety_test "testsuite/small07.t2"
    register_safety_test "testsuite/small08.t2"
    register_safety_test "testsuite/small09.t2"
    register_term_test "testsuite/small12.t2"
    register_term_test "testsuite/small13.t2"
    register_unsafety_test "testsuite/small14.t2"
    register_term_test "testsuite/small19.t2"
    register_term_test "testsuite/small20.t2"
    register_term_test "testsuite/small21.t2"
    register_safety_test "testsuite/small24.t2"
    register_unsafety_test "testsuite/small25.t2"

    register_term_test "testsuite/small26.t2"
    register_term_test "testsuite/small27.t2"
    register_term_test "testsuite/small28.t2"
    register_unsafety_test "testsuite/small30.t2"
    register_term_test "testsuite/small31.t2"
    register_safety_test "testsuite/small31.t2"
    register_term_test "testsuite/small32.t2"
    register_safety_test "testsuite/small32.t2"
    register_term_test "testsuite/small33.t2"
    register_safety_test "testsuite/small33.t2"
    register_term_test "testsuite/small34.t2"

    register_term_test "testsuite/p-4.t2"

    register_term_test "testsuite/disj_nightmare.t2"

    register_term_test "testsuite/create.t2"

    register_term_test "testsuite/create_seg.t2"
    register_term_test "testsuite/create_via_tmps.t2"
    register_term_test "testsuite/destroy.t2"
    register_term_test "testsuite/destroy_seg.t2"
    register_term_test "testsuite/print.t2"
    register_term_test "testsuite/reverse.t2"
    register_term_test "testsuite/reverse_seg_cyclic.t2"
    register_term_test "testsuite/traverse.t2"
    register_term_test "testsuite/traverse2.t2"
    register_term_test "testsuite/traverse_seg.t2"
    register_term_test "testsuite/traverse_seg2.t2"
    register_term_test "testsuite/traverse_twice.t2"
    if pars.lex_term_proof_first then
        register_term_test "testsuite/nested2.t2"

    //
    // These examples come from an early C---T2 translater based on SLAyer, where
    // files named p-*.c were intended to terminate.  Some of the translations
    // are broken, and others have been modified since being constructed, so the
    // original C files only give some guidence as to the meaning of the .t2 files
    //
    register_term_test "testsuite/p-12.t2"
    register_term_test "testsuite/p-13.t2"
    register_term_test "testsuite/p-14.t2"
    register_term_test "testsuite/p-15.t2"
    register_term_test "testsuite/p-16.t2"
    register_term_test "testsuite/p-18.t2"
    register_term_test "testsuite/p-1b.t2"
    register_term_test "testsuite/p-1d.t2"
    register_term_test "testsuite/p-21.t2"
    register_term_test "testsuite/p-22.t2"
    register_term_test "testsuite/p-3.t2"
    register_term_test "testsuite/p-37.t2"

    register_term_test "testsuite/p-40.t2"
    register_term_test "testsuite/p-41.t2"
    register_term_test "testsuite/p-42.t2"
    register_term_test "testsuite/p-43.t2"
    register_term_test "testsuite/p-44.t2"
    register_term_test "testsuite/p-49.t2"
    register_term_test "testsuite/p-53.t2"
    register_term_test "testsuite/p-55.t2"
    register_term_test "testsuite/p-56.t2"
    register_term_test "testsuite/p-58.t2"
    register_term_test "testsuite/p-6.t2"
    register_term_test "testsuite/p-60.t2"
    register_term_test "testsuite/p-61.t2"
    register_term_test "testsuite/p-63.t2"
    register_term_test "testsuite/p-7.t2"
    register_term_test "testsuite/p-7b.t2"
    register_term_test "testsuite/p-45.t2"

    register_term_test "testsuite/byron-1.t2"
    register_term_test "testsuite/iecs.t2"

    register_term_test "testsuite/byron-2.t2"
    register_term_test "testsuite/fun2.t2"

    register_term_test "testsuite/huh.t2"
    register_term_test "testsuite/fun4.t2"
    register_term_test "testsuite/seq.t2"
    register_term_test "testsuite/seq2.t2"
    
    register_safety_test "testsuite/small35.t2"

    register_term_test "testsuite/s1-saved.t2"
    
    register_term_test "testsuite/consts1.t2"
    register_term_test "testsuite/consts2.t2"
    register_term_test "testsuite/consts3.t2"
    register_term_test "testsuite/consts4.t2"
    register_term_test "testsuite/consts5.t2"
   

    register_safety_test "testsuite/eric3.t2"
    register_safety_test "testsuite/unsat.t2"
    register_safety_test "testsuite/curious2.t2"
    register_safety_test "testsuite/db.t2"

    //Abi's Polyranking examples. They will only pass if Arguments.polyrank and Arguments.lexicographic are on
    if pars.polyrank then
        register_term_test "testsuite/polyrank1.t2"
        register_term_test "testsuite/polyrank2.t2"
        register_term_test "testsuite/polyrank3.t2"
        register_term_test "testsuite/polyrank4.t2"
        register_term_test "testsuite/polyrank5.t2"
        register_term_test "testsuite/polyrank6.t2"

    //Regression tests for reported bugs in (non)termination:
    register_term_test "regression/Stockholm_true-termination.t2"