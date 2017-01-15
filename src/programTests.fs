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
            
    let t2_run_temporal parameters prover input_file ctl_formula_string fairness_constraint expected_result =
        if System.IO.File.Exists input_file then
            let ctl_formula = CTL_Parser.parse_CTL ctl_formula_string
            let (p, _) = Input.load_t2 parameters true input_file
            match prover p ctl_formula fairness_constraint with
            | Some (result, _) when (Some result) = expected_result -> true //project away the proof
            | None when None = expected_result -> true
            | _ -> false
        else
            sprintf "Couldn't open file %s\n" input_file |> failwith

    let t2_run_CTLStar parameters prover input_file ctlstar_formula_string expected_result=
        if System.IO.File.Exists input_file then
            let ctlstar_formula = CTL_Parser.parse_CTLStar ctlstar_formula_string
            let (p, _) = Input.load_t2 parameters true input_file
            match prover p ctlstar_formula with
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

    let termination_prover p = Termination.bottomUpProver term_pars p ((CTL.AF(CTL.Atom(Formula.falsec)))) true None
    let inline register_term_test file =
        Test.register_test true (termTestName file None) (fun () -> t2_run_termination term_pars termination_prover file (Some true))
    let inline register_term_testd file =
        Test.register_testd true (fun () -> t2_run_termination term_pars termination_prover file (Some true))
    let inline register_nonterm_test file =
        Test.register_test true (termTestName file None) (fun () -> t2_run_termination term_pars termination_prover file (Some false))
    let inline register_nonterm_testd file =
        Test.register_testd true (fun () -> t2_run_termination term_pars termination_prover file (Some false))

    let parse_fairness_constraint (s : string option) =
        match s with
        | None -> None
        | Some s ->
        let lexbuf = Microsoft.FSharp.Text.Lexing.LexBuffer<byte>.FromBytes (System.Text.Encoding.ASCII.GetBytes s)
        Some (Absparse.Fairness_constraint Absflex.token lexbuf)
    let bottomUp_prover p actl_fmla fairness_constraint = Termination.bottomUpProver ctl_pars p actl_fmla false fairness_constraint
    let CTLStar_prover p ctls_fmla = Termination.CTLStar_Prover ctl_pars p ctls_fmla false
    
    let inline register_CTL_SAT_test file property fairness_constraint =
        Test.register_test true (ctlTestName file property fairness_constraint) (fun () -> t2_run_temporal ctl_pars bottomUp_prover file property (parse_fairness_constraint fairness_constraint) (Some true))
    let inline register_CTL_SAT_testd file property fairness_constraint =
        Test.register_testd true (fun () -> t2_run_temporal ctl_pars bottomUp_prover file property (parse_fairness_constraint fairness_constraint) (Some true))
    let inline register_CTL_UNSAT_test file property fairness_constraint =
        Test.register_test true (ctlTestName file property fairness_constraint) (fun () -> t2_run_temporal ctl_pars bottomUp_prover file property (parse_fairness_constraint fairness_constraint) (Some false))
    let inline register_CTL_UNSAT_testd file property fairness_constraint =
        Test.register_testd true (fun () -> t2_run_temporal ctl_pars bottomUp_prover file property (parse_fairness_constraint fairness_constraint) (Some false))
    let inline register_CTL_FAIL_test file property fairness_constraint =
        Test.register_test true (ctlTestName file property fairness_constraint) (fun () -> t2_run_temporal ctl_pars bottomUp_prover file property (parse_fairness_constraint fairness_constraint) None)
    let inline register_CTL_FAIL_testd file property fairness_constraint =
        Test.register_testd true (fun () -> t2_run_temporal ctl_pars bottomUp_prover file property (parse_fairness_constraint fairness_constraint) None)
    let inline register_CTLStar_SAT_test file property =
        Test.register_test true (ctlStarTestName file property) (fun () -> t2_run_CTLStar ctl_pars CTLStar_prover file property (Some true))    
    let inline register_CTLStar_SAT_testd file property =
        Test.register_testd true (fun () -> t2_run_CTLStar ctl_pars CTLStar_prover file property (Some true))    
    let inline register_CTLStar_UNSAT_test file property =
        Test.register_test true (ctlStarTestName file property) (fun () -> t2_run_CTLStar ctl_pars CTLStar_prover file property (Some false))
    let inline register_CTLStar_UNSAT_testd file property =
        Test.register_testd true (fun () -> t2_run_CTLStar ctl_pars CTLStar_prover file property (Some false))  
    let inline register_CTLStar_FAIL_test file property =
        Test.register_test true (ctlStarTestName file property) (fun () -> t2_run_CTLStar ctl_pars CTLStar_prover file property None)
    let inline register_CTLStar_FAIL_testd file property =
        Test.register_testd true (fun () -> t2_run_CTLStar ctl_pars CTLStar_prover file property None)


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
    if pars.lexicographic || pars.lex_term_proof_first then
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
    if pars.polyrank && pars.lexicographic then
        register_term_test "testsuite/polyrank1.t2"
        register_term_test "testsuite/polyrank2.t2"
        register_term_test "testsuite/polyrank3.t2"
        register_term_test "testsuite/polyrank4.t2"
        register_term_test "testsuite/polyrank5.t2"
        register_term_test "testsuite/polyrank6.t2"

    //Regression tests for reported bugs in (non)termination:
    register_term_test "regression/Stockholm_true-termination.t2"

    //Heidy's basic Temporal Properties examples, some termination
    (*register_CTL_SAT_test   "testsuite/heidy1.t2" "[AG] (x_1 >= y_1)" None
    register_CTL_UNSAT_test "testsuite/heidy2.t2" "[AG] (x_1 > 1)" None
    register_CTL_SAT_test   "testsuite/heidy9.t2" "[AF] (p > 0)" None
    register_CTL_UNSAT_test "testsuite/heidy3.t2" "[AF] (p > 0)" None
    register_CTL_SAT_test   "testsuite/heidy5.t2" "[AG]([AF] (p > 0))" None
    register_CTL_UNSAT_test "testsuite/heidy6.t2" "[AG]([AF] (p > 0))" None
    register_CTL_SAT_test "testsuite/heidy7.t2" "[AF]([AG] (p > 0))" None
    register_CTL_UNSAT_test "testsuite/heidy8.t2" "[AF]([AG] (p > 0))" None
    register_CTL_UNSAT_test "testsuite/test_byron_2.t2" "[AF]([AG] (x > 0))" None

    register_CTL_UNSAT_test "ax_test.t2" "[AG](p > 0 || [AF]([AX](p <= 0)))" None
    register_CTL_UNSAT_test "ax_test.t2" "[AG](p > 0 || [AF]([EX](p <= 0)))" None
    register_CTL_SAT_test   "ax_test.t2" "[AG](p > 0 || [AF](p <= 0))" None
    register_CTL_SAT_test   "ax_test_2.t2" "[AG](p > 0 || [AF]([AX](p <= 0)))" None
    //TODO: Fix X bug. 
    //register_CTL_SAT_test   "ax_test_2.t2" "[EG](p > 0 || [EF]([EX](p <= 0)))" None

    register_CTL_SAT_test   "ax_test_2.t2" "[AG](p <= 0 || [AX](p <= 0))" None
    register_CTL_SAT_test   "ax_test_2.t2" "[AG](p <= 0 || [EX](p <= 0))" None

    register_CTL_SAT_test   "ax_test_3.t2" "[AG](p <= 0 || [EX](p <= 0))" None
    register_CTL_UNSAT_test "ax_test_3.t2" "[AG](p <= 0 || [AX](p <= 0))" None
    register_CTL_SAT_test   "ax_test.t2" "[AX](p <= 0)" None
    register_CTL_SAT_test   "ax_test.t2" "[EX](p <= 0)" None*)

    /////////////////////////////////////////////////////////////////////////////////////////////
    register_CTL_SAT_test "bakery.t2" "[AG](NONCRITICAL <= 0 || ([AF](CRITICAL > 0)))" (Some "(P == 1, Q == 1)")
    register_CTL_UNSAT_test "bakerybug.t2" "[AG](NONCRITICAL <= 0 || ([AF](CRITICAL > 0)))" (Some "(P == 1, Q == 1)")
    register_CTL_SAT_test "ppblock.t2" "[AG](PPBlockInits <= 0 || ([AF](PPBunlockInits > 0)))" (Some "(IoCreateDevice == 1, status == 1)")   
    register_CTL_FAIL_test "ppblockbug.t2" "[AG](PPBlockInits <= 0 || ([AF](PPBunlockInits > 0)))" (Some "(IoCreateDevice == 1, status == 1)")
    

    register_CTL_SAT_test "cav13-ctl-examples/P1.t2" "[AG](varA != 1 || [AF](varR == 1))" None 
    register_CTL_SAT_test "cav13-ctl-examples/P2.t2" "[EF](varA == 1 && [EG](varR != 5))" None
    register_CTL_SAT_test "cav13-ctl-examples/P3.t2" "[AG](varA != 1 || [EF](varR == 1))" None
    register_CTL_SAT_test "cav13-ctl-examples/P4.t2" "[EF](varA == 1 && [AG](varR != 1))" None
    register_CTL_SAT_test "cav13-ctl-examples/P5.t2" "[AG](varS != 1 || [AF](varU == 1))" None
    register_CTL_SAT_test "cav13-ctl-examples/P6.t2" "[EF](varS == 1 || [EG](varU != 1))" None
    register_CTL_SAT_test "cav13-ctl-examples/P7.t2" "[AG](varS != 1 || [EF](varU == 1))" None
    register_CTL_SAT_test "cav13-ctl-examples/P8.t2" "[EF](varS == 1 && [AG](varU != 1))" None
    register_CTL_SAT_test "cav13-ctl-examples/P9.t2" "[AG](varA != 1 || [AF](varR == 1))" None
    register_CTL_SAT_test "cav13-ctl-examples/P10.t2" "[EF](varA == 1 && [EG](varR != 1))" None
    register_CTL_SAT_test "cav13-ctl-examples/P11.t2" "[AG](varA != 1 || [EF](varR == 1))" None
    register_CTL_SAT_test "cav13-ctl-examples/P12.t2" "[EF](varA == 1 && [AG](varR != 1))" None
    register_CTL_SAT_test "cav13-ctl-examples/P13.t2" "[EG](varP1 != 1) || [EG](varP2 != 1)" None
    register_CTL_SAT_test "cav13-ctl-examples/P14.t2" "[EG](varP1 != 1) || [EG](varP2 != 1)" None
    register_CTL_SAT_test "cav13-ctl-examples/P15.t2" "[EF](varP1 == 1) && [EF](varP2 == 1)" None
    register_CTL_SAT_test "cav13-ctl-examples/P16.t2" "[AG](varP1 != 1) || [AG](varP2 != 1)" None
    register_CTL_SAT_test "cav13-ctl-examples/P17.t2" "[AG]([AF](varW >= 1))" None
    register_CTL_SAT_test "cav13-ctl-examples/P18.t2" "[EF]([EG](varW < 1))" None
    register_CTL_SAT_test "cav13-ctl-examples/P19.t2" "[AG]([EF](varW >=1))" None
    register_CTL_SAT_test "cav13-ctl-examples/P20.t2" "[EF]([AG](varW < 1))" None
    register_CTL_SAT_test "cav13-ctl-examples/P21.t2" "[AG]([AF](varW == 1))" None
    register_CTL_SAT_test "cav13-ctl-examples/P22.t2" "[EF]([EG](varW != 1))" None
    register_CTL_SAT_test "cav13-ctl-examples/P23.t2" "[AG]([EF](varW == 1))" None
    register_CTL_SAT_test "cav13-ctl-examples/P24.t2" "[EF]([AG](varW != 1))" None
    register_CTL_SAT_test "cav13-ctl-examples/P25.t2" "(varC <= 5) || ([AF](varR > 5))" None
    register_CTL_UNSAT_test "cav13-ctl-examples/P26.t2" "(varC > 5) && [EG](varR <= 5)" None
    register_CTL_UNSAT_test "cav13-ctl-examples/P27.t2" "(varC <= 5) || [EF](varR > 5)" None
    register_CTL_UNSAT_test "cav13-ctl-examples/P28.t2" "(varC > 5) && [AG](varR <= 5)" None

    //Timeouts for CTL* are commented out. If known why a comment is left above.
    register_CTLStar_UNSAT_test "1394complete-succeed-2.t2" "A G((E G(phi_io_compl <= 0)) || (E F(G (phi_nSUC_ret > 0))))"
    register_CTLStar_SAT_test "1394complete-succeed-2.t2" "E F((A F(phi_io_compl > 0)) && (A G(F (phi_nSUC_ret <= 0))))"
    register_CTLStar_SAT_test "1394-succeed-2.t2" "E F(G (((keA <= 0) && (A G (keR == 0)))))" //
    register_CTLStar_SAT_test "1394-succeed-2.t2" "E F(G (((keA <= 0) || (E F (keR == 1)))))"  //

    register_CTLStar_SAT_test "ppblock.t2" "E F(PPBlockInits > 0  && ( ( (E F(G (IoCreateDevice != 1))) || (A G( F(status == 1))) ) && (E G(PPBunlockInits <= 0)) ) )" 
    //Program is about 110 - 400 lines of code.   

    //CTL* Toy examples - About 10-15 lines of code

    register_CTLStar_SAT_test "testsuite/ctlstar_5.t2" "E F(G ((x == 1) && (E G(y == 0))))"
    register_CTLStar_SAT_test "testsuite/ctlstar_3.t2" "E G(F (x == 1))"
    
    register_CTLStar_SAT_test "testsuite/ctlstar.t2" "E F(G (x == 1))"
    register_CTLStar_UNSAT_test "testsuite/example9.t2" "A G( (E F(G (y = 1))) && (E F(x >= t)))"//

    //Z3 Out of memory exception for program below 
    //register_CTLStar_SAT_test "testsuite/ctlstar_4.t2" "A G(F(b == 0)) && (W(x == 0),(b == 0))"
    register_CTLStar_UNSAT_test "testsuite/example10.t2" "A G( (E F (G (x = 0))) && (E F(x = 20)))"
    register_CTLStar_UNSAT_test "ctlstar_test.t2" "(E F(G (x == 0))) && (E F(G (x == 1)))"
    register_CTLStar_SAT_test "ctlstar_test.t2" "A G ((A F(G (x == 0))) || (A F(G (x == 1))))"

    //Small bug to be fixed for stand alone AF. A corner case essentially. 
   // register_CTL_SAT_test "1394complete-succeed.t2" "([AF](phi_io_compl <= 0)) || ([AF](phi_nSUC_ret <= 0))" None 
   
   
   //A transformation is cutting off nodes for this particular example. Issue currently being worked on. 
   // register_CTLStar_UNSAT_test "testsuite/ctlstar.t2" "E F(G (x == 0))"
    
