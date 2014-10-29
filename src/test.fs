////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      test.fs
//
//  Abstract:
//
//      Infrastructure for unit testing
//
//  Notes:
//
//      * We define register_test as an inlined function and then we use
//        .NET tricks to get the file name and line number  where the test was
//        registered.  The point of this is that you do not need to name your tests
//        they're uniquely defined by where they were registered so long as you dont use
//        register_test within a function that is re-used, or a loop.
//      * When debugging just convert register_test to register_testd on the test that's
//        failing and we execute just that test with logging turned on
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

module Test

//
// List of all unit tests across T2
//
let tests = ref ([] : (bool * (unit -> bool) * (string * int)) list)

///
/// This is set to true if we use register_testd instead of register_test.  The behavior
/// of T2 changes radically if this is set to true. We are no longer testing, but debugging
/// a test
///
let found_debug = ref false

///
/// run_tests () should be called once register_test has been called on all
/// of the desired unit tests
///
let run_tests () =
    printf "Running tests--------------------------------------------\n"
    printf "Using timeout of %.2f s\n" (!Arguments.timeout)

    let num = List.length !tests
    let failed = ref []
    let timeouts = ref []

    let run_test (stored, f, info) =
        // This is probably not the right thing to do............
        Utils.run_clear ()
        System.GC.Collect()

        let (file,line) = info

        printf "Running test %s,%d," file line
        let start_time = System.DateTime.Now

        try
            let b = f()

            if b <> stored then
                printf "Regression: %s,%d\n" file line
                if b then
                    printf "But it's good, see comment to register_test\n"
                printf "Stored = %A, Current = %A\n" stored b
                failed := (info, b, stored) :: !failed;
        with
            | :? System.TimeoutException ->
                printf "Timeout!\n"
                timeouts := info :: !timeouts
            | e ->
                printf "Regression: %s,%d\n" file line
                printf "RAISED EXCEPTION!!!!!\n"
                printf "Exception: %s\n" (e.ToString())
                failed := (info, false, stored) :: !failed;

        printf "%A\n" (System.DateTime.Now.Subtract start_time)

    if not !found_debug then
        List.iter run_test !tests

    let failed_len = List.length !failed
    let timeout_len = List.length !timeouts

    printf "\n\n----------------------------------------\n\n"
    printf "TEST RESULTS: %d regressions and %d timeouts on %d tests\n" failed_len timeout_len num

    if failed_len>0 then
        printf "\n----------------------------------------\n";
        printf "Failures:\n\n";
        let f ((file, line), b, stored) =
            printf "Regression: %s,%d\n" file line
            printf "Stored = %A, Current = %A\n\n" stored b
        List.iter f !failed

    if timeout_len > 0 then
        printf "\n----------------------------------------\n"
        printf "Timeouts:\n\n"
        let f (file, line) =
            printf "Timeout: %s,%d\n" file line
        List.iter f !timeouts

///
/// if "register_testd" gets called we'll shut off normal testing and just run
/// the one case we're debugging ..........this allows you to easily debug a
/// broken regression test by swapping a call to "register_test" with
/// "register_testd"
///
let register_testd s f =
    printf "Debugging.............\n"
    Arguments.print_log := true
    found_debug := true
    let r = f()
    printf "Expected: %b, Found: %b\n" s r

///
/// First argument is expected result.
/// Conventionally correct test should always return true.
/// If test is predictably failing for some reason (for instance,
/// some feature is not implemented), this value is set to false.
/// So if this feature eventually was implemented, it would show up
/// as regression, and thus attract developer's attention.
///
let inline register_test s f =
    let sf = new System.Diagnostics.StackFrame(true)
    let st = new System.Diagnostics.StackTrace(sf)
    let cf = st.GetFrame(0)
    let k = cf.GetFileLineNumber()
    let fn = cf.GetFileName()
    tests := !tests @ [(s, f, (fn, k))]
