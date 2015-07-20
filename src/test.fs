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

module Microsoft.Research.T2.Test

//
// List of all unit tests across T2
//
let tests = ref ([] : (bool * (unit -> bool) * string) list)

///
/// This is set to true if we use register_testd instead of register_test.  The behavior
/// of T2 changes radically if this is set to true. We are no longer testing, but debugging
/// a test
///
let found_debug = ref false

///
/// run_tests should be called once register_test has been called on all
/// of the desired unit tests
///
let run_tests timeout  =
    printf "Running tests--------------------------------------------\n"
    printf "Using timeout of %.2f s\n" timeout

    let num = List.length !tests
    let failed = ref []
    let timeouts = ref []

    let run_test (expectedResult, testClosure, testName) =
        // This is probably not the right thing to do............
        Utils.run_clear ()

        printf "%-90s " (testName + ":")

        let start_time = System.DateTime.Now
        try
            let result = testClosure()

            if result = expectedResult then
                printf "OK after "
            else
                printf "FAIL after "
                failed := testName :: !failed;
            printf "%A\n" (System.DateTime.Now.Subtract start_time)
        with
            | :? System.TimeoutException ->
                printf "Timeout after %A!\n" (System.DateTime.Now.Subtract start_time)
                timeouts := testName :: !timeouts
            | e ->
                printf "FAIL after %A -- Got exception:\n %s" (System.DateTime.Now.Subtract start_time) (e.ToString())
                failed := testName :: !failed;


    if not !found_debug then
        List.iter run_test !tests

    printf "\n\n----------------------------------------\n\n"
    printf "TEST RESULTS: %d regressions and %d timeouts on %d tests\n" (List.length !failed) (List.length !timeouts) num

    if not(List.isEmpty !failed) then
        printf "\n--- Failures:\n"
        List.iter (fun testName -> printfn "   %s" testName) !failed

    if not(List.isEmpty !timeouts) then
        printf "\n--- Timeouts:\n"
        List.iter (fun testName -> printfn "   %s" testName) !timeouts

///
/// if "register_testd" gets called we'll shut off normal testing and just run
/// the one case we're debugging ..........this allows you to easily debug a
/// broken regression test by swapping a call to "register_test" with
/// "register_testd"
///
let register_testd s f =
    printf "Debugging.............\n"
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
let inline register_test expectedResult testName testClosure =
    tests := !tests @ [(expectedResult, testClosure, testName)]
