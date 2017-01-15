////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//     Safety
//
//  Abstract:
//
//       Interface to safety component in T2.
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


module Microsoft.Research.T2.Safety
open SafetyInterface

let GetProver (parameters : Parameters.parameters) (program : Programs.Program) (errorLocation : int) : SafetyProver =
    match parameters.safety_implementation with
    | Parameters.Impact ->
        Impact.ImpactARG(parameters, program, errorLocation) :> _
    | _ ->
        MuZ.MuZWrapper(parameters, program, errorLocation) :> _

 /// Prove that location err is unreachable in p
let prover (pars : Parameters.parameters) (program : Programs.Program) err =
    Utils.timeout pars.timeout

    // Create new initial location with transition assume(_const_100 > _const_32) for all
    // abstracted const variables.
    program.AddSymbolConstantInformation()

    // The connection between programs and Graph is a little bit messy
    // at the moment. We have to marshal a little bit of data between them
    let safetyImplementation = GetProver pars program err

    if pars.dottify_input_pgms then
        Output.print_dot_program program "input.dot"

    // Try to disprove/prove the error location in abs to be unreachable
    let r = safetyImplementation.ErrorLocationReachable ()

    // If the flag is set, produce a counterexample file
    if pars.safety_counterexample && r.IsSome then
        let stem = Some (List.map (fun (x,y,z) -> (x,[y],z)) r.Value)
        let cex = Counterexample.make stem None
        Counterexample.print_defect pars [cex] "defect.tt"
        Counterexample.print_program pars [cex] "defect.t2"
        Utils.run_clear()

    if pars.export_cert.IsSome then
        if r.IsNone then
            let impactARG = safetyImplementation :?> Impact.ImpactARG
            use streamWriter = new System.IO.StreamWriter (pars.export_cert.Value)
            use xmlWriter = new System.Xml.XmlTextWriter (streamWriter)
            xmlWriter.Formatting <- System.Xml.Formatting.Indented

            xmlWriter.WriteStartElement "safetyProblem"
            
            xmlWriter.WriteStartElement "safetyProgram"
            program.ToCeta xmlWriter "program" None false
            xmlWriter.WriteStartElement "error"
            Programs.exportLocation xmlWriter (Programs.OriginalLocation err)
            xmlWriter.WriteEndElement () //end errror 
            xmlWriter.WriteEndElement () //end safetyProgram

            xmlWriter.WriteStartElement "safetyProof"
            impactARG.ToCeta xmlWriter None None false
            xmlWriter.WriteEndElement () //end safetyProof

            xmlWriter.WriteEndElement () //end safetyProblem

        else
            failwith "Export of safety counterexamples not supported yet."

    Utils.reset_timeout()

    r