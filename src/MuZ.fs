////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//    MuZg
//
//  Abstract:
//
//       Abstraction layer over safety engines implemented in of muZ.
//
// Copyright (c) Microsoft Corporation
//
// All rights reserved.g
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the ""Software""), tog
// deal in the Software without restriction, including without limitation the
// rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
// sell copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be includedg
// in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED *AS IS*, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
// THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
// FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
// DEALINGS IN THE SOFTWARE.


module Microsoft.Research.T2.MuZ

open System.Collections.Generic
open SafetyInterface
open Utils

/// Debug helper. If true, prints generated clauses on STDOUT.
let private printSMT2Horn = false

type MuZWrapper (parameters : Parameters.parameters,
                 program : Programs.Program,
                 errorLocation : int) =

    static member private GetFuncDeclForLocation (fixedPoint : Microsoft.Z3.Fixedpoint) (locationToFuncDecl : Dictionary<int, Microsoft.Z3.FuncDecl>) (predDomain : Microsoft.Z3.Sort[]) location =
        match locationToFuncDecl.TryGetValue location with
        | (true, funcDecl) -> funcDecl
        | (false, _) ->
            let predicateSymbol = sprintf "loc_%i" location
            let funcDecl = Z.z3Context.MkFuncDecl (predicateSymbol, predDomain, Z.z3Context.MkBoolSort())
            locationToFuncDecl.[location] <- funcDecl
            fixedPoint.RegisterRelation funcDecl
            if printSMT2Horn then
                printfn "(declare-rel %s (%s))" predicateSymbol (String.concat " " (predDomain |> Seq.map (fun s -> s.ToString())))
            funcDecl

    member private __.BuildProgramRepresentation () =
        /// The actual underlying fixed point object.
        let fixedPoint = Z.z3Context.MkFixedpoint ()

        // Set parameters:
        let muZParameters = Z.z3Context.MkParams()
        match parameters.safety_implementation with
        | Parameters.PDR -> muZParameters.Add("engine", Z.z3Context.MkSymbol("pdr"))
        | Parameters.Spacer -> muZParameters.Add("engine", Z.z3Context.MkSymbol("spacer"))
        | _ ->
            failwithf "Invalid muZ engine '%A' chosen. Exiting" parameters.safety_implementation
        //Turn off some preprocessor options that break traces for us:
        muZParameters.Add("xform.inline_linear", false)
        muZParameters.Add("xform.inline_eager", false)
        muZParameters.Add("datalog.subsumption", false)
        //muZParameters.Add("xform.slice", false)

        muZParameters.Add("use_heavy_mev", true)
        muZParameters.Add("pdr.flexible_trace", true)
        fixedPoint.Parameters <- muZParameters

        //Prepare bits and pieces:
        /// The program variables, in fixed order.
        let programVars : Var.var[] =
            !program.vars |> Array.ofSeq

        /// The program variables (as pre-transition version), in fixed order.
        let programPreVars : Var.var[] =
            programVars |> Array.map (fun var -> Var.prime_var var 0)

        /// The program variables (as pre-transition version) in Z3 format, in fixed order.
        let z3PreVars : Microsoft.Z3.Expr[] =
            programPreVars |> Array.map (fun var -> Z.z3Context.MkIntConst var :> Microsoft.Z3.Expr)

        /// The domain of the predicates that we introduce to represent program locations.
        let z3PredicateDomain : Microsoft.Z3.Sort[] =
            programVars |> Array.map (fun _ -> Z.z3Context.MkIntSort () :> Microsoft.Z3.Sort)

        /// Maps locations to z3 function symbols, which are predicates representing the set of states reachable at that location
        let locationToFuncDecl : Dictionary<int, Microsoft.Z3.FuncDecl> =
            Dictionary<int, Microsoft.Z3.FuncDecl>()

        /// Maps names assigned to rules we pass to z3 to indices in our program representation.
        let ruleNameToTransitionIdx : Dictionary<string, int> =
            Dictionary<string, int>()

        let declaredVariables : HashSet<Microsoft.Z3.Expr> = HashSet()
        let registerVariables (vars : Microsoft.Z3.Expr seq) =
            for v in vars do
                if declaredVariables.Add v then
                    if printSMT2Horn then
                        printfn "(declare-var %s Int)" (v.ToString())
        registerVariables z3PreVars

        //Build and insert fact for initial state:
        let startFuncDecl = MuZWrapper.GetFuncDeclForLocation fixedPoint locationToFuncDecl z3PredicateDomain !program.initial
        let initState =
            Z.z3Context.MkImplies
                (Z.z3Context.MkBool true,
                 Z.z3Context.MkApp (startFuncDecl, z3PreVars) :?> Microsoft.Z3.BoolExpr)
        if printSMT2Horn then
            printfn "(rule %A)" initState
        fixedPoint.AddRule (Z.z3Context.MkForall(z3PreVars, initState), Z.z3Context.MkSymbol "init")

        //Then, build rules for all transitions:
        for idx in !program.active do
            let (k, cmds, k') = program.transitions.[idx]
            let (pathCondition, varToPostIdx) = Symex.path_to_transitions_and_var_map [(k, cmds, k')] Map.empty
            let (_, pathCondition, _) = List.head pathCondition //One transition in, one relation out...
            let pathCondition = Formula.conj pathCondition
            let usedVars =
                Set.union (Formula.freevars pathCondition) (Set.ofSeq programPreVars)
                |> Array.ofSeq |> Array.map (fun var -> Z.z3Context.MkIntConst var :> Microsoft.Z3.Expr)
            registerVariables usedVars

            let preFuncDecl = MuZWrapper.GetFuncDeclForLocation fixedPoint locationToFuncDecl z3PredicateDomain k
            let preState = Z.z3Context.MkApp (preFuncDecl, z3PreVars) :?> Microsoft.Z3.BoolExpr

            let postFuncDecl = MuZWrapper.GetFuncDeclForLocation fixedPoint locationToFuncDecl z3PredicateDomain k'
            let postVars = programVars |> Array.map (fun var -> Z.z3Context.MkIntConst (Var.prime_var var (Map.findWithDefault var 0 varToPostIdx)) :> Microsoft.Z3.Expr)
            let postState = Z.z3Context.MkApp (postFuncDecl, postVars) :?> Microsoft.Z3.BoolExpr

            let transitionCondition = Z.z3Context.MkImplies (Z.z3Context.MkAnd (preState, Formula.z3 pathCondition), postState)
            if printSMT2Horn then
                printfn "(rule %A)" transitionCondition
            let ruleName = sprintf "trans_%i" idx
            fixedPoint.AddRule (Z.z3Context.MkForall(usedVars, transitionCondition), Z.z3Context.MkSymbol ruleName)
            ruleNameToTransitionIdx.[ruleName] <- idx

        //Finally, build the query:
        let errorFuncDecl = MuZWrapper.GetFuncDeclForLocation fixedPoint locationToFuncDecl z3PredicateDomain errorLocation
        let errorQuery = Z.z3Context.MkApp(errorFuncDecl, z3PreVars) :?> Microsoft.Z3.BoolExpr
        if printSMT2Horn then
            printfn "(query %A)" errorQuery

        (fixedPoint, Z.z3Context.MkExists (z3PreVars, errorQuery), ruleNameToTransitionIdx)

    interface SafetyProver with
        member self.ErrorLocationReachable () =
            Log.log parameters "Building muZ program representation"
            Stats.startTimer "muZ-ClauseConstruction"
            let (fixedPoint, errorQuery, ruleNameToTransitionIdx) = self.BuildProgramRepresentation()
            Stats.endTimer "muZ-ClauseConstruction"
            Log.log parameters "Querying muZ for safety ..."

            Stats.startTimer "muZ-Query"
            let queryResult =
                try
                    fixedPoint.Query errorQuery
                finally
                    Stats.endTimer "muZ-Query"

            match queryResult with
            | Microsoft.Z3.Status.SATISFIABLE ->
                Log.log parameters "... found counterexample"
                let rulesInTrace = fixedPoint.GetRuleNamesAlongTrace()

                //Now translate into our format, from the back to get the trace in the right order:
                let mutable resultTrace = []
                Log.debug parameters "Returned counterexample, last step first:"
                for i in 0 .. rulesInTrace.Length - 1 do
                    let curRuleName = (rulesInTrace.[i] :?> Microsoft.Z3.StringSymbol).String
                    Log.debug parameters ("  " + curRuleName)
                    if curRuleName <> "init" then
                        if curRuleName <> "<null>" then //Skip unnamed rules and the initial transition
                            let transitionIdx = ruleNameToTransitionIdx.[curRuleName]
                            let (k, cmds, k') = program.transitions.[transitionIdx]
                            if cmds.IsEmpty then
                                //This case is important, otherwise we "skip" the transition in the returned CEx, and it looks like there is a gap in the path.
                                resultTrace <- (k, Programs.assume Formula.truec, k') :: resultTrace
                            else
                                for cmd in List.rev cmds do
                                    resultTrace <- (k, cmd, k') :: resultTrace
                        else
                            Log.log parameters <| sprintf "Cannot translate transition in muZ counterexample to our representation."

                fixedPoint.Dispose()
                Some resultTrace
            | _ ->
                Log.log parameters <| "... program is safe"
                fixedPoint.Dispose()
                None
        member __.DeleteProgramTransition _ = ()
        member __.ResetFrom _ = ()