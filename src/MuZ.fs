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
open System.Threading.Tasks;

open SafetyInterface
open Utils

/// Debug helper. If true, prints generated clauses on STDOUT.
let private printSMT2Horn = false

type MuZWrapper (parameters : Parameters.parameters,
                 program : Programs.Program,
                 errorLocation : int) =

    member private __.BuildProgramRepresentation () =
        //Prepare bits and pieces:
        /// The program variables, in fixed order.
        let programVars : Var.var[] =
            program.Variables |> Array.ofSeq

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

        let buildRule (variables : Microsoft.Z3.Expr[]) (transitionCondition : Microsoft.Z3.BoolExpr) =
            let variables =
                if variables.Length = 0 then
                    [| Z.z3Context.MkIntConst "__makeItLookLessEmptyVar" :> Microsoft.Z3.Expr |]
                else
                    variables
            if printSMT2Horn then
                printfn "Prevars: %s" (String.concat ", " (variables |> Seq.map (fun v -> v.ToString())))
                printfn "(rule %A)" transitionCondition
            Z.z3Context.MkForall(variables, transitionCondition)

        let getFuncDeclForLocation location =
            match locationToFuncDecl.TryGetValue location with
            | (true, funcDecl) -> funcDecl
            | (false, _) ->
                let predicateSymbol = sprintf "loc_%i" location
                let funcDecl = Z.z3Context.MkFuncDecl (predicateSymbol, z3PredicateDomain, Z.z3Context.MkBoolSort())
                locationToFuncDecl.[location] <- funcDecl
                if printSMT2Horn then
                    printfn "(declare-rel %s (%s))" (funcDecl.Name.ToString()) (String.concat " " (z3PredicateDomain |> Seq.map (fun s -> s.ToString())))
                funcDecl

        /// Maps names assigned to rules we pass to z3 to indices in our program representation.
        let ruleNameToTransition = Dictionary()

        let declaredVariables : HashSet<Microsoft.Z3.Expr> = HashSet()
        let registerVariables (vars : Microsoft.Z3.Expr seq) =
            for v in vars do
                if declaredVariables.Add v then
                    if printSMT2Horn then
                        printfn "(declare-var %s Int)" (v.ToString())
        registerVariables z3PreVars

        //Build and insert fact for initial state:
        let startFuncDecl = getFuncDeclForLocation program.Initial
        let mutable rules = []
        let initState =
            Z.z3Context.MkImplies
                (Z.z3Context.MkBool true,
                 Z.z3Context.MkApp (startFuncDecl, z3PreVars) :?> Microsoft.Z3.BoolExpr)
        rules <- (buildRule z3PreVars initState, Z.z3Context.MkSymbol "init") :: rules

        //Then, build rules for all transitions:
        for (idx, (k, cmds, k')) in program.TransitionsWithIdx do
            let (pathCondition, varToPostIdx) = Symex.path_to_transitions_and_var_map [(k, cmds, k')] Map.empty
            let (_, pathCondition, _) = List.head pathCondition //One transition in, one relation out...
            let pathCondition = Formula.conj pathCondition
            let usedVars =
                Set.union (Formula.freevars pathCondition) (Set.ofSeq programPreVars)
                |> Array.ofSeq |> Array.map (fun var -> Z.z3Context.MkIntConst var :> Microsoft.Z3.Expr)
            registerVariables usedVars

            let preFuncDecl = getFuncDeclForLocation k
            let preState = Z.z3Context.MkApp (preFuncDecl, z3PreVars) :?> Microsoft.Z3.BoolExpr

            let postFuncDecl = getFuncDeclForLocation k'
            let postVars = programVars |> Array.map (fun var -> Z.z3Context.MkIntConst (Var.prime_var var (Map.findWithDefault var 0 varToPostIdx)) :> Microsoft.Z3.Expr)
            let postState = Z.z3Context.MkApp (postFuncDecl, postVars) :?> Microsoft.Z3.BoolExpr

            let transitionCondition = Z.z3Context.MkImplies (Z.z3Context.MkAnd (preState, Formula.z3 pathCondition), postState)
            let ruleName = sprintf "trans_%i" idx
            rules <- (buildRule usedVars transitionCondition, Z.z3Context.MkSymbol ruleName) :: rules
            ruleNameToTransition.[ruleName] <- (k, cmds, k')

        //Finally, build the query:
        let errorFuncDecl = getFuncDeclForLocation errorLocation
        let errorQuery = Z.z3Context.MkApp(errorFuncDecl, z3PreVars) :?> Microsoft.Z3.BoolExpr
        if printSMT2Horn then
            printfn "(query %A)" errorQuery
        let queryVars =
            if z3PreVars.Length = 0 then
               [| Z.z3Context.MkIntConst "__makeItLookLessEmptyVar" :> Microsoft.Z3.Expr |]
            else
               z3PreVars
        (locationToFuncDecl, rules, Z.z3Context.MkExists (queryVars, errorQuery), ruleNameToTransition)

    static member inline private CallOnFixedPoint
        (z3Context : Microsoft.Z3.Context)
        (fixedPoint : Microsoft.Z3.Fixedpoint)
        (locationToFuncDecl : Dictionary<int,Microsoft.Z3.FuncDecl>)
        (rules : (Microsoft.Z3.Quantifier * Microsoft.Z3.StringSymbol) list)
        (errorQuery : Microsoft.Z3.BoolExpr) =
        //When adding stuff, copy it over into our local context:
        Seq.iter (fun (fD : Microsoft.Z3.FuncDecl) -> fixedPoint.RegisterRelation (fD.Translate z3Context)) locationToFuncDecl.Values
        Seq.iter (fun ((rule, name) : (Microsoft.Z3.Quantifier * Microsoft.Z3.StringSymbol)) -> fixedPoint.AddRule (rule.Translate z3Context, name)) rules
        match fixedPoint.Query (errorQuery.Translate z3Context) with
        | Microsoft.Z3.Status.SATISFIABLE -> Some (fixedPoint.GetRuleNamesAlongTrace())
        | _ -> None

    member private __.CallPDR (locationToFuncDecl : Dictionary<int,Microsoft.Z3.FuncDecl>) (rules : (Microsoft.Z3.Quantifier * Microsoft.Z3.StringSymbol) list) (errorQuery : Microsoft.Z3.BoolExpr) =
        use z3Context = lock Z.z3Context (fun _ -> Z.getZ3Context())
        use fixedPoint = z3Context.MkFixedpoint()
        use muZParameters = z3Context.MkParams()
        muZParameters.Add("engine", Z.z3Context.MkSymbol("pdr"))
        muZParameters.Add("pdr.flexible_trace", true)
        fixedPoint.Parameters <- muZParameters

        Stats.startTimer "muZ - PDR Query"
        try     MuZWrapper.CallOnFixedPoint z3Context fixedPoint locationToFuncDecl rules errorQuery
        finally Stats.endTimer "muZ - PDR Query"

    member private __.CallSpacer (locationToFuncDecl : Dictionary<int,Microsoft.Z3.FuncDecl>) (rules : (Microsoft.Z3.Quantifier * Microsoft.Z3.StringSymbol) list) (errorQuery : Microsoft.Z3.BoolExpr) =
        use z3Context = lock Z.z3Context (fun _ -> Z.getZ3Context())
        use fixedPoint = z3Context.MkFixedpoint()
        use muZParameters = z3Context.MkParams()
        muZParameters.Add("engine", Z.z3Context.MkSymbol("spacer"))
        muZParameters.Add("use_heavy_mev", true)
        muZParameters.Add("pdr.flexible_trace", true)
        fixedPoint.Parameters <- muZParameters

        Stats.startTimer "muZ - Spacer Query"
        try     MuZWrapper.CallOnFixedPoint z3Context fixedPoint locationToFuncDecl rules errorQuery
        finally Stats.endTimer "muZ - Spacer Query"

    member private __.CallBMC (locationToFuncDecl : Dictionary<int,Microsoft.Z3.FuncDecl>) (rules : (Microsoft.Z3.Quantifier * Microsoft.Z3.StringSymbol) list) (errorQuery : Microsoft.Z3.BoolExpr) =
        use z3Context = lock Z.z3Context (fun _ -> Z.getZ3Context())
        use fixedPoint = z3Context.MkFixedpoint()
        use muZParameters = z3Context.MkParams()
        muZParameters.Add("engine", Z.z3Context.MkSymbol("bmc"))
        muZParameters.Add("bmc.linear_unrolling_depth", uint32 (rules.Length * 3))
        fixedPoint.Parameters <- muZParameters

        let res =
            Stats.startTimer "muZ - BMC Query"
            try     MuZWrapper.CallOnFixedPoint z3Context fixedPoint locationToFuncDecl rules errorQuery
            finally Stats.endTimer "muZ - BMC Query"
        if res.IsNone then
            // We do not want to return from this task, but wait for the competing tasks to finish
            while true do System.Threading.Thread.Sleep 100
        res

    interface SafetyProver with
        member self.ErrorLocationReachable () =
            Log.log parameters "Building muZ program representation"
            Stats.startTimer "muZ - Clause construction"
            let (locationToFuncDecl, rules, errorQuery, ruleNameToTransition) = self.BuildProgramRepresentation()
            Stats.endTimer "muZ - Clause construction"
            Log.log parameters "Querying muZ for safety ..."
            let res =
                match parameters.safety_implementation with
                | Parameters.PDR -> self.CallPDR locationToFuncDecl rules errorQuery
                | Parameters.Spacer -> self.CallSpacer locationToFuncDecl rules errorQuery
                | Parameters.SpacerBMC ->
                    use cancellationTokenSource = new System.Threading.CancellationTokenSource();
                    let bmcTask = Task.Factory.StartNew(fun () -> self.CallBMC locationToFuncDecl rules errorQuery, cancellationTokenSource.Token)
                    let spacerTask = Task.Factory.StartNew(fun () -> self.CallSpacer locationToFuncDecl rules errorQuery, cancellationTokenSource.Token)
                    let resIndex = Task.WaitAny(spacerTask, bmcTask);
                    cancellationTokenSource.Cancel()
                    if resIndex = 0 then
                        Stats.incCounter "muZ - Spacer faster than BMC"
                        fst spacerTask.Result
                    else
                        Stats.incCounter "muZ - BMC faster than Spacer"
                        fst bmcTask.Result
                | _ -> failwithf "Unknown muZ safety engine %A. Giving up." parameters.safety_implementation

            match res with
            | Some rulesInTrace ->
                Log.log parameters "... found counterexample"

                //Now translate into our format, from the back to get the trace in the right order:
                let mutable resultTrace = []
                Log.debug parameters "Returned counterexample, last step first:"
                for i in 0 .. rulesInTrace.Length - 1 do
                    let curRuleName = (rulesInTrace.[i] :?> Microsoft.Z3.StringSymbol).String
                    Log.debug parameters ("  " + curRuleName)
                    if curRuleName <> "init" then
                        if curRuleName <> "__query" then //Ignore the error fact
                            if not(ruleNameToTransition.ContainsKey curRuleName) then
                                Log.log parameters <| sprintf "Cannot translate transition in muZ counterexample to our representation."
                            else
                                let (k, cmds, k') = ruleNameToTransition.[curRuleName]
                                if cmds.IsEmpty then
                                    //This case is important, otherwise we "skip" the transition in the returned CEx, and it looks like there is a gap in the path.
                                    resultTrace <- (k, Programs.assume Formula.truec, k') :: resultTrace
                                else
                                    for cmd in List.rev cmds do
                                        resultTrace <- (k, cmd, k') :: resultTrace

                Some resultTrace
            | _ ->
                Log.log parameters <| "... program is safe"
                None
        member __.DeleteProgramTransition _ = ()
        member __.ResetFrom _ = ()
