//////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      programs.fs
//
//  Abstract:
//
//      Representation for arithmetic, non-recursive programs
//
//  Notes:
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


module Microsoft.Research.T2.Programs

open Utils
open Term
open Formula
open Log

///
/// Constants not abstracted away because they are used as bounds
///
let bound_constants = [-4 .. 4] |> List.map (fun i -> bigint i) |> Set.ofList
//let bound_constants = ref (Set.ofList [0])

///
/// File position information for commands: (line number, file name)
///
type pos = (int * string) option

///
/// Commands datatype
///
type Command =

    ///
    /// Assign(p,v,t) represents v <- t at location p
    ///
    | Assign of pos * Var.var * term

    ///
    /// Assume(p,f) represents  "if (f) ignore" at location p
    ///
    | Assume of pos * formula

    member cmd.Is_Assign = match cmd with
                           | Assign(_,_,_) -> true
                           | Assume(_,_) -> false
    member cmd.Is_Assume = cmd.Is_Assign |> not
    member cmd.Position  = match cmd with
                           | Assign(pos,_,_) -> pos
                           | Assume(pos,_) -> pos

    override cmd.ToString() =
        let pos2pp pos =
            match pos with
            | None -> ""
            | Some(k,file) -> sprintf "%s:%d" file k

        match cmd with
        | Assign(None,v,e) -> Var.pp v + " <- " + e.pp + ";"
        | Assume(None,e)   -> "assume(" + Formula.pp e + ");"
        | Assign(p,v,e)    -> Var.pp v + " <- " + e.pp + "; // at " + pos2pp p
        | Assume(p,e)      -> "assume(" + Formula.pp e + "); // at " + pos2pp p 

let assume f = Assume(None, f)
let assign v t = Assign(None, v, t)
let skip = Assume(None,Formula.truec)

type NodeId = int
type ProgramLocation = NodeId
type ProgramLocationLabel =
    | OriginalLocation of string 
    | DuplicatedLocation of string
    | DuplicatedCutpointLocation of string
    | CutpointVarSnapshotLocation of string
    | CutpointDummyEntryLocation of string
    | CutpointRFCheckLocation of string

    override self.ToString() =
        match self with
        | OriginalLocation label -> label
        | DuplicatedLocation label -> label + "#"
        | DuplicatedCutpointLocation label -> label + "# (cp)"
        | CutpointVarSnapshotLocation label -> label + "# (snap)"
        | CutpointDummyEntryLocation label -> label + "# (entry)"
        | CutpointRFCheckLocation label -> label + " (rf check)"

let getBaseLabel = function
    | CutpointRFCheckLocation baseLabel
    | CutpointVarSnapshotLocation baseLabel
    | CutpointDummyEntryLocation baseLabel
    | DuplicatedCutpointLocation baseLabel
    | DuplicatedLocation baseLabel
    | OriginalLocation baseLabel -> baseLabel

//
// Pretty-printing routines
//

let commands2pp b = (List.fold (fun x y -> x + "    " + y.ToString() + "\n") "{\n" b) + "}"

///
/// Return free variables in a sequence of commands
///
let freevars cmds =
    let cmd_vars c =
        match c with
        | Assign(_, v, e) ->  (Term.freevars e).Add v
        | Assume(_, e) ->    freevars e

    Seq.map cmd_vars cmds |> Set.unionMany

///
/// Return the set of variables modified by a sequence of commands
///
let modified cmds =
    seq {
        for cmd in cmds do
            match cmd with
            | Assume _ -> ()
            | Assign (_, v, _) -> yield v
    } |> Set.ofSeq

///
/// Replace all constants that are not in 'range' with special variables
/// like __const__42. Return new term and set of eliminated constants.
///
let rec term_constants range t =
    let s = ref Set.empty
    let rec alpha t =
        match t with
        | Nondet -> Nondet
        | Const(c) when Set.contains c range -> Const(c)
        | Const(c) -> s := Set.add c !s;
                      Var(Formula.const_var c)
        | Var(v) -> Var(v)
        | Neg(t) -> Neg(alpha t)
        | Add(t1, t2) -> Add(alpha t1, alpha t2)
        | Sub(t1, t2) -> Sub(alpha t1, alpha t2)
        | Mul(t1, t2) -> Mul(alpha t1, alpha t2)
    let t' = alpha t
    (t', !s)

///
/// Replace all constants that are not in range with special variables
/// like __const__42. Return new formula and set of eliminated constants.
///
let rec formula_constants range f =
    let s = ref Set.empty

    let case_term t1 t2 f =
        let (t1', s1) = term_constants range t1
        let (t2', s2) = term_constants range t2
        s := Set.unionMany [!s; s1; s2]
        f(t1',t2')

    let rec alpha f =
        match f with
        | Eq(t1, t2) -> case_term t1 t2 Eq
        | Ge(t1, t2) -> case_term t1 t2 Ge
        | Le(t1, t2) -> case_term t1 t2 Le
        | Gt(t1, t2) -> case_term t1 t2 Gt
        | Lt(t1, t2) -> case_term t1 t2 Lt
        | And(f1, f2) -> And(alpha f1, alpha f2)
        | Or(f1, f2) -> Or(alpha f1, alpha f2)
        | Not(f) -> Not(alpha f)
    let f' = alpha f
    (f', !s)

/// Replace all constants that are not in range with special variables
/// like __const__42. Return new commands and set of eliminated constants.
let commands_constants range cmds =
    /// Replace all constants that are not in range with special variables
    /// like __const__42. Return new command and set of eliminated constants.
    let command_constants range cmd =
        let cmd =
            let vs = freevars [cmd]
            let pos = match cmd with
                      | Assign(pos,_,_) -> pos
                      | Assume(pos,_) -> pos
            let contains_pc = Set.exists (fun (v:string) -> v.Contains "_pc") vs
            if contains_pc then
                Assume(pos,Formula.truec)
            else
                cmd

        match cmd with
        | Assume(pos,f) ->
            let (f',s) = formula_constants range f
            (Assume(pos,f'),s)
        | Assign(pos,v,t) ->
            let (t',s) = term_constants range t
            (Assign(pos,v,t'),s)

    let cmds', constants = List.unzip (List.map (command_constants range) cmds)
    (cmds', Set.unionMany constants)

type private SeqPar =
    | Atom of Command
    | Seq of SeqPar list
    | Par of SeqPar list

let rec private as_seq sp =
    match sp with
    | Seq ss -> ss |> List.map as_seq |> List.concat
    | _ -> [sp]

//Returns a map of a nested loop, out loop
let make_isolation_map (loops : Map<NodeId,Set<NodeId>>) =
    let mutable isolation_map = Map.empty

    for KeyValue(cp, loop) in loops do
        for loc in loop do
            if loops.ContainsKey(loc) then
                let v = loops.[loc]
                if not(Set.contains cp v) then
                    isolation_map <- isolation_map.Add(loc, cp)

    isolation_map

/// Collapse adjacent commands so that if there were multiple commands
/// in the transition from location x to location y, we end up with a single list of commands
/// for the transition from x to y.
/// Example: [(1, a, 2), (1, b, 2), (2, c, 3), (2, d, 3)] -> [(1, [a, b], 2), (2, [c, d], 3)]
/// Loop edges are not allowed.
let collapse_path p =
    let mutable first = true
    let mutable prev_l1 = 0
    let mutable prev_l2 = 0
    let mutable accum_cmds = []
    let mutable result = []

    for (l1, cmd, l2) in p do
        if not first && l1 = prev_l1 && l2 = prev_l2 then
            accum_cmds <- cmd :: accum_cmds
        else
            //assert (first || prev_l2 = l1)
            if accum_cmds <> [] then
                result <- (prev_l1, List.rev accum_cmds, prev_l2) :: result
            prev_l1 <- l1
            prev_l2 <- l2
            accum_cmds <- [cmd]
        first <- false

    if accum_cmds <> [] then
        result <- (prev_l1, List.rev accum_cmds, prev_l2) :: result

    List.rev result

let print_path path =
    for from ,cmds, to_ in path do
        printf "    %d-->%d;\n" from to_
        for cmd in cmds do
            printf "              %s\n" (cmd.ToString())

let symbolic_consts_cmds consts =

    let small = bound_constants

    assert ((Set.intersect small consts).IsEmpty)

    let consts = Set.union small consts
    let consts = Set.toList consts |> List.sort

    let make_const k =
       if Set.contains k small then
           Term.Const k
       else
           Var(Formula.const_var k)

    [
        if not consts.IsEmpty then
            for c1, c2 in List.zip (List.all_but_last consts) (List.tail consts) do
                if not (Set.contains c1 small &&
                        Set.contains c2 small) then
                    let v1 = make_const c1
                    let v2 = make_const c2
                    assert (c1 < c2)
                    let lt = Lt(v1, v2)
                    yield Assume(None, lt)
    ]

let consts_cmds path =
    let mutable used = Set.empty
    let assign_const_vars cmd =
        match cmd with
        | Assume(_,_) -> Set.empty
        | Assign(_,_,t) -> Term.freevars t |> Set.filter Formula.is_const_var
    let assign_const_vars_cmds cmds = List.map assign_const_vars cmds |> Set.unionMany

    for (_,cmds,_) in path do
        let vs = assign_const_vars_cmds cmds
        used <- Set.union used (Set.filter Formula.is_const_var vs)
    done
    let used_ints = Set.map Formula.get_const_from_constvar used
    symbolic_consts_cmds used_ints

/// Replace __const variables by the actual constants again
let const_subst cmd =
    match cmd with
        | Assign(pos,v,t) ->
            let t' = Term.subst Formula.eval_const_var t
            Assign(pos,v,t')
        | Assume(pos,f)   ->
            let f' = Formula.subst Formula.eval_const_var f
            Assume(pos,f')

let addVarsToVarMap fs varMap =
    let vars = List.fold (fun accum f -> Set.union accum (Formula.freevars f)) Set.empty fs |> Set.toList
    let rec addVars vars varMap =
        match vars with
        | [] -> varMap
        | h::t -> addVars t (match Map.tryFind h varMap with | None -> Map.add h 0 varMap | _ -> varMap)
    addVars vars varMap

/// Translates a sequence of commands into a transition formula over pre (v^0), post (v^varMap.[v]) and intermediate variables.
let cmdsToFormulae cmds varMap =
    let cmdToFormula varMap cmd =
        match cmd with
        | Assign(_, v, Nondet) ->
            let idx = (Map.findWithDefault v 0 varMap) + 1
            let lhs = Term.var (Var.prime_var v idx)
            let varMap' = Map.add v idx varMap
            (Formula.Eq(lhs, lhs), varMap')
        | Assign(_, v, t) ->
            let idx = (Map.findWithDefault v 0 varMap) + 1
            let lhs = Term.var(Var.prime_var v idx)
            let rhs = Term.alpha (fun x -> Var.prime_var x (Map.findWithDefault x 0 varMap)) t
            let varMap' = Map.add v idx varMap
            (Formula.Eq(lhs, rhs), varMap')
        | Assume(_, e) ->
            let varMap = addVarsToVarMap [e] varMap
            let f = Formula.alpha (fun x -> Var.prime_var x (Map.findWithDefault x 0 varMap)) e
            (f, varMap)
    let rec cmdsToFormulae cs varMap =
        match cs with
        | c :: cs' -> let (fs, varMap') = cmdToFormula varMap c
                      let (fs', varMap'') = cmdsToFormulae cs' varMap'
                      (fs :: fs', varMap'')
        | [] -> ([], varMap)
    cmdsToFormulae cmds varMap

let cmdsToCetaFormula (variables : Var.var seq) cmds =
    let (formula, varMap) = cmdsToFormulae cmds Map.empty
    //Extend to reflect unchanged variables:
    let (formula, varMap) =
        Seq.fold 
            (fun (formula, varMap) var ->
                if Map.findWithDefault var 0 varMap = 0 then
                    let newVarMap = Map.add var 1 varMap
                    let newFormula = (Formula.Eq (Var (Var.prime_var var 0), Var (Var.prime_var var 1))) :: formula
                    (newFormula, newVarMap)
                else
                    (formula, varMap))
            (formula, varMap)
            variables
    (formula, varMap)

/// Convert path to path formula, applying SSA transformation.
/// varMap contains var to SSA version number.
/// Return pair (<list of transition formulae>, <new varMap>).
/// If variable is not present in varMap, its version is 0.
let cmdPathToFormulaPathAndVarMap path varMap =


    // Convert a path (sequence of commands) to a sequence of formulae over the program variables.
    let rec pathToFormulae path varMap =
        let isSkip cmd =
            match cmd with
            | Assume (_, f) -> Formula.is_true_formula f
            | _ -> false
        match path with
        | (l1, cmds, l2) :: rest ->
            let cmds = List.filter (isSkip >> not) cmds
            let (fs, varMap') = cmdsToFormulae cmds varMap
            let (rest_formulae, varMap'') = pathToFormulae rest varMap'
            (l1, fs, l2) :: rest_formulae, varMap''
        | [] -> ([], varMap)

    pathToFormulae path varMap

let cmdPathToFormulaPath p =
    cmdPathToFormulaPathAndVarMap p Map.empty |> fst

/// Vars from 'vars' go to prevars and postvars.
/// Prevars and postvars are guaranteed to be distinct.
let cmdPathToRelation path vars =
    let cmds = List.collect (fun (_, cmds, _) -> cmds) path
    let writtenVars = Set.intersect (modified cmds) vars
    let unwrittenVars = Set.difference vars writtenVars

    let (transitions, varMap) = cmdPathToFormulaPathAndVarMap path Map.empty

    let formulae = List.collect (fun (_, f, _) -> f) transitions

    let copyForward v idx =
        Formula.Eq(Term.var(Var.prime_var v idx), Term.var(Var.prime_var v (idx + 1)))

    let copyFormulae = [for v in unwrittenVars -> copyForward v 0]

    let aggregateFormula = Formula.conj (formulae @ copyFormulae)

    let prevars = [for v in writtenVars -> Var.var(Var.prime_var v 0)]
    let postvars = [for v in writtenVars -> Var.var(Var.prime_var v (Map.findWithDefault v 0 varMap))]

    let copyPrevars = [for v in unwrittenVars -> Var.var(Var.prime_var v 0)]
    let copyPostvars = [for v in unwrittenVars -> Var.var(Var.prime_var v 1)]

    Relation.make aggregateFormula (prevars @ copyPrevars) (postvars @ copyPostvars)

let exportLocation (writer : System.Xml.XmlWriter) (loc : ProgramLocationLabel) =
    match loc with
    | CutpointRFCheckLocation _ ->
        assert false
    | CutpointVarSnapshotLocation id ->
        writer.WriteElementString ("locationDuplicate", string id + "_var_snapshot")
    | CutpointDummyEntryLocation id ->
        writer.WriteElementString ("locationDuplicate", string id + "*")
    | DuplicatedCutpointLocation id ->
        writer.WriteElementString ("locationDuplicate", string id)
    | DuplicatedLocation id ->
        writer.WriteElementString ("locationDuplicate", string id)
    | OriginalLocation id ->
        writer.WriteElementString ("locationId", string id)

let exportTransition (writer : System.Xml.XmlWriter) variables transId source cmds target shouldExportVariable =
    let (transFormula, varToMaxSSAIdx) = cmdsToCetaFormula variables cmds
    writer.WriteStartElement "transition"

    writer.WriteElementString ("transitionId", string transId)
    
    writer.WriteStartElement "source"
    exportLocation writer source
    writer.WriteEndElement() //source end
    
    writer.WriteStartElement "target"
    exportLocation writer target
    writer.WriteEndElement() //target end

    //We are not using Formula.conj here because we absolutely want to control the order of formulas...
    let transLinearTerms = Formula.formula.FormulasToLinearTerms (transFormula :> _)
    writer.WriteStartElement "formula"
    Formula.linear_terms_to_ceta writer (Var.toCeta varToMaxSSAIdx) transLinearTerms shouldExportVariable
    writer.WriteEndElement () //formula end
    
    writer.WriteEndElement() //transition end

// Programs as Control Flow Graphs -----------------------------------------------------
type TransitionId = int
type Transition = ProgramLocation * Command list * ProgramLocation
type TransitionFunction = ProgramLocation -> (Command list * ProgramLocation) list

type Program private (parameters : Parameters.parameters) =
    let mutable initial = -1
    let mutable locationToLabel = BiDirectionalDictionary()
    let mutable locationCount = 0
    let mutable transitionCount = 0
    let mutable transitionsArray = Array.create 100 (-1,[],-1)
    /// x \in active iff transitions[x] != (-1,_,-1)
    let mutable activeTransitions = Set.empty
    /// Variables in the program
    let mutable variables = Set.empty
    /// Locations in the program
    let mutable locations = Set.empty
    /// Constants used in the program.
    let mutable usedConstants = Set.empty
    /// Flag indicating that we abstracted away things in an incomplete manner and hence should not report non-term
    let mutable incompleteAbstraction = false

    let mutable transitionFromCache : ListDictionary<NodeId, TransitionId * (NodeId * Command list * NodeId)> option = None
    let mutable findLoopsCache = None

    member __.Parameters with get () = parameters
    member __.Initial 
        with         get ()  = initial
        and  private set loc = initial <- loc
    member __.LocationToLabel
        with private get ()  = locationToLabel
        and  private set map = locationToLabel <- map
    member __.LocationCount 
        with private get ()    = locationCount
        and  private set count = locationCount <- count
    member __.TransitionCount 
        with private get ()    = transitionCount
        and  private set count = transitionCount <- count
    member __.TransitionsArray
        with private get ()         = transitionsArray
        and  private set transArray = transitionsArray <- transArray
    member __.ActiveTransitions
        with private get ()     = activeTransitions
        and  private set active = activeTransitions <- active
    member __.Variables
        with         get ()   = variables
        and  private set vars = variables <- vars
    member __.Locations
        with         get ()   = locations
        and  private set locs = locations <- locs
    member __.UsedConstants
        with private get ()     = usedConstants
        and  private set consts = usedConstants <- consts
    member __.IncompleteAbstraction
        with         get ()     = incompleteAbstraction
        and  private set flag   = incompleteAbstraction <- incompleteAbstraction || flag //never go back...

    /// Return deep copy of program
    member self.Clone() =
        new Program(self.Parameters,
                    Initial = self.Initial,
                    LocationToLabel = self.LocationToLabel.Clone(),
                    LocationCount = self.LocationCount,
                    TransitionCount = self.TransitionCount,
                    TransitionsArray = Array.copy self.TransitionsArray,
                    ActiveTransitions = self.ActiveTransitions,
                    Variables = self.Variables,
                    Locations = self.Locations,
                    UsedConstants = self.UsedConstants,
                    IncompleteAbstraction = self.IncompleteAbstraction
        )

    static member Create (pars : Parameters.parameters) (is_temporal : bool) (init : ProgramLocationLabel) (ts : (ProgramLocationLabel * Command list * ProgramLocationLabel) seq) (incompleteAbstraction : bool) =
        let program = new Program(pars, IncompleteAbstraction = incompleteAbstraction)

        let mutable init_is_target = false
        for (x, cmds, y) in ts do
            program.AddTransitionMapped x cmds y |> ignore
            if y = init then
                init_is_target <- true
        done
        program.Initial <- program.GetLabelledLocation init

        //Make sure that an initial state is not in a loop:
        if not(is_temporal) && init_is_target then
            let new_initial = program.NewLocationWithLabel (OriginalLocation "separatedStart")
            program.AddTransition new_initial [] program.Initial |> ignore
            program.Initial <- new_initial
        else
            if init_is_target then
                let (cp_to_dominated_loops, _) = program.FindLoops()
                if Map.containsKey program.Initial cp_to_dominated_loops then
                    Utils.dieWith "Cannot do temporal proofs for programs with start state on a loop."
        program

    member self.ToString (stream : System.IO.TextWriter) =
        fprintfn stream "=================== PROGRAM ====================="
        fprintfn stream "Initial location: %d" self.Initial
        fprintfn stream "Labels:"
        for (loc, label) in locationToLabel do
            fprintfn stream "  %A:%d" label loc

        fprintf stream "Transitions:"
        for (k, cmds, k') in self.Transitions do
            fprintfn stream "%d ---> %d\n%s" k k' (commands2pp cmds)
    
    override self.ToString () =
        use stream = new System.IO.StringWriter()
        self.ToString stream
        stream.ToString()

    member self.Transitions 
        with get () =
            seq {
                for idx in self.ActiveTransitions do
                    yield transitionsArray.[idx]
            }

    member self.TransitionsWithIdx
        with get () =
            seq {
                for idx in self.ActiveTransitions do
                    yield (idx, transitionsArray.[idx])
            }

    member self.TransitionsFrom loc =
        match transitionFromCache with
        | None ->
            [
                for idx in self.ActiveTransitions do
                    let (k, cmds, k') = transitionsArray.[idx]
                    if k = loc then
                        yield (idx, (k, cmds, k'))
            ]
        | Some dict ->
            dict.[loc]

    member self.CacheTransitionsFrom () =
        if transitionFromCache.IsNone then
            let directConnections = ListDictionary()
            for (idx, (k, cmds, k')) in self.TransitionsWithIdx do
                directConnections.Add (k, (idx, (k, cmds, k')))
            transitionFromCache <- Some directConnections
        transitionFromCache.Value

    member self.TransitionsTo loc =
        seq { 
            for idx in self.ActiveTransitions do
                let (k, cmds, k') = transitionsArray.[idx]
                if k' = loc then
                    yield (idx, (k, cmds, k'))
        }

    member self.GetTransition idx = transitionsArray.[idx]
    member self.SetTransition idx (source, cmds, target) = 
        self.Variables <- Set.union self.Variables (freevars cmds)
        self.Locations <- Set.add source <| Set.add target self.Locations
        transitionsArray.[idx] <- (source, cmds, target)
        self.InvalidateCaches()

    member self.TransitionNumber with get () = self.ActiveTransitions.Count

    member private self.NewLabellessLocation () : ProgramLocation =
        let old = self.LocationCount 
        self.LocationCount <- old + 1
        old
 
    member self.NewLocation labelMaker : ProgramLocation =
        let newLoc = self.NewLabellessLocation ()
        self.LocationToLabel.[newLoc] <- labelMaker ("anon_" + string newLoc)
        newLoc
    
    /// Creates a new location and assigns a label to it. If the label already existed, it will be overwritten.
    member self.NewLocationWithLabel label : ProgramLocation =
        let newLoc = self.NewLabellessLocation ()
        locationToLabel.[newLoc] <- label
        newLoc

    /// Returns the location in the program with the given label. If no such location existed, creates a new one.
    member self.GetLabelledLocation (label : ProgramLocationLabel) : ProgramLocation =
        match locationToLabel.TryFindValue label with
        | None -> self.NewLocationWithLabel label
        | Some loc -> loc

    /// Checks if a location with this label exists. 
    member __.HasLabelledLocation (label : ProgramLocationLabel) : bool =
        locationToLabel.ContainsValue label

    /// Returns the label for the given location.
    member __.GetLocationLabel loc =
        locationToLabel.[loc]

    member private __.InvalidateCaches () =
        transitionFromCache <- None
        findLoopsCache <- None

    member self.AddVariable var =
        self.Variables <- Set.add var self.Variables

    ///Remove transition with index idx from the program
    member self.RemoveTransition idx =
        self.TransitionsArray.[idx] <- (-1, [], -1)
        self.ActiveTransitions <- Set.remove idx self.ActiveTransitions
        self.InvalidateCaches()

    /// add transition source -- cmds --> target as it is, without any preprocessing
    member self.AddTransition source cmds target : int =
        let newTransIdx = self.TransitionCount
        self.TransitionCount <- newTransIdx + 1
        self.ActiveTransitions <- Set.add newTransIdx self.ActiveTransitions
        if newTransIdx >= self.TransitionsArray.Length then
            let newTransArray = Array.create (2 * self.TransitionsArray.Length) (-1,[],-1)
            System.Array.Copy (self.TransitionsArray, newTransArray, self.TransitionsArray.Length)
            self.TransitionsArray <- newTransArray
        transitionsArray.[newTransIdx] <- (source, cmds, target)
        self.Variables <- Set.union self.Variables (freevars cmds)
        self.Locations <- Set.add source <| Set.add target self.Locations
        self.InvalidateCaches()
        newTransIdx

    /// add transition n--T-->M with preprocessing (eliminates constants, creates DNF)
    member self.AddTransitionMapped (input_n : ProgramLocationLabel) (cmds : Command list) (input_m : ProgramLocationLabel) : int list =
        let n = self.GetLabelledLocation input_n
        let m = self.GetLabelledLocation input_m

        let rec command_to_seqpar cmd =
            let skip_if_true cmd =
                match cmd with
                | Assume (_, f) when Formula.is_true_formula f -> Seq []
                | _ -> Atom cmd

            match cmd with
            | Assume(_, f) when f.ContainsNondet() ->
                Seq []
            | Assume(pos, f) ->
                let atoms = 
                    f.PolyhedraDNF().SplitDisjunction()
                    |> List.map (fun (f : formula) -> f.SplitConjunction())
                match atoms with
                | [[f1]; [f2]] -> // disjunction of two atomic formulae
                    Par [for f' in [f1; f2] -> command_to_seqpar (Assume (pos, f'))]
                | [fs] -> // conjunction of atomic formulae
                    Seq [
                        for f in fs do
                            match f with
                            | Le (t1, t2) ->
                                let f =
                                    try
                                        Le (SparseLinear.term_as_linear t1, SparseLinear.term_as_linear t2)
                                    with SparseLinear.Nonlinear _ ->
                                        sprintf "WARNING: Non-linear assumption %s\n" (cmd.ToString()) |> Log.log parameters 
                                        self.IncompleteAbstraction <- true
                                        Formula.truec

                                let cmd = Assume (pos, f)
                                yield skip_if_true cmd

                            | _ -> dieWith "polyhedra_dnf returned something strange"
                    ]
                | x -> 
                    Log.log parameters <| sprintf "WARNING: assume blowup = %d\n" x.Length
                    Par [for f' in x -> Seq [for f'' in f' -> command_to_seqpar (Assume (pos, f''))]]

            | Assign(_, _, Nondet) ->
                Atom cmd
            | Assign(pos, v, tm) ->
                let c =
                    try
                        Assign(pos, v, SparseLinear.term_as_linear tm)
                    with SparseLinear.Nonlinear _ ->
                       sprintf "WARNING: Non-linear assignment %s\n" (cmd.ToString()) |> Log.log parameters
                       self.IncompleteAbstraction <- true
                       Assign(pos, v, Term.Nondet)
                Atom c

        let cmds =
            if parameters.elim_constants then
                let (cmds, consts) = commands_constants bound_constants cmds
                self.UsedConstants <- Set.union self.UsedConstants consts
                cmds
            else
                cmds
        let sp = cmds |> List.map command_to_seqpar |> Seq

        let addedTransitions = ref []

        let rec addTransitionSeqPar n sp m =
            let parts = as_seq sp
            if List.length parts = 0 then
                let newTransIdx = self.AddTransition n [] m
                addedTransitions := newTransIdx :: !addedTransitions
            else
                let len = List.length parts

                let mutable last_loc = n
                let mutable unsaved_commands = []
                for part, number in List.zip parts [0 .. len-1] do
                    match part with
                    | Atom cmd ->
                        unsaved_commands <- cmd::unsaved_commands
                    | Par pars ->
                        assert (List.length pars >= 1)
                        // it is important that Par introduces new nodes even when length(pars) = 1
                        // see command_to_seqpar
                        if unsaved_commands <> [] then
                            let loc = self.NewLocation OriginalLocation
                            let newTransIdx = self.AddTransition last_loc (List.rev unsaved_commands) loc
                            addedTransitions := newTransIdx :: !addedTransitions
                            unsaved_commands <- []
                            last_loc <- loc
                        let next_loc = if number = len-1 then m else self.NewLocation OriginalLocation
                        for par in pars do
                            addTransitionSeqPar last_loc par next_loc
                        last_loc <- next_loc
                        ()
                    | Seq _ -> die()
                if unsaved_commands <> [] then
                    assert (n = m || last_loc <> m)
                    let newTransIdx = self.AddTransition last_loc (List.rev unsaved_commands) m
                    addedTransitions := newTransIdx :: !addedTransitions

        addTransitionSeqPar n sp m
        self.InvalidateCaches()
        !addedTransitions

    /// Return a mapping from nodes to nodes that are reachable using the CFG edges
    member self.GetTransitiveCFG () =
        //(v, w) \in transitiveReaches <-> p has non-empty path from v to w
        let transitiveReaches = System.Collections.Generic.HashSet()
        for n in self.ActiveTransitions do
            let (l, _, l') = self.TransitionsArray.[n]
            transitiveReaches.Add (l, l') |> ignore

        //Who you gonna call? Floyd-Warshall!
        for w in self.Locations do
            for v in self.Locations do
                for u in self.Locations do
                    if transitiveReaches.Contains (w, u) && transitiveReaches.Contains (v, w) then
                        transitiveReaches.Add (v, u) |> ignore

        let reachableLocations = new SetDictionary<NodeId, NodeId>()
        for (v, w) in transitiveReaches do
            reachableLocations.Add (v, w)

        reachableLocations

    /// Prune out unreachable locations in the program
    member self.RemoveUnreachableLocations () =
        let reachableMap = self.GetTransitiveCFG()
        let reachableLocs = Set.add self.Initial reachableMap.[self.Initial]
        let unreachable = Set.difference self.Locations reachableLocs

        for idx in self.ActiveTransitions do
            let (k,_,k') = self.TransitionsArray.[idx]
            if Set.contains k unreachable || Set.contains k' unreachable then
                self.RemoveTransition idx

        self.Locations <- Set.difference self.Locations unreachable

    /// Returns strongly connected subgraphs in the transitive closure of the program's
    /// control-flow graph.
    member self.GetSCCSGs includeTrivial =
        SCC.find_sccs (self.CacheTransitionsFrom()) self.Initial includeTrivial

    /// Compute dominators tree
    member private self.GetDominatorsFrom loc =
        Dominators.find_dominators (self.CacheTransitionsFrom()) loc

    member self.GetCutpoints () =
        let cuts = ref Set.empty
        let marks = new System.Collections.Generic.Dictionary<NodeId, bool>()
        let rec dfs_visit node =
            marks.Add(node, false) // false means in progress
            for (_, (_, _, node')) in self.TransitionsFrom node do
                match marks.TryGetValue(node') with
                | false, _ -> dfs_visit node'
                | true, true -> ()
                | true, false ->
                    // node->node' is backedge
                    cuts := (!cuts).Add node'
            marks.[node] <- true // true means fully processed
        dfs_visit self.Initial
        !cuts |> Set.toList

    /// For each node we return a set of nodes representing the nodes "inside" the loop. As described in
    /// "Variance analyses from invariance analyses", POPL'07
    ///
    /// Return list of pairs (cutpoint, corresponding region)
    member self.GetIsolatedRegions () =
        let scs = self.GetSCCSGs false
        let dtree = self.GetDominatorsFrom self.Initial
        let cps = self.GetCutpoints()

        //Check out all CPs
        [for cutpoint in cps do
            //For each CP, find the SCCs dominated by it:
            let sets = [
                //Check each SCC:
                for comp in scs do
                    //Weed out trivial one-element SCCs.
                    let isNontrivial =
                        if comp.Count > 1 then
                            true
                        else
                            let singletonElement = Set.minElement comp
                            let outgoingTrans = self.TransitionsFrom singletonElement
                            Seq.exists (fun (_, (_, _, k)) -> k = singletonElement) outgoingTrans
                    if isNontrivial then
                        //Does this SCC only have one entry point?
                        if Dominators.well_formed dtree comp then
                            //Is that entry point our cutpoint? If yes, add things.
                            yield Set.filter (Dominators.dominates dtree cutpoint) comp // is that even right?
                        else
                            //If not, are we part of the SCC?
                            if comp.Contains cutpoint then
                                yield comp
                ]
            yield cutpoint, sets
        ]

    member self.GetIsolatedRegionsNonCP nodes =
        let scs = self.GetSCCSGs false
        let dtree = self.GetDominatorsFrom self.Initial

        //Check out all CPs
        [for node in nodes do
            //For each CP, find the SCCs dominated by it:
            let sets = [
                //Check each SCC:
                for comp in scs do
                    //Weed out trivial one-element SCCs. Invariant guarantees that we have no self-loops:
                    let isNontrivial =
                        if comp.Count > 1 then
                            true
                        else
                            let singletonElement = Set.minElement comp
                            let outgoingTrans = self.TransitionsFrom singletonElement
                            Seq.exists (fun (_, (_, _, k)) -> k = singletonElement) outgoingTrans
                    if isNontrivial then
                        //Does this SCC only have one entry point?
                        if Dominators.well_formed dtree comp then
                            //Is that entry point our cutpoint? If yes, add things.
                            yield Set.filter (Dominators.dominates dtree node) comp // is that even right?
                        else
                            //If not, are we part of the SCC?
                            if comp.Contains node then
                                yield comp
                ]
            yield node, sets
        ]

    member self.FindLoops() =
        Stats.startTimer "T2 - Find Loops"
        if findLoopsCache.IsNone then
            let regions = self.GetIsolatedRegions()
            let cps_to_loops =
                seq {
                    for (cp, sccs) in regions do
                        let loop = Set.unionMany sccs
                        yield cp, loop
                } |> Map.ofSeq
            let cps_to_sccs =
                seq {
                    for (cp, sccs) in regions do
                        let loop = sccs |> Seq.filter (fun scc -> scc.Contains cp) |> Set.unionMany
                        yield cp, loop
                } |> Map.ofSeq
            Stats.endTimer "T2 - Find Loops"
            findLoopsCache <- Some (cps_to_loops, cps_to_sccs)
        findLoopsCache.Value

    /// take function that transforms transition
    /// and apply it to every transition in the program
    member private self.TransitionsInplaceMap f =
        for idx in self.ActiveTransitions do
            transitionsArray.[idx] <- f transitionsArray.[idx]
        self.InvalidateCaches()

    /// If variables are used temporarly in basic blocks and then are killed or not used elsewhere, LetConvert
    /// removes them in the obvious way. livevars is assumed to be the set of live variables
    /// Our heuristic is based on the idea that more variables are bad, given how constraint-based rank
    /// function synthesis and interpolation work.
    /// It also special cases instrumentation variables, which might be considered dead, but are still
    /// important to us.
    member self.LetConvert (liveVariables : System.Collections.Generic.Dictionary<NodeId, Set<Var.var>>) =
        // Is the variable read in the later commands before being written to again? We know the livevars
        // at the beginning and end of the command sequence, but not in the intermediate points.
        // We could compute the live
        let rec needed_local v cmds =
            match cmds with
            | Assume(_,f)::cmds'   -> if Set.contains v (Formula.freevars f) then true
                                      else needed_local v cmds'
            | Assign(_,v',t)::cmds' -> if Set.contains v (Term.freevars t) then true
                                       else if v'=v then false
                                       else needed_local v cmds'
            | [] -> false

        let unrelated x v t = x<>v && not (Set.contains x  (Term.freevars t))
        let wipe x env = Map.filter (unrelated x) env

        let rewrite_cmd map cmd =
            let env v =
                match Map.tryFind v map with
                | Some t -> t
                | None -> Var v

            match cmd with
            | Assume(p,f) -> Assume(p,Formula.subst env f)
            | Assign(p,v,t) -> Assign(p,v,Term.subst env t)

        let rec interp lvs env cmds =
            match cmds with
            | Assign(pos,v,Nondet)::r ->
                let env' = wipe v env
                if not (Set.contains v lvs) && not (needed_local v r) && not(Formula.is_snapshot_var v) then
                    interp lvs env' r
                else
                    (Assign (pos, v, Nondet)) :: interp lvs env' r
            | Assign(pos,v,t)::r ->
                let cmd' = rewrite_cmd env (Assign(pos,v,t))
                let t' = match cmd' with
                         | Assign(_,_,t') -> t'
                         | _ -> die()
                let env' = wipe v env
                let env'' = if not (Set.contains v lvs) then Map.add v t' env' else env'
                if not (Set.contains v lvs) && not (needed_local v r) && not(Formula.is_snapshot_var v) then interp lvs env'' r
                else cmd'::interp lvs env'' r
            | assm::r -> rewrite_cmd env assm::interp lvs env r
            | [] -> []

        self.TransitionsInplaceMap (fun (k, T, k') ->
            let lvs = liveVariables.[k']
            let T' = interp lvs Map.empty T
            (k,T',k')
        )

    member self.ConstantPropagation mapping =
        let rewrite_cmd map cmd =
            let env v =
                match Map.tryFind v map with
                | Some c -> Term.Const c
                | None -> Var v
            match cmd with
            | Assume(p,f) -> Assume(p,Formula.subst env f)
            | Assign(p,v,t) -> Assign(p,v,Term.subst env t)

        let get_mods T =
            seq {
                for c in T do
                    match c with
                    | Assume(_, _) -> ()
                    | Assign(_, v, _) -> yield v
            } |> Set.ofSeq

        // make sure not to rewrite x to 5 if x is temporarily set to some other value in T
        let clean_map k T =
            let vs = get_mods T
            Map.filter (fun v _ -> not (Set.contains v vs)) (Map.find k mapping)

        self.TransitionsInplaceMap (fun (k,T,k') ->
            let map' = clean_map k T
            let T' = List.map (rewrite_cmd map') T
            (k,T',k')
        )

    member self.ConstantAssignmentPropagation (variables_to_protect : Set<Var.var>) =
        //For each location, keep a map var -> expr, where expr has the value of var
        let locToVarExprs = System.Collections.Generic.Dictionary()
        // Propagate variables. Continue if the target location set changed (either because of a first visit or because things changed)
        let rec loop (loc : NodeId) =
            let varToExprs : Map<Var.var, Term.term> = locToVarExprs.GetWithDefault loc Map.empty
            let mutable changedLocs = []
            for (_, (_, cmds, targetLoc)) in self.TransitionsFrom loc do
                //Keep a local, mutable copy
                let varToExprs = ref varToExprs
                for cmd in cmds do
                    match cmd with
                    | Assume _ -> ()
                    | Assign (_, v, t) ->
                        //Eliminate all expressions that are invalidated by this assignment:
                        let cleanedVarToExprs = Map.filter (fun _ expr -> not (Set.contains v (Term.freevars expr))) !varToExprs
                        varToExprs :=
                            if Term.contains_nondet t || Set.contains v (Term.freevars t) then Map.remove v cleanedVarToExprs
                            else Map.add v t cleanedVarToExprs
                //Compare with current state at target:
                match locToVarExprs.TryGetValue targetLoc with
                | (false, _) ->
                    //Discovered new pastures! Do the thing!
                    locToVarExprs.[targetLoc] <- !varToExprs
                    changedLocs <- targetLoc :: changedLocs
                |  (true, oldVarToExprs) ->
                    let commonVarExprs =
                        Map.filter
                            (fun k v ->
                                match (!varToExprs).TryFind k with
                                | Some v' -> v = v'
                                | _ -> false)
                            oldVarToExprs
                    if commonVarExprs <> oldVarToExprs then
                        locToVarExprs.[targetLoc] <- commonVarExprs
                        changedLocs <- targetLoc :: changedLocs
            List.iter loop changedLocs

        //Compute the sets of constant expressions:
        self.CacheTransitionsFrom() |> ignore
        loop self.Initial

        //Rewrite the program to make use of constant expressions:
        self.TransitionsInplaceMap
            (fun (k, cmds, k') ->
                let varToExprs = ref (locToVarExprs.GetWithDefault k Map.empty)
                let newCmds =
                    cmds
                    |> List.map
                        (fun cmd ->
                            let substEnv var =
                                if Set.contains var variables_to_protect || Formula.is_instr_var var then
                                    Term.var var
                                else
                                    Map.findWithDefault var (Term.var var) !varToExprs
                            match cmd with
                            | Assume (pos, f) -> Assume(pos, Formula.subst substEnv f)
                            | Assign (pos, v, t) ->
                                //Eliminate all expressions that are invalidated by this assignment:
                                let t = Term.subst substEnv t
                                let cleanedVarToExprs = Map.filter (fun _ expr -> not (Set.contains v (Term.freevars expr))) !varToExprs
                                varToExprs :=
                                    if Term.contains_nondet t || Set.contains v (Term.freevars t) then Map.remove v cleanedVarToExprs
                                    else Map.add v t cleanedVarToExprs
                                Assign (pos, v, t))
                (k, newCmds, k'))


    /// Adds a new initial transition that asserts relative information on symbolized constants (e.g., __const_4 < __const_10)
    member self.AddSymbolConstantInformation () =
        if not <| Set.isEmpty self.UsedConstants then
            let commands = symbolic_consts_cmds self.UsedConstants
            let new_init = self.NewLocation OriginalLocation
            self.AddTransition new_init commands self.Initial |> ignore
            self.Initial <- new_init

    /// Chain linear sequences of program transitions, in-place.
    /// Returns a map from original transition IDs to the freshly chosen transition IDs.
    member self.ChainTransitions (dontChain : NodeId seq) onlyRemoveUnnamed =
        let dontChain = System.Collections.Generic.HashSet(dontChain)
        // (1) Create map, giving access to all incoming/outgoing transitions for a location
        let incomingTransitions = Utils.SetDictionary()
        let outgoingTransitions = Utils.SetDictionary()
        for idx in self.ActiveTransitions do
            let (k, cmds, k') = transitionsArray.[idx]
            incomingTransitions.Add (k', (Set.singleton idx, k, cmds)) |> ignore
            outgoingTransitions.Add (k, (Set.singleton idx, cmds, k')) |> ignore

        // (2) Then try to chain away each location:
        for location in self.Locations do
            if not (dontChain.Contains location) 
                && (not onlyRemoveUnnamed || not (locationToLabel.ContainsKey location)) then
                let incomingCount = incomingTransitions.[location].Count
                let outgoingCount = outgoingTransitions.[location].Count
                let incomingEmptySingleton =
                    if incomingCount = 1 && outgoingCount > 0 then
                        let (_, _, cmds) = incomingTransitions.[location].MinimumElement
                        cmds.IsEmpty
                    else
                        false
                let outgoingEmptySingleton =
                    if outgoingCount = 1 && incomingCount > 0 then
                        let (_, cmds, _) = outgoingTransitions.[location].MinimumElement
                        cmds.IsEmpty
                    else
                        false
                if (incomingCount = 1 && outgoingCount = 1) || incomingEmptySingleton || outgoingEmptySingleton then
                    let mutable chained = true
                    for (inIdx, s, cmds1) in incomingTransitions.[location] do
                        for (outIdx, cmds2, e) in outgoingTransitions.[location] do
                            //Don't do this for self-loops
                            if s <> location && e <> location then
                                if parameters.print_log then
                                    Log.log parameters <| sprintf "Removed location %i by chaining %A:(%i,%i) w/ %A:(%i,%i)" location inIdx s location outIdx location e
                                let cmds = cmds1 @ cmds2
                                let transIdxSet = Set.union inIdx outIdx
                                incomingTransitions.RemoveKeyVal e (outIdx, location, cmds2)
                                incomingTransitions.Add (e, (transIdxSet, s, cmds))
                                outgoingTransitions.RemoveKeyVal s (inIdx, cmds1, location)
                                outgoingTransitions.Add (s, (transIdxSet, cmds, e))
                            else
                                chained <- true
                    if chained then
                        incomingTransitions.Remove location |> ignore
                        outgoingTransitions.Remove location |> ignore

        // (3) Rewrite the program:
        self.ActiveTransitions <- Set.empty
        self.TransitionCount <- 0
        self.Locations <- Set.empty
        let transMap = System.Collections.Generic.Dictionary()
        for (startLoc, outgoings) in outgoingTransitions do
            for (transIdxSet, cmds, endLoc) in outgoings do
                let newTransIdx = self.AddTransition startLoc cmds endLoc
                for transIdx in transIdxSet do
                    transMap.[transIdx] <- newTransIdx
        transMap

    member self.ToCeta (writer : System.Xml.XmlWriter) (elementName : string) shouldExportVar =
        writer.WriteStartElement elementName
        writer.WriteStartElement "initial"
        exportLocation writer (locationToLabel.[self.Initial])
        writer.WriteEndElement () //initial end
        for (transIdx, (source, cmds, target)) in self.TransitionsWithIdx do
            let source_label = locationToLabel.[source]
            let target_label = locationToLabel.[target]
            exportTransition writer self.Variables transIdx source_label cmds target_label shouldExportVar
        writer.WriteEndElement () //program end

/// Merge chains of transitions together.
let chain_transitions nodes_to_consider transitions =
    // (1) Create maps in_trans/out_trans mapping nodes to incoming/outgoing transitions.
    let in_trans = new System.Collections.Generic.Dictionary<NodeId, System.Collections.Generic.HashSet<Set<TransitionId> * Transition>>()
    let out_trans = new System.Collections.Generic.Dictionary<NodeId, System.Collections.Generic.HashSet<Set<TransitionId> * Transition>>()
    let add_to_set_dict (dict : System.Collections.Generic.Dictionary<NodeId, System.Collections.Generic.HashSet<Set<TransitionId> * Transition>>) k v =
        if dict.ContainsKey k then
            dict.[k].Add v
        else
            dict.Add(k, new System.Collections.Generic.HashSet<(Set<TransitionId> * Transition)>())
            dict.[k].Add v
    for trans in transitions do
        let (_, (k, _, k')) = trans
        add_to_set_dict in_trans k' trans |> ignore
        add_to_set_dict out_trans k trans |> ignore

    let first_elem_of_set (set : System.Collections.Generic.HashSet<'T>) =
        let mutable set_enum = set.GetEnumerator()
        set_enum.MoveNext() |> ignore
        set_enum.Current

    // (2) If for some k out_trans.[k] and in_trans.[k] are singleton sets, replace the two transitions by a direct one.
    for k in nodes_to_consider do
        if in_trans.ContainsKey k && out_trans.ContainsKey k then
            let in_trans_k = in_trans.[k]
            let out_trans_k = out_trans.[k]
            if in_trans_k.Count = 1 && out_trans_k.Count = 1 then
                // k has only one incoming and one outgoing transition. Merge:
                let t1 = first_elem_of_set in_trans_k //that's the only one!
                let (idxs1, (k1, cmds1, _)) = t1
                let t2 = first_elem_of_set out_trans_k //that's the only one!
                let (idxs2, (_, cmds2, k2)) = t2
                let t = (Set.union idxs1 idxs2, (k1, cmds1@cmds2, k2))
                if k1 <> k then
                    //printfn "Chaining %i->%i and %i->%i" k1 k k k2
                    //Now remove t1 and t2, add t instead:
                    in_trans.Remove k |> ignore
                    out_trans.Remove k |> ignore
                    if out_trans.ContainsKey k1 then
                        out_trans.[k1].Remove t1 |> ignore
                        out_trans.[k1].Add t |> ignore
                    if in_trans.ContainsKey k2 then
                        in_trans.[k2].Remove t2 |> ignore
                        in_trans.[k2].Add t |> ignore
    // (3) The updated transitions are now in in_trans and out_trans:
    in_trans.Values |> Seq.concat |> Set.ofSeq

let add_const1_var_to_relation extra_pre_var extra_post_var rel =
    let (formula, prevars, postvars) = (Relation.formula rel, Relation.prevars rel, Relation.postvars rel)
    let newformula =
        Formula.And (
            Formula.And (formula,
                (Formula.Eq (Term.Var extra_pre_var, (Term.constant 1)))),
            (Formula.Eq (Term.Var extra_post_var, (Term.constant 1))))
    Relation.standardise_postvars (Relation.make newformula (extra_pre_var::prevars) (extra_post_var::postvars))
