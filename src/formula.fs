////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      formula.fs
//
//  Abstract:
//
//       * Definition of Formula.formula type + simple tools for quantifier free FOL formulae with arithmetic.
//       * Connection to Z3 for formula type
//       * Also: some special encoding predicates and definitions used in the effecient reduction of termination
//         to safety checking
//
//  Notes:
//
//       * TODO.v2: Long term it might be nice just to move to Native Z3 formulae
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

module Microsoft.Research.T2.Formula

open Utils
open Term

[<StructuredFormatDisplayAttribute("{pp}")>]
type formula =
    |Not of formula | And of formula * formula | Or of formula * formula | Eq of term * term
    | Lt of term * term | Le of term * term | Ge of term * term | Gt of term * term

    member self.pp =
        // see comment to term2pp
        let protect strength force s =
            if strength >= force then s else "(" + s + ")"

        // using standard C precedence
        let rec pp' force e =
            match e with
            | Not(e)     -> protect 3 force ("not " + pp' 3 e)
            | And(e1,e2) -> protect 2 force  (pp' 2 e1 + " and " + pp' 2 e2)
            | Or(e1,e2)  -> protect 1 force (pp' 1 e1 + " or " + pp' 1 e2)
            | Eq(e1,e2)  -> e1.pp + " == " + e2.pp
            | Lt(e1,e2)  -> e1.pp + " < " + e2.pp
            | Le(e1,e2)  -> e1.pp + " <= " + e2.pp
            | Ge(e1,e2)  -> e1.pp + " >= " + e2.pp
            | Gt(e1,e2)  -> e1.pp + " > " + e2.pp

        pp' 0 self

    override self.ToString () = self.pp

    member self.prefix_pp =
        match self with
        | Not(e)     -> sprintf "(not %s)" e.prefix_pp
        | And(e1,e2) -> sprintf "(and %s %s)" e1.prefix_pp e2.prefix_pp
        | Or(e1,e2)  -> sprintf "(or %s %s)" e1.prefix_pp e2.prefix_pp
        | Eq(e1,e2)  -> sprintf "(= %s %s)" e1.prefix_pp e2.prefix_pp
        | Lt(e1,e2)  -> sprintf "(< %s %s)" e1.prefix_pp e2.prefix_pp
        | Le(e1,e2)  -> sprintf "(<= %s %s)" e1.prefix_pp e2.prefix_pp
        | Ge(e1,e2)  -> sprintf "(>= %s %s)" e1.prefix_pp e2.prefix_pp
        | Gt(e1,e2)  -> sprintf "(> %s %s)" e1.prefix_pp e2.prefix_pp

    member self.clause_pp varPP =
        match self with
        | Not(e) -> sprintf "\\+(%s)" (e.clause_pp varPP)
        | And(e1, e2) -> sprintf "(%s, %s)" (e1.clause_pp varPP) (e2.clause_pp varPP)
        | Or(e1, e2) -> sprintf "(%s; %s)" (e1.clause_pp varPP) (e2.clause_pp varPP)
        | Eq(e1, e2) -> sprintf "(%s=%s)" (e1.clause_pp varPP) (e2.clause_pp varPP)
        | Lt(e1, e2) -> sprintf "(%s<%s)" (e1.clause_pp varPP) (e2.clause_pp varPP)
        | Le(e1, e2) -> sprintf "(%s=<%s)" (e1.clause_pp varPP) (e2.clause_pp varPP)
        | Gt(e1, e2) -> sprintf "(%s>%s)" (e1.clause_pp varPP) (e2.clause_pp varPP)
        | Ge(e1, e2) -> sprintf "(%s>=%s)" (e1.clause_pp varPP) (e2.clause_pp varPP)

//
// Note that we dont have a "true" or "false" in formula
// We encode these as arithmetic formulae
//
let falsec = Le(Const(bigint.One),Const(bigint.Zero))
let truec = Le(Const(bigint.Zero),Const(bigint.Zero))

let conj fs =
    let mutable result = truec
    for f in fs do
        if result = truec then
            result <- f
        else if f <> truec then
            result <- And(result, f)
    result

let disj fs =
    let mutable result = falsec
    for f in fs do
        if result = falsec then
            result <- f
        else if f <> falsec then
            result <- Or(result, f)
    result

let negate x = Not(x)
let implies x y = Or(Not(x),y)
let iff x y = conj [implies x y ; implies y x]
let equal x y = conj [Le(x,y); Ge(x,y)]

//
// is_true_const and is_false_const are syntactic checks to see if an e is
// representing true.  We dont have a "True" or "False" constructor in the
// formula type, thus we use use the following predicates. Note that it would
// be VERY tempting to define
//       is_false_const = is_true_const o not,
// but that would be wrong, as is_true_const will return false when it hits
// variables, and other cases......
//

let is_false_formula c =
    match c with
    | Le(Const(k1),Const(k2)) -> not (k1<=k2)
    | Ge(Const(k1),Const(k2)) -> not (k1>=k2)
    | Lt(Const(k1),Const(k2)) -> not (k1<k2)
    | Gt(Const(k1),Const(k2)) -> not (k1>k2)
    | _ -> false

let rec is_true_formula c =
    match c with
    | Le(Const(k1),Const(k2)) -> k1<=k2
    | Ge(Const(k1),Const(k2)) -> k1>=k2
    | Lt(Const(k1),Const(k2)) -> k1<k2
    | Gt(Const(k1),Const(k2)) -> k1>k2
    | _ -> false

let rec simplify p =
    let simplify_step p =
          match p with
          | Not(Eq(a,b)) -> Or(Lt(a,b),Lt(b,a))
          | Eq(a,b) -> And(Le(a,b),Le(b,a))
          | Or(q,p) | Or(p,q) when is_false_formula q -> p
          | Or(q,p) when is_true_formula p || is_true_formula q -> truec
          | And(q,p) | And(p,q) when is_true_formula q -> p
          | And(q,p) when is_false_formula p || is_false_formula q -> falsec
          | Not(c) when is_true_formula c -> falsec
          | Not(c) when is_false_formula c -> truec
          | Not(Lt(a,b)) -> Ge(a,b)
          | Not(Le(a,b)) -> Gt(a,b)
          | Not(Gt(a,b)) -> Le(a,b)
          | Not(Ge(a,b)) -> Lt(a,b)
          | _ -> p
    match p with
    | Not(p)   -> simplify p |> negate |> simplify_step
    | And(p,q) -> conj [simplify p;simplify q] |> simplify_step
    | Or(p,q)  -> disj [simplify p;simplify q] |> simplify_step
    | _        -> p

let pp (f:formula) = f.pp

let rec contains_term f e =
    match e with
    | Not(e)     -> contains_term f e
    | And(e1,e2)
    | Or(e1,e2)  -> contains_term f e1 || contains_term f e2
    | Eq(e1,e2)
    | Lt(e1,e2)
    | Le(e1,e2)
    | Ge(e1,e2)
    | Gt(e1,e2) -> Term.contains f e1 || Term.contains f e2

let contains_nondet = contains_term (function Nondet -> true | _ -> false)

let rec freevars e =
    match e with
    | Not(e)     -> freevars e
    | And(e1,e2) -> Set.union (freevars e1) (freevars e2)
    | Or(e1,e2)  -> Set.union (freevars e1) (freevars e2)
    | Eq(e1,e2)  -> Set.union (Term.freevars e1) (Term.freevars e2)
    | Lt(e1,e2)  -> Set.union (Term.freevars e1) (Term.freevars e2)
    | Le(e1,e2)  -> Set.union (Term.freevars e1) (Term.freevars e2)
    | Ge(e1,e2)  -> Set.union (Term.freevars e1) (Term.freevars e2)
    | Gt(e1,e2)  -> Set.union (Term.freevars e1) (Term.freevars e2)

let freevars_list l =
    let accum s e = Set.union s (freevars e)
    List.fold accum Set.empty l

let rec subst env e =
   match e with
    | Not(e)     -> Not(subst env e)
    | And(e1,e2) -> And(subst env e1, subst env e2)
    | Or(e1,e2)  -> Or(subst env e1, subst env e2)
    | Eq(e1,e2)  -> Eq(Term.subst env e1, Term.subst env e2)
    | Lt(e1,e2)  -> Lt(Term.subst env e1, Term.subst env e2)
    | Le(e1,e2)  -> Le(Term.subst env e1, Term.subst env e2)
    | Ge(e1,e2)  -> Ge(Term.subst env e1, Term.subst env e2)
    | Gt(e1,e2)  -> Gt(Term.subst env e1, Term.subst env e2)

///
/// Alpha-renaming
///
let alpha m f = subst (m >> Var) f

///
/// Break a formulae into a list of its conjuncts
///
let split_conjunction f =
    // Note: we don't use obvious recursive version because it's potentially O(n^2)
    let rec split f accum =
        match f with
        | And (f1, f2) -> split f1 (split f2 accum)
        | _ -> f::accum
    split f []

///
/// Break a formulae into a list of its disjuncts
///
let split_disjunction f =
    let rec split f accum =
        match f with
        | Or (f1, f2) -> split f1 (split f2 accum)
        | _ -> f::accum
    split f []

///
/// Convert to DNF where atomic inequalities are of the form t1 <= t2
/// (they are supposed to be linear, but it is not checked here)
/// This is a preferred way of simplifying formulae. It's supposed to be
/// fast: O(size of result).
///
let rec polyhedra_dnf f =
    match f with
    | Le (_, _) -> f // for efficiency
    | Ge (t2, t1)
    | Not (Lt (t2, t1))
    | Not (Gt (t1, t2)) -> Le(t1, t2)

    | Lt (t1, t2)
    | Gt (t2, t1)
    | Not (Ge (t1, t2))
    | Not (Le (t2, t1)) -> Le (Term.add t1 (Term.constant 1), t2)

    | Eq (t1, t2) -> And (Le (t1, t2), Le (t2, t1))
    | Not (Eq (t1, t2)) -> polyhedra_dnf (Or (Lt (t1, t2), Lt (t2, t1)))

    | Or (f1, f2) -> Or (polyhedra_dnf f1, polyhedra_dnf f2)
    | And (f1, f2) ->
        let fs1 = polyhedra_dnf f1 |> split_disjunction
        let fs2 = polyhedra_dnf f2 |> split_disjunction
        [
            for d1 in fs1 do
                for d2 in fs2 do
                    yield And (d1, d2)
        ] |> List.reduce (fun a b -> Or (a, b))

    | Not (And (f1, f2)) -> polyhedra_dnf (Or (Not f1, Not f2))
    | Not (Or (f1, f2)) -> polyhedra_dnf (And (Not f1, Not f2))
    | Not (Not f1) -> polyhedra_dnf f1

// ----------------------------------------------------------------------------
// Decision procedure tools for formula, via the Z3 decision procedure

///
/// Convert T2 Formula to Z3 Formula
///
let rec z3 e =
    match e with
    | Not(e)       -> Z.mk_not (z3 e)
    | And(e1, e2)  -> Z.conj2 (z3 e1) (z3 e2)
    | Or(e1, e2)   -> Z.disj2 (z3 e1) (z3 e2)
    | Eq(e1, e2)   -> Z.eq (Term.z3 e1) (Term.z3 e2)
    | Lt(e1, e2)   -> Z.lt (Term.z3 e1) (Term.z3 e2)
    | Le(e1, e2)   -> Z.le (Term.z3 e1) (Term.z3 e2)
    | Gt(e1, e2)   -> Z.gt (Term.z3 e1) (Term.z3 e2)
    | Ge(e1, e2)   -> Z.ge (Term.z3 e1) (Term.z3 e2)

let print_sat_model q  =
    let vs = freevars q |> Set.map (fun v -> Term.var v |> Term.z3)
    let q_z3 = z3 q
    Z.print_sat_model [q_z3] vs

//
// Make memoized validity for the formula type, add reset function
// to global list of clear functions
//
let (clear1,valid_memoized) = memoize (z3 >> Z.valid)
Utils.add_clear clear1

///
/// Z3-based validity procedure for T2 formulae
///
let valid = valid_memoized

///
/// Entailment procedure for T2 formulae
///
let entails x y = implies x y |> valid

///
/// Satisfiability procedure for T2 formulae
///
let unsat x = entails x falsec

// ----------------------------------------------------------------------------
// IMPORTANT
// The encoding of termination, as well as the lazy disjunction optimization are encoded using
// commands, formulae and variables.  Variables with special names are used.  I'm trying to keep all of
// those details in one spot. This code is very brittle, as it may have subtle consequences elsewhere.
// Beware when modifying it!
//

let instrumentation_prefix = "__"

let const_prefix = instrumentation_prefix + "const_"
let const_var v =
    assert (v >= bigint.Zero)
    sprintf "%s%s" const_prefix (v.ToString())
let is_const_var (v:string) = v.StartsWith const_prefix
let get_const_from_constvar (v : System.String) =
    let withoutPrefix = v.[const_prefix.Length ..]
    bigint.Parse withoutPrefix

let copied_prefix = instrumentation_prefix + "copied_"
let copy_var state = Var.var(copied_prefix + string(state))
let is_copied_var (v:string) = v.StartsWith copied_prefix
let copied_assume k = (Ge(Term.var (copy_var k), Term.constant 1))
let not_copied_assume k = (Lt(Term.var (copy_var k), Term.constant 1))

let snapshot_prefix = instrumentation_prefix + "snapshot_"
let save_state_var v cp = Var.var(snapshot_prefix + string(cp) + "_" + v)
let is_saved_var (v:string) = v.StartsWith snapshot_prefix
let is_saved_var_for_cp (v:string) cp = v.StartsWith (snapshot_prefix + string(cp) + "_")
let extract_saved_var_name (v:string) = 
    let withoutPrefix = v.[snapshot_prefix.Length ..]
    withoutPrefix.[(withoutPrefix.IndexOf "_") + 1 ..]

let init_cond_prefix = instrumentation_prefix + "init_cond_at_"
let init_cond_var cp = Var.var init_cond_prefix + string(cp)
let is_init_cond_var (v:string) = v.StartsWith init_cond_prefix

let iter_prefix = instrumentation_prefix + "iters_"
let iters_var cp = Var.var iter_prefix + string(cp)
let is_iter_var (v:string) = v.StartsWith iter_prefix

let disj_prefix = instrumentation_prefix + "disjvar_"
let disj_var v = sprintf "%s%d" disj_prefix v
let is_disj_var (v:string) = v.StartsWith disj_prefix

let fair_proph_var = Var.var instrumentation_prefix + "fair_proph"
let fair_proph_old_var = Var.var instrumentation_prefix + "fair_proph_old"
let fair_term_var  = Var.var instrumentation_prefix + "fair_TERM"
let is_fair_var (v:string) =    v.StartsWith fair_proph_var 
                             || v.StartsWith fair_proph_old_var

let subcheck_return_prefix = instrumentation_prefix + "RET_VAL_" 
let subcheck_return_var id = Var.var subcheck_return_prefix + string(id)
let is_subcheck_return (v:string) = v.StartsWith subcheck_return_prefix
let contains_var_str (var:string) (v:Var.var) = v.Contains var

let is_instr_var (v:string) =  is_saved_var v
                            || is_copied_var v
                            || is_init_cond_var v
                            || is_iter_var v
                            || is_subcheck_return v

let contains_instr_var f = f |> freevars |> Seq.exists is_instr_var
let contains_fair_var f = f |> freevars |> Seq.exists is_fair_var
let contains_var f v = f |> freevars |> Seq.exists (contains_var_str v)

//
/// For __const_42 return Term.Const(42).
/// To use in subst
///
let eval_const_var v =
    if (is_const_var v) then
        Term.Const (get_const_from_constvar v)
    else
        Term.Var v

///
/// Raise this if we can't translate a Z3 formula back to Formula.formula
///
exception Z3_op_not_supported of string

///
/// Used internally. Since Z3 formulas do not distinguish between "formula"
///   and "term", it's convenient to have a union of these two types during
///   translation.
///
type fromZ3result = FromZ3term of term  |  FromZ3form of formula  |  FromZ3none

///
/// Get the term from the union
///
let z3t =
  function
     FromZ3term foo -> foo
     |  _ -> raise (Z3_op_not_supported("expecting a term, got formula"))

///
/// Get the formula from the union
///
let z3f =
  function
     FromZ3form foo -> foo
     |  _ -> raise (Z3_op_not_supported("expecting a formula, got term"))

///
/// Translate a Z3.Term to a Formula.formula.
///
let fromZ3 f =
   //
   // This is memoized to prevent an exponential recursion, as Z3 terms can have sharing.
   // Sadly, the result formula may also have sharing, which could lead to exponential traversals
   // down the line. We hope for the best.
   //
   let memo = new System.Collections.Generic.Dictionary<Microsoft.Z3.Expr,fromZ3result>()
   let rec get (f : Microsoft.Z3.Expr ) : fromZ3result =
     if memo.ContainsKey f
     then memo.[f]
     else
       let res = ref FromZ3none
       match f.ASTKind with
         |  Microsoft.Z3.Z3_ast_kind.Z3_NUMERAL_AST ->
               let numstr = f.ToString()
               res := FromZ3term(Term.Const(bigint.Parse numstr))
         |  Microsoft.Z3.Z3_ast_kind.Z3_APP_AST ->
               let args = f.Args
               let vcargs : fromZ3result array = Array.create args.Length FromZ3none;
               for i = 0 to args.Length - 1 do
                  vcargs.[i] <- get (args.[i]);
               done
               match f.FuncDecl.DeclKind with
                  | Microsoft.Z3.Z3_decl_kind.Z3_OP_ADD ->
                            if (Array.length vcargs = 0)
                            then res := FromZ3term(Term.constant 0)
                            else
                                res := vcargs.[0];
                                for k = 1 to vcargs.Length - 1 do
                                    res := FromZ3term(Term.Add(z3t(!res), z3t(vcargs.[k])))

                  | Microsoft.Z3.Z3_decl_kind.Z3_OP_DIV ->
                            raise (Z3_op_not_supported("Div"));
                  | Microsoft.Z3.Z3_decl_kind.Z3_OP_IDIV ->
                            raise (Z3_op_not_supported("IDiv"));
                  | Microsoft.Z3.Z3_decl_kind.Z3_OP_ITE ->
                            raise (Z3_op_not_supported("Ite"));
                  | Microsoft.Z3.Z3_decl_kind.Z3_OP_MOD ->
                            raise (Z3_op_not_supported("Mod"));
                  | Microsoft.Z3.Z3_decl_kind.Z3_OP_MUL ->
                            assert((Array.length vcargs) = 2);
                            res := FromZ3term(Term.Mul(z3t(vcargs.[0]), z3t(vcargs.[1])))
                  | Microsoft.Z3.Z3_decl_kind.Z3_OP_SELECT ->
                            raise (Z3_op_not_supported("Select"));
                  | Microsoft.Z3.Z3_decl_kind.Z3_OP_STORE ->
                            raise (Z3_op_not_supported("Store"));
                  | Microsoft.Z3.Z3_decl_kind.Z3_OP_SUB ->
                            assert((Array.length vcargs) = 2);
                            res := FromZ3term(Term.Sub(z3t(vcargs.[0]), z3t(vcargs.[1])))
                  | Microsoft.Z3.Z3_decl_kind.Z3_OP_UMINUS ->
                            assert((Array.length vcargs) = 1);
                            res := FromZ3term(Term.Sub(Term.constant 0, z3t(vcargs.[0])))
                  | Microsoft.Z3.Z3_decl_kind.Z3_OP_UNINTERPRETED ->
                            let name = f.FuncDecl.Name.ToString();
                            if (args.Length = 0)
                            then
                                res := FromZ3term(Term.Var(name))
                            else
                                raise (Z3_op_not_supported(name))
                  | Microsoft.Z3.Z3_decl_kind.Z3_OP_AND ->
                            if (Array.length vcargs) = 0 then
                                res := FromZ3form(Ge(Term.constant 0,Term.constant 0))
                            else
                                res := vcargs.[0]
                                for i = 1 to (Array.length vcargs)-1 do
                                   res := FromZ3form(And(z3f !res, z3f(vcargs.[i])))
                  | Microsoft.Z3.Z3_decl_kind.Z3_OP_EQ ->
                            assert((Array.length vcargs) = 2);
                            res := FromZ3form(Eq(z3t(vcargs.[0]), z3t(vcargs.[1])))
                  | Microsoft.Z3.Z3_decl_kind.Z3_OP_FALSE ->
                            res := FromZ3form(Ge(Term.constant 0,Term.constant 1))
                  | Microsoft.Z3.Z3_decl_kind.Z3_OP_GE ->
                            assert((Array.length vcargs) = 2);
                            res := FromZ3form(Ge(z3t(vcargs.[0]), z3t(vcargs.[1])))
                  | Microsoft.Z3.Z3_decl_kind.Z3_OP_GT ->
                            assert((Array.length vcargs) = 2);
                            res := FromZ3form(Gt(z3t(vcargs.[0]), z3t(vcargs.[1])))
                  | Microsoft.Z3.Z3_decl_kind.Z3_OP_IFF ->
                            assert((Array.length vcargs) = 2);
                            res := FromZ3form(Or(And(z3f(vcargs.[0]), z3f(vcargs.[1])),And(Not(z3f(vcargs.[0])), Not(z3f(vcargs.[1])))))
                  | Microsoft.Z3.Z3_decl_kind.Z3_OP_IMPLIES ->
                            assert((Array.length vcargs) = 2);
                            res := FromZ3form(Or(Not(z3f(vcargs.[0])), z3f(vcargs.[1])))
                  | Microsoft.Z3.Z3_decl_kind.Z3_OP_LE ->
                            assert((Array.length vcargs) = 2);
                            res := FromZ3form(Le(z3t(vcargs.[0]), z3t(vcargs.[1])))
                  | Microsoft.Z3.Z3_decl_kind.Z3_OP_LT ->
                            assert((Array.length vcargs) = 2);
                            res := FromZ3form(Lt(z3t(vcargs.[0]), z3t(vcargs.[1])))
                  | Microsoft.Z3.Z3_decl_kind.Z3_OP_NOT ->
                            assert((Array.length vcargs) = 1);
                            res := FromZ3form(Not(z3f(vcargs.[0])))
                  | Microsoft.Z3.Z3_decl_kind.Z3_OP_OR ->
                            if (Array.length vcargs) = 0 then
                                res := FromZ3form(Ge(Term.constant 0,Term.constant 1))
                            else
                                res := vcargs.[0]
                                for i = 1 to (Array.length vcargs)-1 do
                                   res := FromZ3form(Or(z3f !res, z3f(vcargs.[i])))
                  | Microsoft.Z3.Z3_decl_kind.Z3_OP_TRUE ->
                            res := FromZ3form(Ge(Term.constant 0,Term.constant 0))
                  | x ->
                            raise (Z3_op_not_supported(x.ToString()))

         | x ->
                raise (Z3_op_not_supported(x.ToString()))

       memo.[f] <- !res
       !res
   z3f(get f)
