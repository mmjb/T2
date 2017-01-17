////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      SparseLinear.fs
//
//  Abstract:
//
//      Sparse linear matrix/vectors
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


module Microsoft.Research.T2.SparseLinear

open Utils

///
/// special 'variable' name to represent constants
///
let ONE = "1"

//
// keys are variable names
// "1" corresponds to constant term
//
type LinearTerm = Map<Var.var, bigint>

// When treated as inequalities, terms are interpreted as t<=0

// For efficient implementation of addition it's important that Linear term
// is Map (immutable structure that supports sharing) as opposed to Dictionary.

let linear_term_to_term (t:LinearTerm) =
    let mutable summands = []

    for KeyValue(v, coeff) in t do
        if coeff <> bigint.Zero then
            let z3Coeff = Term.Const coeff
            if v = ONE then
                summands <- z3Coeff :: summands
            else
                if coeff = bigint.One then
                    summands <- (Term.var v) :: summands
                else
                    summands <- (Term.Mul (z3Coeff, Term.var v)) :: summands

    if summands.IsEmpty then
        Term.Const bigint.Zero
    else
        let first = List.head summands
        List.fold (fun x y -> Term.Add(x, y)) first (List.tail summands)

let alpha (varRenamer : Var.var -> Var.var) (t : LinearTerm) =
    t |> Seq.map (function KeyValue(v, coeff) -> ((if v = ONE then v else varRenamer v), coeff)) |> Map.ofSeq

let linearTermToString lt =
    lt
    |> Seq.map
        (function KeyValue(v, coeff) ->
                    let vString = if v = ONE then "" else "*" + v
                    sprintf "%s%s" (coeff.ToString()) vString)
    |> String.concat " + "

let remove_zeros (t:LinearTerm) : LinearTerm =
    Map.filter (fun _ coeff -> coeff <> bigint.Zero) t

let as_constant (t:LinearTerm) =
    let rest = t.Remove ONE
    if rest.IsEmpty then
        Some (t.FindWithDefault ONE bigint.Zero)
    else
        None

let is_always_nonpositive (t:LinearTerm) =
    match as_constant t with
    | Some c -> c <= bigint.Zero
    | None -> false

let is_always_positive (t:LinearTerm) =
    match as_constant t with
    | Some c -> c > bigint.Zero
    | None -> false

let mul_by_const (t:LinearTerm) c : LinearTerm =
    if c = bigint.Zero then
        Map.empty
    else
        Map.map (fun _ k -> c*k) t

let rec add (t1: LinearTerm) (t2: LinearTerm) : LinearTerm =
    if t1.Count < t2.Count then
        add t2 t1
    else
        let mutable result = t1
        for KeyValue(var, coeff) in t2 do
            let new_coeff = coeff + result.FindWithDefault var bigint.Zero
            if new_coeff <> bigint.Zero then
                result <- result.Add(var, new_coeff)
            else
                result <- result.Remove var
        result

let sub t1 t2 = add t1 (mul_by_const t2 bigint.MinusOne)

///
/// divide by gcd
///
let simplify_as_inequality (t:LinearTerm) : LinearTerm =
    let t = remove_zeros t
    let g = Map.fold (fun g _ k -> gcd g k) bigint.Zero t

    if g = bigint.Zero then
         Map.empty
    else if g = bigint.One then
        t
    else
        assert (g > bigint.Zero)
        Map.map (fun _ k -> k/g) t

///
/// Simplify conjunction of inequalities represented by terms (as t <= 0)
///
let simplify_as_inequalities terms : LinearTerm list =
    if List.exists is_always_positive terms then
        // conjunction contains false; return singular false
        [Map.empty.Add (ONE, bigint.One)]
    else
        terms
        |> List.map simplify_as_inequality
        |> List.filter (is_always_nonpositive >> not)
        |> Set.ofList
        |> Set.toList

exception Nonlinear of Term.term

let rec term_to_linear_term t : LinearTerm =
    let rec singleconst t = //MEB
        match t with
        | Term.Const c -> Term.Const c
        | Term.Var v -> Term.Var v
        | Term.Neg (Term.Const c) -> Term.Const (-c)
        | Term.Add (Term.Const c, Term.Const d) -> Term.Const (c+d)
        | Term.Sub (Term.Const c, Term.Const d) -> Term.Const (c-d)
        | Term.Mul (Term.Const c, Term.Const d) -> Term.Const (c*d)
        | Term.Neg tt -> Term.Neg (singleconst tt)
        | Term.Add (t1, t2) -> Term.Add (singleconst t1, singleconst t2)
        | Term.Sub (t1, t2) -> Term.Sub (singleconst t1, singleconst t2)
        | Term.Mul (t1, t2) -> Term.Mul (singleconst t1, singleconst t2)
        | _ -> raise (Nonlinear t)
    match singleconst t with
    | Term.Const c -> Map.empty.Add(ONE, c)
    | Term.Var v ->
        assert (v <> ONE)
        Map.empty.Add(v, bigint.One)
    | Term.Neg tt ->  mul_by_const (term_to_linear_term tt) bigint.MinusOne
    | Term.Add (t1, t2) -> add (term_to_linear_term t1)
                                (term_to_linear_term t2)
    | Term.Sub (t1, t2) -> sub (term_to_linear_term t1)
                                (term_to_linear_term t2)
    | Term.Mul (Term.Add (t1, t2), Term.Const c) -> term_to_linear_term (Term.Add (Term.Mul (Term.Const c, t1), Term.Mul (Term.Const c, t2)))
    | Term.Mul (Term.Const c, Term.Add (t1, t2)) -> term_to_linear_term (Term.Add (Term.Mul (Term.Const c, t1), Term.Mul (Term.Const c, t2)))
    | Term.Mul (Term.Sub (t1, t2), Term.Const c) -> term_to_linear_term (Term.Sub (Term.Mul (Term.Const c, t1), Term.Mul (Term.Const c, t2)))
    | Term.Mul (Term.Const c, Term.Sub (t1, t2)) -> term_to_linear_term (Term.Sub (Term.Mul (Term.Const c, t1), Term.Mul (Term.Const c, t2)))
    | Term.Mul (tt, Term.Const c) // mloop -> mul_by_const (term_to_linear_term tt) c
    | Term.Mul (Term.Const c, tt) -> mul_by_const (term_to_linear_term tt) c
    | _ -> raise (Nonlinear t)

///
/// Fourier-Motzkin elimination.
/// Terms are understood as system of inequalities t <= 0.
/// (since we can't represent congruence module constant, it's
/// imprecise (consider elimination of y from x <= 2*y && x >= 2*y))
///
let eliminate_var var (terms : LinearTerm list) =
    assert (var <> ONE)

    let mutable positive = Set.empty
    let mutable negative = Set.empty
    let mutable others = Set.empty

    for t in terms do
        let coeff = t.FindWithDefault var bigint.Zero
        if  coeff > bigint.Zero then
            positive <- Set.add t positive
        else if coeff < bigint.Zero then
            negative <- Set.add t negative
        else
            others <- Set.add t others

    let combine (neg:LinearTerm) (pos:LinearTerm) =
        let neg_coeff = neg.[var]
        assert (neg_coeff < bigint.Zero)
        let pos_coeff = pos.[var]
        assert (pos_coeff > bigint.Zero)

        let g = gcd neg_coeff pos_coeff

        let t = add (mul_by_const neg (pos_coeff/g)) (mul_by_const pos ((-neg_coeff)/g))
        let t = simplify_as_inequality t

        assert (t.FindWithDefault var bigint.Zero = bigint.Zero)

        t

    //
    // make them immutable to capture in list comprehension
    //
    let positive = positive
    let negative = negative

    //let pos_len = List.length positive
    //let neg_len = List.length negative
    let v =
      (List.ofSeq others) @ [
        for pos in positive do
            for neg in negative do
                (!Utils.check_timeout)()
                yield combine neg pos
      ]
    v

let combine_with_z3_terms (A: LinearTerm list) (coeffs: Microsoft.Z3.ArithExpr list) =
    Map.Concat [for a, coeff in List.zip A coeffs ->
                Map.map (fun _ k -> Z.mul (Z.constant k) coeff) a]
    |> Map.map (fun _ terms -> List.fold Z.add (Z.constant bigint.Zero) terms)

///
/// ensure that term is linear and simplify it a little bit.
/// If it's not linear, Nonlinear exception is thrown
///
let term_as_linear = term_to_linear_term >> linear_term_to_term

let toCeta (writer : System.Xml.XmlWriter) (varWriter : System.Xml.XmlWriter -> Var.var -> unit) (t : LinearTerm) =
    if Map.isEmpty t then
        writer.WriteElementString ("constant", "0")
    else
        writer.WriteStartElement "sum"

        match Map.tryFind ONE t with
        | Some constant ->
            writer.WriteElementString ("constant", string constant)
        | _ -> ()

        Map.iter
            (fun var value ->
                if var <> ONE && value <> bigint.Zero then
                    if value = bigint.One then
                        varWriter writer var
                    else
                        writer.WriteStartElement "product"
                        writer.WriteElementString ("constant", string value)
                        varWriter writer var
                        writer.WriteEndElement ())
            t
        writer.WriteEndElement () //end sum

let private getFarkasCoefficients (pres : LinearTerm seq) (post : LinearTerm) : (bigint list) =
    let presNLambdas : (LinearTerm * Microsoft.Z3.ArithExpr) list = [ for pre in pres do yield (pre, upcast Z.fresh_var()) ]
    let allVars = Set.unionMany (Seq.map (fun (t : LinearTerm) -> Set.ofSeq t.Keys) (Seq.append (Seq.singleton post) pres))

    //For t.[v] the v-coefficient of t:
    //   (\bigwedge_{t \in pres} t <= 0) -> post <= 0
    //        <=>
    //   \bigwedge_{v \in (allVars - ONE)} \sum_{t \in pres} lambda_t * t.[v] = post.[v]
    //   && \sum_{t \in pres} lambda_t * t.[ONE] <= post.[ONE]
    //   && \bigwedge_{t \in pres} lambda_t >= 0
    let ZERO = Z.constant bigint.Zero
    let lambdasPos =
        presNLambdas
        |> List.map (fun (_, lambda) -> Z.ge lambda ZERO)
        |> Z.conj
    let farkasConstraints =
        Seq.fold
            (fun partialConstraint v ->
                let preCoeffSum =
                    List.fold
                        (fun partialSum (pre, lambda) ->
                            match Map.tryFind v pre with
                            | Some coeff -> Z.add partialSum (Z.mul lambda (Z.constant coeff))
                            | None -> partialSum)
                        (Z.constant bigint.Zero) presNLambdas
                let postCoeff = Z.constant (Map.findWithDefault v bigint.Zero post)
                let constr =
                    if v = ONE then
                        Z.ge preCoeffSum postCoeff
                    else
                        Z.eq preCoeffSum postCoeff
                Z.conj2 partialConstraint constr)
            lambdasPos allVars
    match Z.solve [farkasConstraints] with
    | None ->
        printfn "Looking for Farkas coefficients for this:"
        Seq.iter (fun (t, _) -> printfn "  %s <= 0" (linearTermToString t)) presNLambdas
        printfn " ==> %s <= 0" (linearTermToString post)
        failwith "Trying to get Farkas coefficients for implication that doesn't hold!"
    | Some model ->
        List.map (fun (_, lambda) ->  Z.get_model_int model lambda) presNLambdas

let writeCeTALinearImplicationHints (writer : System.Xml.XmlWriter) (pres : LinearTerm list) (post : LinearTerm) =
    let farkasCoeffs = getFarkasCoefficients pres post
    writer.WriteStartElement "linearImplicationHint"
    writer.WriteStartElement "linearCombination"
    List.iter
        (fun (i : bigint) ->
            writer.WriteStartElement "constant"
            writer.WriteValue (int64 i)
            writer.WriteEndElement ()) //constant end
        farkasCoeffs
    writer.WriteEndElement () //linearCombination end
    writer.WriteEndElement () //linearImplicationHint end

let linear_term_to_z3 (t : LinearTerm) =
    t
    |> Map.toSeq
    |> Seq.fold
        (fun res (var, coeff) ->
            let summand =
                if var = ONE then 
                    Z.constant coeff
                else
                    Z.mul (Z.constant coeff) (Z.var var)
            Z.add res summand)
            (Z.constantInt 0)

let le_linear_term_to_z3 (t : LinearTerm) =
    Z.le (linear_term_to_z3 t) (Z.constantInt 0)

let le_linear_terms_to_z3 (ts : LinearTerm list) =
    Z.conj (ts |> List.map le_linear_term_to_z3)