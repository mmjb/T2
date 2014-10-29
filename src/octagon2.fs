////////////////////////////////////////////////////////////////////////////////
//
//  Module Name:
//
//      Octagon
//
//  Abstract:
//
//      Octagon abstract domain
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


module Octagon2

open IIntAbsDom
open Var
open Utils

open SparseLinear
open Checked

///
/// div that rounds down even for negative x
///
let floor_div (x : bigint) (y : bigint) =
    assert (y > bigint.Zero)
    if x >= bigint.Zero then
        x/y
    else
        let rem = ref bigint.Zero
        let div = bigint.DivRem (x, y, rem)
        div + !rem //!rem is always negative, as x is, so this is rounding down

[<CustomEquality;CustomComparison>]
type octint =
    | Const of bigint
    | POSINF

    static member (+) (a, b) =
        match (a, b) with
        | (POSINF, _) -> POSINF
        | (_, POSINF) -> POSINF
        | (Const x, Const y) -> Const (x + y)

    static member (*) (a, b) =
        match (a, b) with
        | (POSINF, _) -> POSINF
        | (_, POSINF) -> POSINF
        | (Const x, Const y) -> Const (x * y)

    static member (/) (a, b) =
        match (a, b) with
        | (_, POSINF) -> 
            assert (false) // this doesn't make a whole lot of sense...
            POSINF
        | (_, Const c) when c = bigint.Zero -> 
            raise (new System.DivideByZeroException())
        | (POSINF, _) -> POSINF
        | (Const x, Const y) -> Const (x + y)

    member self.floor_half = 
        match self with
        | POSINF -> POSINF
        | Const c -> Const (floor_div c (bigint 2))

    interface System.IComparable with
        member self.CompareTo (other : obj) =
            match other with
            | :? octint as other ->
                match (self, other) with
                | (POSINF, POSINF) -> 0
                | (POSINF, _) -> 1
                | (_, POSINF) -> -1
                | (Const selfC, Const otherC) -> selfC.CompareTo(otherC)
            | _ -> 1
            
    override self.Equals other =
        ((self :> System.IComparable).CompareTo other) = 0
    override self.GetHashCode () =
        match self with
        | POSINF -> 1009
        | Const c -> c.GetHashCode()

let widening_thresholds = [Const bigint.Zero; POSINF]

///
/// internal Oct invariants checks; somewhat expensive
///
let sanity_check = false

[<StructuredFormatDisplayAttribute("Oct({pp})")>]
type Oct =
    private {
        mutable vars : Map<var, int>;

        ///
        /// dbm[2*x_index, 2*y_index] = c means that x-y <= c;
        /// 2*x_index+1 corresponds to (-x);
        /// dbm[0, 0] < 0 is used as emptiness flag;
        ///
        mutable dbm : octint [,];
    }

    member self.pp =
        self.to_formula

    static member create =
        { vars = Map.empty; dbm = Array2D.create 1 1 POSINF }

    static member from_formula f =
        let result = Oct.create
        result.assume f
        result

    ///
    /// number of variables (not the size of dbm!)
    ///
    member private self.size =
        self.vars.Count

    member private self.has_var var =
        self.vars.ContainsKey var

    ///
    /// return index i for the var (if it's not present in octagon, add it)
    /// (2*i is for v+,
    ///  2*i+1 is for v-)
    ///
    member private self.var_index v =
        match self.vars.TryFind v with
        | Some i -> i
        | None ->
            let i = self.size
            self.resize (i+1)
            self.vars <- self.vars.Add (v, i)
            i

    ///
    /// Projection
    ///
    member private self.delete_var v =
        match self.vars.TryFind v with
        | None -> assert(false)
        | Some idx ->
            if self.is_empty then
                ()
            else

            let max_var, max_idx = seq {for kv in self.vars -> (kv.Key, kv.Value)}
                                 |> Seq.maxBy snd

            //
            // move var with maximum index to the vacant place
            //
            let n = self.size
            for i in 0..2*n-1 do
                self.dbm.[idx*2, i] <- self.dbm.[max_idx*2, i]
                self.dbm.[idx*2+1, i] <- self.dbm.[max_idx*2+1, i]
            for i in 0..2*n-3 do
                self.dbm.[i, idx*2] <- self.dbm.[i, max_idx*2]
                self.dbm.[i, idx*2+1] <- self.dbm.[i, max_idx*2+1]

            for i in 0..2*n-1 do
                self.dbm.[i, max_idx*2] <- POSINF
                self.dbm.[i, max_idx*2+1] <- POSINF
                self.dbm.[max_idx*2, i] <- POSINF
                self.dbm.[max_idx*2+1, i] <- POSINF
            self.dbm.[2*max_idx, 2*max_idx] <- Const bigint.Zero
            self.dbm.[2*max_idx+1, 2*max_idx+1] <- Const bigint.Zero

            self.vars <- (self.vars.Add (max_var, idx)).Remove v

    member self.havoc var =
        if self.is_empty then
            ()
        else
        // it could be done a little bit more efficiently, without deletion
        if self.has_var var then
            self.delete_var var
        self.var_index var |> ignore

    member private self.resize new_size =
        assert (new_size > self.size)

        if 2*new_size > self.dbm.GetLength(0) then
            // TODO.v2: allocate more space in advance
            let q = Array2D.create (2*new_size) (2*new_size) POSINF
            for i in 0..2*self.size-1 do
                for j in 0..2*self.size-1 do
                    q.[i, j] <- self.dbm.[i, j]
            q.[0, 0] <- self.dbm.[0, 0] // copy emptiness flag even if we have 0 vars
            self.dbm <- q

        for i in 2*self.size..2*new_size-1 do
            self.dbm.[i, i] <- Const bigint.Zero

    ///
    /// check coherence and some other internal invariants
    ///
    member self.check =
        if self.is_empty then
            ()
        else

        let indices = [for KeyValue(_, v) in self.vars -> v] |> List.sort
        assert (indices = [0..self.vars.Count-1])

        let n = self.size
        for i in 0..2*n-1 do
            for j in 0..2*n-1 do
                assert (self.dbm.[i, j] = self.dbm.[j^^^1, i^^^1])

        for i in 0..2*n-1 do
            assert (self.dbm.[i, i] = Const bigint.Zero)

    /// Test is precise only immediately after tight_closure.
    /// Otherwise false negatives are possible.
    member self.is_empty =
        self.dbm.[0, 0] < Const bigint.Zero

    member private self.basic_make_false =
        self.dbm.[0, 0] <- Const bigint.MinusOne

    member self.tight_closure =
        // see
        // "An Improved Tight Closure Algorithm for Integer Octagonal Constraints"
        // by Roberto Bagnara, Patricia M. Hill, and Enea Zaffanella

        if self.is_empty then
            ()
        else

        let old_formula = if sanity_check then self.to_formula else Formula.truec

        let n = self.size

        // Initialization
        for i in 0..2*n-1 do
            assert (self.dbm.[i, i] = Const bigint.Zero)

        // Floyd-Warhsall for computing the closure
        for k in 0..2*n-1 do
            for i in 0..2*n-1 do
                if self.dbm.[i, k] <> POSINF then
                    for j in 0..2*n-1 do
                        if self.dbm.[k, j] <> POSINF then
                            self.dbm.[i, j] <- min
                                self.dbm.[i, j]
                                (self.dbm.[i, k] + self.dbm.[k, j])

        // Check for Q-consistency
        for i in 0..2*n-1 do
            if self.dbm.[i, i] < Const bigint.Zero then
                self.dbm.[0, 0] <- Const bigint.MinusOne

        // Tightening
        for i in 0..2*n-1 do
            if self.dbm.[i, i^^^1] <> POSINF then
                self.dbm.[i, i^^^1] <- self.dbm.[i, i^^^1].floor_half * (Const (bigint 2))

        // Check for Z-consistency
        for i in 0..2..2*n-2 do
            let a = self.dbm.[i, i^^^1]
            let b = self.dbm.[i^^^1, i]
            if a <> POSINF && b <> POSINF && a+b < Const bigint.Zero then
                self.dbm.[0, 0] <- Const bigint.MinusOne

        // Strong coherence
        for i in 0..2*n-1 do
            for j in 0..2*n-1 do
                let a = self.dbm.[i, i^^^1]
                let b = self.dbm.[j^^^1, j]
                if a <> POSINF && b <> POSINF then
                    self.dbm.[i, j] <- min
                        self.dbm.[i, j]
                        (a.floor_half + b.floor_half)

        if sanity_check then
            let formula = self.to_formula
            assert (Formula.entails old_formula formula)
            assert (Formula.entails formula old_formula)

    member private self.basic_assume_ineq i j d =
        assert (d <> POSINF)
        assert (i <> j)

        self.dbm.[i, j] <- min
            self.dbm.[i, j]
            d
        self.dbm.[j^^^1, i^^^1] <- min
            self.dbm.[j^^^1, i^^^1]
            d

    member private self.basic_assume_eq idx1 idx2 =
        // Better than two basic_assume_ineq because does not require tight_closure.
        // This property is used in 'assign'
        let n = self.size

        for i in 0..2*n-1 do
            let d = min self.dbm.[idx1, i] self.dbm.[idx2, i]
            self.dbm.[idx1, i] <- d
            self.dbm.[idx2, i] <- d

            let d = min self.dbm.[idx1^^^1, i] self.dbm.[idx2^^^1, i]
            self.dbm.[idx1^^^1, i] <- d
            self.dbm.[idx2^^^1, i] <- d

        for i in 0..2*n-1 do
            let d = min self.dbm.[i, idx1] self.dbm.[i, idx2]
            self.dbm.[i, idx1] <- d
            self.dbm.[i, idx2] <- d

            let d = min self.dbm.[i, idx1^^^1] self.dbm.[i, idx2^^^1]
            self.dbm.[i, idx1^^^1] <- d
            self.dbm.[i, idx2^^^1] <- d

    member self.clone =
        if sanity_check then
            self.check

        {vars = self.vars; dbm = self.dbm.Clone() :?> octint[,] }

    /// inplace union
    member self.union (other:Oct) =
        if sanity_check then
            self.check
            other.check

        if other.is_empty then
            ()
        elif self.is_empty then
            let t = other.clone
            self.vars <- t.vars
            self.dbm <- t.dbm
        else

        //for v in map_keys other.vars do
        //    self.var_index v |> ignore
        for KeyValue(u, i) in other.vars do
            let i1 = self.var_index u
            for KeyValue(v, j) in other.vars do
                let j1 = self.var_index v
                for i' in 0..1 do
                    for j' in 0..1 do
                        self.dbm.[2*i1+i', 2*j1+j'] <- max
                            self.dbm.[2*i1+i', 2*j1+j']
                            other.dbm.[2*i+i', 2*j+j']

    /// inplace widen;
    /// return true if widening changed the octagon
    member self.widen (other:Oct) =
        if sanity_check then
            self.check
            other.check

        if other.is_empty then
            false
        elif self.is_empty then
            assert (not other.is_empty)
            let t = other.clone
            self.vars <- t.vars
            self.dbm <- t.dbm
            true
        else

        let mutable result = false
        for KeyValue(u, i) in other.vars do
            let i1 = self.var_index u
            for KeyValue(v, j) in other.vars do
                let j1 = self.var_index v
                for i' in 0..1 do
                    for j' in 0..1 do
                        let o = other.dbm.[2*i+i', 2*j+j']
                        if self.dbm.[2*i1+i', 2*j1+j'] < o then
                            result <- true
                            let x = List.filter ((<=)o) widening_thresholds |> List.min
                            assert (self.dbm.[2*i1+i', 2*j1+j'] < x)
                            self.dbm.[2*i1+i', 2*j1+j'] <- x
        result

    /// return conjunction of (linear_termt1 <= linear_term2)
    member self.to_formula_filtered filter =
        self.check
        if self.is_empty then
            Formula.falsec
        else

        seq {
            for KeyValue(u, i) in self.vars do
                if not(filter u) then () else
                let u = Term.var (var u)

                let c = self.dbm.[2*i+1, 2*i]
                match c with
                | POSINF -> ()
                | Const c -> yield Formula.Le (Term.Const -(floor_div c (bigint 2)), u)

                let c = self.dbm.[2*i, 2*i+1]
                match c with
                | POSINF -> ()
                | Const c -> yield Formula.Le (u, Term.Const (floor_div c (bigint 2)))

            for KeyValue(u, i) in self.vars do
                if not(filter u) then () else
                let u = Term.var (var u)
                for KeyValue(v, j) in self.vars do
                    let v = Term.var (var v)

                    if i < j then
                        let c = self.dbm.[2*i, 2*j]
                        match c with
                        | POSINF -> ()
                        | Const c -> yield Formula.Le (Term.sub u v, Term.Const c)

                        let c = self.dbm.[2*i+1, 2*j+1]
                        match c with
                        | POSINF -> ()
                        | Const c -> yield Formula.Le (Term.sub v u, Term.Const c)

                        let c = self.dbm.[2*i, 2*j+1]
                        match c with
                        | POSINF -> ()
                        | Const c -> yield Formula.Le (Term.add u v, Term.Const c)

                        let c = self.dbm.[2*i+1, 2*j]
                        match c with
                        | POSINF -> ()
                        | Const c -> yield Formula.Le (Term.Const -c, Term.add u v)

        } |> Formula.conj
    member self.to_formula = self.to_formula_filtered (fun _ -> true)

    member private self.upper_bound (t:LinearTerm) =
        // TODO.v2: make more precise by taking into account pairs,
        // e.g. ub(x-y+z) = ub(x-y)+ub(z)

        let t = remove_zeros t

        let mutable result = Const bigint.Zero
        for KeyValue(v, coeff) in t do
            if result <> POSINF then
                if v = ONE then
                    result <- result + Const coeff
                elif not <| self.has_var v then
                    result <- POSINF
                else
                    let idx = self.var_index v
                    if coeff > bigint.Zero then
                        let d = self.dbm.[2*idx, 2*idx+1]
                        if d = POSINF then
                            result <- POSINF
                        else
                            result <- result + ((Const coeff) * (d.floor_half))
                    else
                        let d = self.dbm.[2*idx+1, 2*idx]
                        if d = POSINF then
                            result <- POSINF
                        else
                            result <- result + ((Const -coeff) * (d.floor_half))

        result

    /// does not introduce variables that are not already in the octagon;
    /// potentially O(n^3) in the size of formula
    member private self.conservative_assume f =
        if self.is_empty then
            ()
        else

        let initial_oct_formula = if sanity_check then self.to_formula else Formula.truec

        let ts = formula_to_linear_terms f |> simplify_as_inequalities

        for t in ts do
            let neg_t = mul_by_const t (bigint.MinusOne)
            let u = t.Remove ONE // uniform part

            if u.IsEmpty then
                let c = t.FindWithDefault ONE bigint.Zero
                if c > bigint.Zero then
                    self.basic_make_false

            elif not <| Seq.forall self.has_var u.Keys then
                // we can't get any information from this
                // inequality because it involves unknown var
                ()

            elif u.Count = 1 then
                for KeyValue(v, coeff) in u do
                    let idx = self.var_index v
                    let ub = neg_t.Remove v |> self.upper_bound
                    match ub with
                    | POSINF -> ()
                    | Const ub ->
                        let ub = floor_div ub (abs coeff)
                        if coeff > bigint.Zero then
                            self.basic_assume_ineq (2*idx) (2*idx+1) (Const ((bigint 2)*ub))
                        else
                            self.basic_assume_ineq (2*idx+1) (2*idx) (Const ((bigint 2)*ub))
            else

            // suppose we have ineq
            //   10*v1+13*v2+zzz <= 0
            // We transform it to
            //   10*(v1+v2) <= -zzz-3*v2,
            // and set ub(-zzz-3*v)/10 as upper bound for v1+v2.
            // Then we do the same with representation
            //   13*(v1+v2) <= -zzz+3*v1

            for KeyValue(v1, coeff1) in u do
                for KeyValue(v2, coeff2) in u do
                    let idx1 = self.var_index v1
                    let idx2 = self.var_index v2
                    if idx1 < idx2 then // we only consider each pair of variables once
                        let mt = [(v1, bigint (sign coeff1)); (v2, bigint (sign coeff2))]
                                    |> Map.ofList
                        let ks = [abs(coeff1); abs(coeff2)]
                                    |> Set.ofList // in case these two coeffs are the same
                        for k in ks do
                            let right = add neg_t (mul_by_const mt k)
                            let ub = self.upper_bound right
                            match ub with
                            | POSINF -> ()
                            | Const ub ->
                                let ub = floor_div ub k
                                match (sign coeff1, sign coeff2) with
                                | (1, -1) ->
                                    self.basic_assume_ineq (2*idx1) (2*idx2) (Const ub)
                                | (1, 1) ->
                                    self.basic_assume_ineq (2*idx1) (2*idx2+1) (Const ub)
                                | (-1, -1) ->
                                    self.basic_assume_ineq (2*idx1+1) (2*idx2) (Const ub)
                                | (-1, 1) ->
                                    self.basic_assume_ineq (2*idx1+1) (2*idx2+1) (Const ub)
                                | _ -> die()

        if sanity_check then
            let oct_formula = self.to_formula
            assert (Formula.entails (Formula.conj [initial_oct_formula; f]) oct_formula)

    /// may introduce new variables from f to octagon
    member self.assume f =
        for v in Formula.freevars f do
            self.var_index v |> ignore
        self.conservative_assume f

    /// performs tight closure inside, so it's expensive;
    /// introduces all variables mentioned in term (and of course var)
    /// to the octagon if not present already;
    member self.assign var term =

        //
        // Global timeout check
        //
        (!Utils.check_timeout)()

        if self.is_empty then
            ()
        elif Term.contains_nondet term then
            self.havoc var
        else

        // TODO.v2: special case when term does not contain var, so
        // we don't have to introduce old_var

        let old = "____octagon_old_var___"
        assert (not <| self.has_var old)

        let idx = self.var_index var
        let old_idx = self.var_index old

        self.basic_assume_eq (2*idx) (2*old_idx)

        self.havoc var

        let make_old v = if v = var then old else v
        self.assume (Formula.equal (Term.var var) (Term.alpha make_old term))

        self.tight_closure

        self.delete_var old

    interface IIntAbsDom with
        member self.tight_closure = self.tight_closure
        member self.clone = self.clone :> IIntAbsDom
        member self.widen other = self.widen (other :?> Oct)
        member self.assign var term = self.assign var term
        member self.assume f = self.assume f
        member self.to_formula = self.to_formula
        member self.to_formula_filtered filter = self.to_formula_filtered filter

let register_tests() =

    let equiv f1 f2 =
        Formula.entails f1 f2 && Formula.entails f2 f1

    let x = Term.var "x"
    let y = Term.var "y"
    let z = Term.var "z"

    Test.register_test true (fun () ->
        let oct = Oct.create
        oct.assume Formula.falsec
        equiv oct.to_formula Formula.falsec
    )

    Test.register_test true (fun () ->
        let oct = Oct.create
        oct.assume (Formula.Gt(x, y))
        oct.assume (Formula.Gt(y, z))
        oct.assume (Formula.Gt(z, x))
        oct.tight_closure
        oct.is_empty
    )

    Test.register_test true (fun () ->
        let oct = Oct.create
        oct.assume (Formula.Ge(x, y))
        oct.assume (Formula.Ge(y, z))
        oct.assume (Formula.Ge(z, x))
        oct.tight_closure
        equiv oct.to_formula (Formula.conj [Formula.Eq(x, y); Formula.Eq(y, z)])
    )

    Test.register_test true (fun () ->
        let oct = Oct.create
        oct.assume (Formula.Ge(x, Term.constant 10))
        oct.assign "x" (Term.add x (Term.constant 1))
        oct.assign "y" (Term.sub (Term.constant 42) x)

        let res =
            [
                Formula.Ge(x, Term.constant 11);
                Formula.Eq(Term.add x y, Term.constant 42)
            ] |> Formula.conj

        equiv oct.to_formula res
    )

    Test.register_test true (fun () ->
        let oct = Oct.create
        oct.assume (Formula.Lt(x, Term.constant 10))
        oct.assume (Formula.Le(z, Term.constant 1))
        oct.assign "x" (Term.add x z)
        oct.assign "y" (Term.sub (Term.constant 42) x)
        oct.assign "x" Term.nondet
        oct.havoc "z"

        equiv oct.to_formula (Formula.Gt(y, Term.constant 31))
    )

    for sx in [1; -1] do
        for sy in [1; -1] do
            for sz in [1; -1] do
                // try with all possible combinations of signs
                // to catch potential errors in copypasted indexing code
                let x = Term.mul (Term.var "x") (Term.constant sx)
                let y = if sy = 1 then Term.var "y" else Term.sub (Term.constant 0) (Term.var "y")
                let z = Term.mul (Term.var "z") (Term.constant sz)

                Test.register_test true (fun () ->
                    let oct = Oct.create
                    oct.assume (Formula.Ge (x, Term.constant 1))
                    oct.assume (Formula.Ge (y, Term.constant 2))
                    oct.assume (Formula.Ge (z, Term.constant 3))
                    oct.assume (
                        Formula.Le(
                            Term.add
                                (Term.add (Term.mul x (Term.constant 13))
                                          (Term.mul y (Term.constant 15)))
                                z,
                            Term.constant 100))

                    let res =
                        [
                            Formula.Ge (x, Term.constant 1);
                            Formula.Ge (y, Term.constant 2);
                            Formula.Ge (z, Term.constant 3);
                            Formula.Le (Term.add x y, Term.constant 7);
                            Formula.Le (Term.add x z, Term.constant 58);
                            Formula.Le (Term.add y z, Term.constant 59);
                        ] |> Formula.conj

                    equiv oct.to_formula res
                )
