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

module IntervalIntDom

open Utils
open Term
open Formula
open IIntAbsDom

type Bound = NegInf | PosInf | C of bigint
[<StructuredFormatDisplayAttribute("{pp}")>]
type Bound with
    member b1.min b2 =
        match (b1, b2) with
            | (NegInf, _) -> NegInf
            | (_, NegInf) -> NegInf
            | (PosInf, o) -> o
            | (o, PosInf) -> o
            | (C(c1), C(c2)) -> C(if c1 < c2 then c1 else c2)

    member b1.max b2 =
        match (b1, b2) with
            | (NegInf, o) -> o
            | (o, NegInf) -> o
            | (PosInf, _) -> PosInf
            | (_, PosInf) -> PosInf
            | (C(c1), C(c2)) -> C(if c1 > c2 then c1 else c2)

    member b.negate =
        match b with
            | NegInf -> PosInf
            | PosInf -> NegInf
            | C(x)   -> C(-x)

    member b.const_mult m =
        match b with
            | NegInf -> NegInf
            | PosInf -> PosInf
            | C(c) -> C(m*c)

    member b.const_add s =
        match b with
            | NegInf -> NegInf
            | PosInf -> PosInf
            | C(c) -> C(c+s)

    member b.int_value =
        match b with
            | C(c) -> c
            | _ -> Utils.dieWith ("Trying to get int value of " + b.ToString())

[<StructuredFormatDisplayAttribute("Intervals({pp})")>]
type Intervals =
    private {
        ///Variables we know something about. Everything that's not in there has a completely unknown value
        mutable vars : Map<Var.var, (Bound * Bound)>;
    }

    static member create = { vars = Map.empty; }

    member self.clone = {vars = self.vars; }

    member private self.setBoundsOfVar var bounds =
        if Map.containsKey var self.vars then
            self.vars <- self.vars |> Map.remove var |> Map.add var bounds
        else
            self.vars <- self.vars |> Map.add var bounds

    member private self.boundsOfVar var =
        if Map.containsKey var self.vars then
            self.vars.[var]
        else
            (NegInf, PosInf)

    member private self.boundsOfTerm (term : Term.term) : (Bound * Bound) =
        match term with
            | Const(x) -> (C(x), C(x))
            | Var(x) -> self.boundsOfVar x
            | Neg(t) ->
                let (l, u) = (self.boundsOfTerm t)
                (u.negate, l.negate)
            | Add(t1,t2) ->
                let (l1,u1) = self.boundsOfTerm t1
                let (l2,u2) = self.boundsOfTerm t2

                let mutable lr = NegInf
                if l1 = NegInf || l2 = NegInf then
                    lr <- NegInf
                else
                    match (l1, l2) with
                        | (C(c1), C(c2)) ->
                            lr <- C(c1+c2)
                        | (_,_) ->
                             //If the lower bound is inf, then there is no integer number that is described by these intervals. HELP!
                            assert (l1 <> PosInf && l2 <> PosInf);

                let mutable ur = PosInf
                if u1 = PosInf || u2 = PosInf then
                    ur <- PosInf
                else
                    match (u1, u2) with
                        | (C(c1), C(c2)) ->
                            ur <- C(c1+c2)
                        | (_,_) ->
                             //If the upper bound is -inf, then there is no integer number that is described by these intervals. HELP!
                             assert (u1 <> NegInf && u2 <> NegInf);
                (lr, ur)
            | Sub(t1,t2) -> self.boundsOfTerm (Add(t1,Neg(t2)))
            | Mul(t1,t2) ->
                let (l1,u1) = self.boundsOfTerm t1
                let (l2,u2) = self.boundsOfTerm t2

                //Only handle mult with constants
                if (l1 = u1) then
                    match l1 with
                        | C(c) -> (l2.const_mult c, u2.const_mult c)
                        | _ -> (NegInf, PosInf)
                else if (l2 = u2) then
                    match l2 with
                        | C(c) -> (l1.const_mult c, u1.const_mult c)
                        | _ -> (NegInf, PosInf)
                else
                    (NegInf, PosInf)
            | Nondet -> (NegInf, PosInf)

    member private self.merge (other: Intervals) (merge_func: Bound * Bound -> Bound * Bound -> Bound * Bound) =
        let changed = ref false
        let new_vars =
               self.vars
            |> Map.map
                (fun k v ->
                    let old_interval = v
                    let new_interval = merge_func v (other.boundsOfVar k)
                    if old_interval <> new_interval then changed := true
                    new_interval)
        self.vars <- new_vars
        !changed

    ///The other is always the "newer" value (obtained lated in the program):
    member self.widen (other: Intervals) =
        let interval_widen ((l1, u1) : Bound*Bound) ((l2, u2) : Bound*Bound) =
            let mutable lr = l1.min l2
            if (lr <> NegInf && (lr <> l1 || lr <> l2)) then
                let (l1c, l2c) = (l1.int_value, l2.int_value)
                //we get smaller, and have not reached rock bottom:
                if (l2c < l1c) then
                    lr <- match lr with
                            | C(c) -> if c > bigint.One then C(bigint.One)
                                      else if c > bigint.Zero then C(bigint.Zero)
                                      else NegInf
                            | _ -> NegInf

            let mutable ur = u1.max u2
            if (ur <> PosInf && (ur <> u1 || ur <> u2)) then
                let (u1c, u2c) = (u1.int_value, u2.int_value)
                //we get bigger and haven't reached the sky yet:
                if (u2c > u1c) then
                    ur <- match ur with
                            | C(c) -> if c < bigint.MinusOne then C(bigint.MinusOne)
                                      else if c < bigint.Zero then C(bigint.Zero)
                                      else PosInf
                            | _ -> PosInf
            (lr, ur)
        self.merge other interval_widen

    member self.assign var term = self.boundsOfTerm term |> self.setBoundsOfVar var

    member self.assume formula =
        let interval_intersection ((l1, u1) : Bound*Bound) ((l2, u2) : Bound*Bound) = (l1.max l2, u1.min u2)

        //Split variables out of sums in inequalities and put them on their own side:
        let normalize_term_pair l r =
            match l with
                // v + rest < r <=> v < r - rest
                | Add(Var(v), rest) -> (Var(v), Add(r, Neg(rest)))
                // v - rest < r <=> v < r + rest
                | Sub(Var(v), rest) -> (Var(v), Add(r, rest))
                // rest + v < r <=> v < r - rest
                | Add(rest, Var(v)) -> (Var(v), Add(r, Neg(rest)))
                // rest - v < r <=> rest < r + v <=> rest - r < v
                | Sub(rest, Var(v)) -> (Add(rest, Neg(r)), Var(v))
                | _ -> match r with
                        // l < v + rest <=> l - rest < v
                        | Add(Var(v), rest) -> (Add(l, Neg(rest)), Var(v))
                        // l < v - rest <=> l + rest < v
                        | Sub(Var(v), rest) -> (Add(l, rest), Var(v))
                        // l < rest + v <=> l - rest < v
                        | Add(rest, Var(v)) -> (Add(l, Neg(rest)), Var(v))
                        // l < rest - v <=> l + v < rest <=> v < rest - l
                        | Sub(rest, Var(v)) -> (Var(v), Add(rest, Neg(l)))
                        | _ -> (l,r)
        let rec normalize_formula f =
            match f with
                | And(f1,f2) -> And(normalize_formula f1, normalize_formula f2)
                | Or(f1,f2)  -> Or(normalize_formula f1, normalize_formula f2)
                | Not(f1)    -> Not(normalize_formula f1)
                | Eq(t1,t2)  ->
                    let (t1', t2') = normalize_term_pair t1 t2;
                    Eq(t1',t2')
                | Lt(t1,t2)  ->
                    let (t1', t2') = normalize_term_pair t1 t2;
                    Lt(t1',t2')
                | Le(t1,t2)  ->
                    let (t1', t2') = normalize_term_pair t1 t2;
                    Le(t1',t2')
                | Ge(t1,t2)  ->
                    let (t1', t2') = normalize_term_pair t1 t2;
                    Ge(t1',t2')
                | Gt(t1,t2)  ->
                    let (t1', t2') = normalize_term_pair t1 t2;
                    Gt(t1',t2')

        match (normalize_formula formula) with
            | And(f1, f2) ->
                self.assume f1
                self.assume f2
            | Eq(Var(v), t) ->
                self.boundsOfTerm t |> interval_intersection (self.boundsOfVar v) |> self.setBoundsOfVar v
            | Eq(t, Var(v)) ->
                self.assume (Eq(Var(v),t))
            | Eq _ -> ()
            | Lt(Var(v), t) ->
                let (_,ut) = self.boundsOfTerm t
                let (lv,uv) = self.boundsOfVar v
                self.setBoundsOfVar v (lv, uv.min (ut.const_add bigint.MinusOne))
            | Lt(t, Var(v)) ->
                let (lt,_) = self.boundsOfTerm t
                let (lv,uv) = self.boundsOfVar v
                self.setBoundsOfVar v (lv.max (lt.const_add bigint.One), uv)
            | Lt _ -> ()
            | Le(Var(v), t) ->
                let (_,ut) = self.boundsOfTerm t
                let (lv,uv) = self.boundsOfVar v
                self.setBoundsOfVar v (lv, uv.min ut)
            | Le(t, Var(v)) ->
                let (lt,_) = self.boundsOfTerm t
                let (lv,uv) = self.boundsOfVar v
                self.setBoundsOfVar v (lv.max lt, uv)
            | Le _ -> ()
            | Ge(l,r) -> self.assume (Le(r,l))
            | Gt(l,r) -> self.assume (Lt(r,l))
            | Not _ -> ()
            | Or _ -> ()

    member self.to_formula_filtered filter =
        [ for (v,i) in self.vars.Items do
            if filter v then
                match i with
                    | (NegInf, PosInf) -> ()
                    | (NegInf, C(u))   -> yield Formula.Le(Term.var(v), Term.Const(u))
                    | (C(l), PosInf)   -> yield Formula.Ge(Term.var(v), Term.Const(l))
                    | (C(l), C(u))     ->
                        if l = u then
                            yield Formula.Eq(Term.var(v), Term.Const(u))
                        else
                            yield Formula.Ge(Term.var(v), Term.Const(l))
                            yield Formula.Le(Term.var(v), Term.Const(u))
                    | _                -> assert(false); //Illegal Interval!
        ] |> Formula.conj

    interface IIntAbsDom with
        member self.tight_closure = ()
        member self.clone = self.clone :> IIntAbsDom
        member self.widen other = self.widen (other :?> Intervals)
        member self.assign var term = self.assign var term
        member self.assume f = self.assume f
        member self.to_formula = self.to_formula_filtered (fun _ -> true)
        member self.to_formula_filtered filter = self.to_formula_filtered filter
