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

module Microsoft.Research.T2.CTL


[<StructuredFormatDisplayAttribute("{pp}")>]
type CTL_Formula =
    | Atom of Formula.formula
    | CTL_And of CTL_Formula * CTL_Formula
    | CTL_Or of CTL_Formula * CTL_Formula
    | AF of CTL_Formula
    | AW of CTL_Formula * CTL_Formula
    | AG of CTL_Formula
    | AX of CTL_Formula
    | EF of CTL_Formula
    | EU of CTL_Formula * CTL_Formula
    | EG of CTL_Formula
    | EX of CTL_Formula

    //Pretty Printing for CTL datatype, not quite complete, but not worried about it right now.
    member self.pp =
        // see comment to term2pp
        let protect strength force s =
            if strength >= force then s else "(" + s + ")"

        let rec pp' force e =
            match e with
            | Atom a -> protect 0 force a.pp
            | AF e -> protect 3 force ("AF " + pp' 3 e)
            | AG e -> protect 3 force ("AG " + pp' 3 e)
            | AX e -> protect 3 force ("AX " + pp' 3 e)
            | EF e -> protect 3 force ("EF " + pp' 3 e)
            | EG e -> protect 3 force ("EG " + pp' 3 e)
            | EX e -> protect 3 force ("EX " + pp' 3 e)
            | CTL_And(e1,e2) -> protect 1 force  (pp' 1 e1 + " and " + pp' 1 e2)
            | CTL_Or(e1,e2)  -> protect 1 force (pp' 1 e1 + " or " + pp' 1 e2)
            | AW(e1,e2) -> protect 0 force ("A " + pp' 3 e1 + " W " + pp' 3 e2)
            | EU(e1,e2) -> protect 0 force ("E " + pp' 3 e1 + " U " + pp' 3 e2)

        pp' 0 self

    member self.isAtomic =
        match self with
        | Atom _ -> true
        | _ -> false

    static member freevars formula =
        match formula with
        | Atom a -> 
            Formula.freevars a
        | AF e | AG e | AX e | EF e | EG e | EX e -> 
            CTL_Formula.freevars e
        | CTL_And (e1, e2) | CTL_Or (e1, e2) | AW (e1, e2) | EU (e1, e2) ->
            Set.union (CTL_Formula.freevars e1) (CTL_Formula.freevars e2)