{
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

module Absflex

open Absparse
let lexerror msg lexbuf = (Printf.printf "Unimplemented %s" msg; failwith "error")

}

let digit    = ['0'-'9']
let letdig   = ['0'-'9' 'a'-'z' 'A'-'Z' '_' '.' ]
let letdigpling   = ['0'-'9' 'a'-'z' 'A'-'Z' '_' '!']
let alphlet  = ['A'-'Z' 'a'-'z' '_' '$' '\'' ]
let ws       = [' ' '\009' '\012']

rule token = parse
    '\r'                { token lexbuf}
  | '\n'                { ParseError.noteNewline lexbuf.EndPos.AbsoluteOffset;
                          token lexbuf
                        }

  | "//"[^'\n']*'\n'
                        { ParseError.noteNewline lexbuf.EndPos.AbsoluteOffset;
                          token lexbuf
                         }

  | "#line"ws+digit+ws+'"'[^'"']*'"'[^'\n']*'\n'
      { begin
        failwith "error"
      end }    
      
  | "#"[^'\n']*'\n'
                        { begin
                          ParseError.noteNewline lexbuf.EndPos.AbsoluteOffset;
                          token lexbuf
                          end }

  | '"'[^'\n''"']*'"' 
      { 
        let str = System.Text.Encoding.Default.GetString(lexbuf.Lexeme)
        (* get rid of first and last characters *)
        String(str.Substring(1, str.Length - 2))
      }        

  | ws                        { token lexbuf }

  | "TO"              { TO }
  | "FROM"             { FROM }
  | "CUTPOINT"              { CUTPOINT }
  | "nondet"              { NONDET }
  | "NONDET"              { NONDET }
  | "SHADOW"              { SHADOW }
  | "START"             { START }
  | "AT"             { AT }


  | "[AF]"   {AF}
  | "[AG]"   {AG}
  | "[AW]"   {AW}
  | "[AX]"   {AX}
  | "[EF]"   {EF}
  | "[EG]"   {EG}
  | "[EU]"   {EU}
  | "[EX]"   {EX}


  | ','                 { COMMA }
  | '('                        { LPAREN }
  | ')'                        { RPAREN }
  | '+'                        { PLUS }
  | '-'                        { MINUS }
  | "*"                        { STAR }
  | '/'                 { DIV  }
  | '!'                 { NOT  }
  | '%'                 { REM  }
  | ';'                 { SEMICOLON  }
  | ":"                 { COLON }
  | "<"                        { LT }
  | ">"                        { GT }
  | "<="                { LE }
  | ">="                { GE }
  | "=="                { EQ }
  | "="                { EQ }
  | "!="                { NE }
  | ":="                { ASSIGN }
  | "assume"            { ASSUME }
  | "&&"                { AND_OP }
  | "||"                { OR_OP }
  | (digit)+                { Num(bigint.Parse (System.Text.Encoding.Default.GetString(lexbuf.Lexeme))) }
  | (alphlet)(letdig)*('!' letdig+)*        { Id    (System.Text.Encoding.Default.GetString(lexbuf.Lexeme)) }
  | eof                        { EOF }
  | _                        { 
                          begin
                            lexerror ("Illegal Character '" + 
                                      (System.Text.Encoding.Default.GetString(lexbuf.Lexeme))) lexbuf;
                            token lexbuf
                          end }






