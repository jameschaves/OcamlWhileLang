
(* The type of tokens. *)

type token = 
  | VAR of (string)
  | TRUE
  | TIMES
  | SKIP
  | RPAREN
  | RCURLYBRACKET
  | RBRACKET
  | PLUS
  | OR
  | NUM of (int)
  | NOT
  | MINUS
  | LT
  | LPAREN
  | LCURLYBRACKET
  | LBRACKET
  | LABEL of (Ast.label)
  | GT
  | FALSE
  | EQUAL
  | EOF
  | ASSIGN
  | AND
  | AEXP of (Ast.aExp)

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.expr)
