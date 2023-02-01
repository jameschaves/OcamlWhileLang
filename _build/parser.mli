
(* The type of tokens. *)

type token = 
  | WHILE
  | VAR of (string)
  | TRUE
  | TIMES
  | SKIP
  | SEMICOLON
  | RPAREN
  | RCURLYBRACKET
  | RBRACKET
  | PLUS
  | OR
  | NOT
  | MINUS
  | LT
  | LPAREN
  | LCURLYBRACKET
  | LBRACKET
  | INT of (int)
  | IF
  | GT
  | FALSE
  | EQUAL
  | EOF
  | ELSE
  | ASSIGN
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val program: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.program)
