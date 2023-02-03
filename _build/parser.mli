
(* The type of tokens. *)

type token = 
  | WHILE
  | VAR of (string)
  | TRUE
  | TIMES
  | THEN
  | SKIP
  | SEMICOLON
  | RPAREN
  | RBRACKET
  | PLUS
  | OR
  | NOT
  | MINUS
  | LT
  | LPAREN
  | LBRACKET
  | INT of (int)
  | IF
  | GT
  | FALSE
  | EQUAL
  | EOF
  | ELSE
  | DO
  | ASSIGN
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.stmt)
