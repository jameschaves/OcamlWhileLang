
(* The type of tokens. *)

type token = 
  | WHILE
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
  | IDENT of (string)
  | GT
  | FALSE
  | EQUAL
  | EOF
  | END
  | ELSE
  | DO
  | ASSIGN
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.stmt)
