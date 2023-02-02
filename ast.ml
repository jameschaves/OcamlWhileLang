(* Synopsis: The abstract syntax definition of the WhileLanguage. 
  
  Description: The While Language is a tiny imperative 
  programming language supporting arithmetic and boolean expressions, 
  as well a small number of statements: 
  
     * assignment statement
     * if-then-else statement
     * while statement 
     * skip statement
     * sequence statement (a statement s1 followed by a statement s2) 
   
  We represented the abstract syntax of the WhileLanguage using algebraic 
  data types in Ocaml--- one algebraic data type for every main syntactic 
  construct (boolean expressions (BExp), arithmetic expressions (AExp), and 
  statements (Stmt)). Elementary statements, including assigment and skip 
  are annotated with labels (a unique int value). Conditions appearing 
  in if-then-else and while statements are also annotated with labels. 
  
  We implemented an additional algebraic type Block to generalize over 
  statements and conditions.  *)

(* * An abstract type for identifiers
module type ID = sig
  type t

  val of_string : string -> t
  val to_string : t -> string
end

module String_id = struct
  type t = string

  let of_string x = x
  let to_string x = x
end

module Var_name : ID = String_id *)

type identifier = Variable of string 

type expr =
  | Int of int
  | Bool of bool
  | Var of string  
  | True
  | False
  | Not of unop
  | Binop of binop * expr * expr
  | Unop of unop * expr
  | Assignment of identifier * expr * label_expr
  | Skip of label_expr
  (* | Seq of expr * expr *)
  | IfThenElse of expr * block_expr * block_expr (* If ___ then ___ else ___ *)
  | While of condition_expr * block_expr (* While ___ do ___ *)

and block_expr = 
| Stmt of expr list

(* | Seq of expr * expr *)

and condition_expr = 
| Condition of expr * label_expr

and label_expr = 
| Label of expr

and binop = 
  | Add
  | Sub
  | Mult
  | And
  | Or
  | Eq
  | NotEq
  | Gt
  | Lt  

and unop = 
  | Not
  | Neg

type program = Prog of block_expr

(* 
let label(Stmt(Assignment(_, _, l))) = l
let label(Stmt(Skip(l))) = l
let label(Condition(b, l)) = l *)

