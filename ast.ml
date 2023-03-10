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

type ident = string

type label = Label of int

type binOp = 
  | Add
  | Sub
  | Mult

type boolOp = 
  | And
  | Or

type relOp = 
  | Eq
  | NotEq
  | Gt
  | Lt  

type expr =
  | Print of expr
  | Ident of ident  
  | Int of int
  | Neg
  | BinOp of binOp * expr * expr
  | Bool of bool
  | Not of expr
  | RelOp of relOp * expr * expr
  | BoolOp of boolOp * expr * expr
  | Seq of expr * expr
  | IfThenElse of expr * expr * expr (* If ___ then ___ else ___ *)
  | While of expr * expr (* While ___ do ___ *)
  | Assignment of ident * expr * label
  | Skip of label
  | Condition of expr * label

