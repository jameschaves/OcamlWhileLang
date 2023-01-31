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

type label = Int

type aExp = 
  | Add
  | Sub
  | Mult

type bExp = 
  | And
  | Or
  | Eq
  | Gt
  | Lt

type conditionExp = Condition of bExp * label

type stmt = 
  | Assignment of string * aExp * label
  | Seq of stmt * stmt
  | IfThenElse of conditionExp * stmt * stmt
  | While of conditionExp * stmt

type block = 
  | Stmt of stmt
  | Condition of conditionExp

type expr = 
  | Block of block
  | Stmt of stmt
  | Skip of expr
  | BExp of bExp * expr * expr
  | True
  | False
  | Not of expr
  | Var of string
  | Num of int
  | AExp of aExp * expr * expr
  | Label of label

let label(Stmt(Assignment(_, _, l))) = l
let label(Skip(l)) = l
let label(Condition(Condition(b, l))) = l






  
