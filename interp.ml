open Ast


module MemMap = Map.Make(struct type t = Ident let compare = compare end);;

(* Data Flow Node. *)
type mem_data = (int, string) either;;

let assign = MemMap.empty;;

(** [parse s] parses [s] into an AST. *)
let parse (s : string) : expr = 
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog Lexer.read_token lexbuf in 
  ast

(** [string_of_val e] converts [e] to a string. Requires: [e] is a value. *)
let string_of_val (e : expr) : string = 
  match e with
  | Int i -> string_of_int i
  | Ident i -> i
  | Bool b ->string_of_bool b
  | (Neg | BinOp (_, _, _) | Bool _ | Not _
  | RelOp (_, _, _) | BoolOp (_, _, _) | Seq (_, _) | While (_, _) 
  | Assignment (_, _, Label _)| Skip (Label _) | Condition (_, Label _) 
  | IfThenElse (_, _, _)) -> failwith "14 precondition violated"

let output (e : expr) : string = 
    match e with
  | Print i -> string_of_int i
  | _ -> failwith "erro"
(* 
  let process (ident : string) (a : int)  = function
    let assign = AssignMap.add x a assign *)

(* [is_value e] is whether [e] is a value *)
let rec is_value : expr -> bool = function
  | Int _ -> true
  | Ident _ -> true
  | (Bool _ | Not _) -> true;  
  | (Assignment (_, _, _) | Neg | BinOp (_, _, _)
  | RelOp (_, _, _) | BoolOp (_, _, _)
  | Seq (_, _)| IfThenElse (_, _, _)| While (_, _)| Skip _| Condition (_, _)) -> false


  
(** [step e] takes a single step of evaluation of [e]. *)
let rec step : expr -> expr = function 
  | Int i -> i
  | Ident a -> if MemMap.mem a then 
  | Bool b -> b
  | ( Not _ | Neg) -> failwith "Does not step"

  | Print expr -> expr

  | BinOp (binOp, a1, a2) when is_value a1 && is_value a2 ->
    let v = step_binOp binOp a1 a2 in step v
  | BinOp (binOp, a1, a2) when is_value a1 -> BinOp (binOp, a1, step a2)
  | BinOp (binOp, a1, a2) -> BinOp (binOp, step a1, a2)
  
  | RelOp (relOp, a1, a2) when is_value a1 && is_value a2 ->
    let v = step_relOp relOp a1 a2 in step v
  | RelOp (relOp, a1, a2) when is_value a1 -> RelOp (relOp, a1, step a2)
  | RelOp (relOp, a1, a2) -> RelOp (relOp, step a1, a2)
  
  | BoolOp (boolOp, b1, b2) when is_value b1 && is_value b2 ->
    let v = step_boolOp boolOp b1 b2 in step
  | BoolOp (boolOp, b1, b2) when is_value b1 -> BoolOp (boolOp, b1, step b2)
  | BoolOp (boolOp, b1, b2) -> BoolOp (boolOp, step b1, b2)

  | Seq (s1, s2) -> Seq (step s1, step s2)

  | IfThenElse (c, s1, s2) -> let cond = step c in if (cond) then step s1 else step s2 

  | While (c, w) when step c -> step w 
  
  | Assignment (x, a, _) when not(is_value a) -> let v = step a in MemMap.singleton x v
  | Assignment (x, a, _) -> MemMap.singleton x a
  | Skip _ -> failwith "TODO"
  | Condition (c, l) -> let cStep = step c 

 
(* [step_bop bop v1 v2] implements the primite operation 
   [v1 bop v2]. Requires: [v1] and [v2] are both values *)
and step_binOp binOp v1 v2 = match binOp, v1, v2 with
  | Add, Int a, Int b -> Int (a + b)
  | Sub, Int a, Int b -> Int (a - b)
  | Mult, Int a, Int b -> Int (a * b)
  | _ -> failwith "Operator and operand binOp type mismatch"
    
and step_relOp relOp v1 v2 = match relOp, v1, v2 with
  | Eq, Int a1, Int a2 -> Bool (a1 == a2)
  | NotEq, Int a1, Int a2 -> Bool (a1 != a2)
  | Gt, Int a1, Int a2 -> Bool (a1 > a2)
  | Lt, Int a1, Int a2 -> Bool (a1 < a2)
  | _ -> failwith "Operator and operand relOp type mismatch"

and step_boolOp boolOp v1 v2 = match boolOp, v1, v2 with
  | And, Bool b1, Bool b2 -> Bool (b1 && b2)
  | Or, Bool b1, Bool b2 -> Bool (b1 || b2)
  | _ -> failwith "Operator and operand boolOp type mismatch"

(** [eval e] fully evaluates [e] to a value [v].*)
let rec eval (e : expr) : expr = 
  if is_value e then e else 
    e |> step |> eval
    
(* * [interpret s] interpret [s] by lexing and parsing it,
    evaluating it, and converting the result to a string. *)
let interp (s : string) : string =
  s |> parse |> eval |> string_of_val