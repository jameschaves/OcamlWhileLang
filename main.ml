open Ast

module AssignMap = Map.Make(String);;
let assign = AssignMap.empty;;

type ('a, 'b) either = Left of 'a | Right of 'b;;

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
  | Assignment (_, _, _) -> false
  | (Neg | BinOp (_, _, _)) -> false
  | (Bool _ | Not _) -> true;
  | (RelOp (_, _, _) | BoolOp (_, _, _)) -> false
  | (Seq (_, _)|IfThenElse (_, _, _)|While (_, _)|Skip _| Condition (_, _)) -> false
  
(** [step e] takes a single step of evaluation of [e]. *)
let rec step : expr -> expr = function 
  | (Int _ | Ident _ | Bool _ | Not _ | Neg) -> failwith "Does not step"

  | BinOp (binOp, a1, a2) when is_value a1 && is_value a2 ->
  step_binOp binOp a1 a2
  | BinOp (binOp, a1, a2) when is_value a1 -> BinOp (binOp, a1, step a2)
  | BinOp (binOp, a1, a2) -> BinOp (binOp, step a1, a2)
  
  | RelOp (relOp, a1, a2) when is_value a1 && is_value a2 ->
  step_relOp relOp a1 a2
  | RelOp (relOp, a1, a2) when is_value a1 -> RelOp (relOp, a1, step a2)
  | RelOp (relOp, a1, a2) -> RelOp (relOp, step a1, a2)
  
  | BoolOp (boolOp, b1, b2) when is_value b1 && is_value b2 ->
  step_boolOp boolOp b1 b2
  | BoolOp (boolOp, b1, b2) when is_value b1 -> BoolOp (boolOp, b1, step b2)
  | BoolOp (boolOp, b1, b2) -> BoolOp (boolOp, step b1, b2)

  | Seq (s1, s2) when not(is_value s1) && not(is_value s2) -> Seq (step s1, step s2)
  | Seq (s1, s2) when not(is_value s1) -> Seq (step s1, s2)
  | Seq (s1, s2) when not(is_value s2) -> Seq (s1, step s2)

  | IfThenElse (c, s1, s2) when not(is_value s1) && not(is_value s2) -> IfThenElse (step c, step s1, step s2)
  | IfThenElse (c, s1, s2) when not(is_value s1) -> IfThenElse (step c, step s1, s2)
  | IfThenElse (c, s1, s2) when not(is_value s2) -> IfThenElse (step c, s1, step s2)

  | IfThenElse (c, s1, s2) when not(is_value s1) && not(is_value s2) -> IfThenElse (step c, step s1, step s2)

  | While (c, w) when not(is_value w) -> While (step c, step w)
  
  | Assignment (x, a, _) when not(is_value a) -> step a
  | Assignment (x, a, _) -> let assign = AssignMap.add x a assign in Ident x

  | Skip _ -> failwith "TODO"
  | Condition (c, l) -> 
    let cStep = step c in
          Condition (cStep, l)

 
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