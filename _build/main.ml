open Ast

(** [parse s] parses [s] into an AST. *)
let parse (s : string) : stmt = 
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog Lexer.read_token lexbuf in 
  ast


(*  
(** [string_of_val e] converts [e] to a string.
    Requires: [e] is a value. *)
let string_of_val (e : stmt) : string = 
  match e with
  | IfThenElse (_, _, _) -> failwith "TODO"
  (* | Stmt(Unop _) -> failwith "14 precondition violated" *)

(* [is_value e] is whether [e] is a value *)
let is_value : aExp -> bool = function 
  | Var _ -> true
  (* | Num _ -> true *)
  (* | AExp _ -> false
  | Stmt _ -> false *)

let is_valueBExp : bExp -> bool = function 
  | Bool(true) -> true
  | Bool(false) -> true
  (* | Num _ -> true *)
  (* | AExp _ -> false
  | Stmt _ -> false *)

(** [step e] takes a single step of evaluation of [e]. *)
let rec step : aExp -> aExp = function 
  | Int _ -> failwith "Does not step"
  | Var _ -> failwith "Does not step"
  | BinOp (binOp, a1, a2) when is_value a1 && is_value a2 ->
  step_binOp binOp a1 a2
  | BinOp (binOp, a1, a2) when is_value a1 -> BinOp (binOp, a1, step a2)
  | BinOp (binOp, a1, a2) -> BinOp (binOp, step a1, a2)

(* [step_bop bop v1 v2] implements the primite operation 
   [v1 bop v2]. Requires: [v1] and [v2] are both values *)
and step_binOp binOp v1 v2 = match binOp, v1, v2 with
  | Add, Int a, Int b -> Int (a + b)
  | Sub, Int a, Int b -> Int (a - b)
  | Mult, Int a, Int b -> Int (a * b)
  | _ -> failwith "32 precondition violated"

let rec step : bExp -> bExp = function 
  | Bool (true) -> failwith "Does not step"
  | Bool (false) -> failwith "Does not step"
  | Not _ -> failwith "Does not step"
  (* | RelOp (relOp, a1, a2) when is_value a1 && is_value a2 ->
    step_relOp relOp a1 a2
  | RelOp (relOp, a1, a2) when is_value a1 -> RelOp (relOp, a1, stepAExp a2)
  | RelOp (relOp, a1, a2) -> RelOp (relOp, step a1, a2) *)
  | BoolOp (boolOp, b1, b2) when is_valueBExp b1 && is_valueBExp b2 ->
    step_boolOp boolOp b1 b2
  | BoolOp (boolOp, b1, b2) when is_valueBExp b1 -> BoolOp (boolOp, b1, step b2)
  | BoolOp (boolOp, b1, b2) -> BoolOp (boolOp, step b1, b2)

and step_relOp relOp v1 v2 = match relOp, v1, v2 with
  | Eq, Int a1, Int a2 -> if a1 = a2 then true else false
  | NotEq, Int a1, Int a2 -> if a1 != a2 then true else false
  | Gt, Int a1, Int a2 -> if a1 > a2 then true else false
  | Lt, Int a1, Int a2 -> if a1 < a2 then true else false
  | _ -> failwith "32 precondition violated"

and step_boolOp boolOp v1 v2 = match boolOp, v1, v2 with
  | And, Bool b1, Bool b2 -> if b1 && b2 then true else false
  | Or, Bool b1, Bool b2 -> if b1 || b2 then true else false
  | _ -> failwith "32 precondition violated"

(** [eval e] fully evaluates [e] to a value [v].*)
let rec eval (e : 'a) : 'a = 
  if is_value e then e else 
    e |> step |> eval

(* * [interpret s] interpret [s] by lexing and parsing it,
    evaluating it, and converting the result to a string. *)
let interp (s : string) : string =
  s |> parse |> eval |> string_of_val *)
