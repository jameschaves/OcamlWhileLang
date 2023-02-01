open Ast

(** [parse s] parses [s] into an AST. *)
let parse (s : string) : program = 
  let lexbuf = Lexing.from_string s in
  let ast = Parser.program Lexer.read_token lexbuf in 
  ast
(* 
(** [string_of_val e] converts [e] to a string.
    Requires: [e] is a value. *)
let string_of_val (e : stmt) : string = 
  match e with
  | True -> "true"
  | False -> "false"
  | Int i -> string_of_int i
  | Var v -> v

let string_of_val (e : aExp) : string = 
    match e with
    | Binop _ -> failwith "14 precondition violated"

let string_of_val (e : bExp) : string = 
    match e with
    | Boolop _ -> failwith "14 precondition violated"


(* [is_value e] is whether [e] is a value *)
  let is_value : 'a -> bool = function 
    | Var _ -> true
    (* | Num _ -> true *)
    (* | AExp _ -> false
    | Stmt _ -> false *)

(** [step e] takes a single step of evaluation of [e]. *)
let rec step : 'a -> 'a = function 
  | Int _ -> failwith "Does not step"
  | Var _ -> failwith "Does not step"
| Binop (binop, e1, e2) when is_value e1 && is_value e2 ->
  step_binop binop e1 e2
| Binop (binop, e1, e2) when is_value e1 -> Binop (binop, e1, step e2)
| Binop (binop, e1, e2) -> Binop (binop, step e1, e2)

  (* | Stmt (Assignment(var, e, l)) when is_value e1 && is_value e2 -> *)

 
(* [step_bop bop v1 v2] implements the primite operation 
   [v1 bop v2]. Requires: [v1] and [v2] are both values *)
and step_binop binop v1 v2 = match binop, v1, v2 with
| Add, Num a, Num b -> Num (a + b)
| Sub, Num a, Num b -> Num (a - b)
| Mult, Num a, Num b -> Num (a * b)
| _ -> failwith "32 precondition violated"

(** [eval e] fully evaluates [e] to a value [v].*)
let rec eval (e : 'a) : 'a = 
  if is_value e then e else 
    e |> step |> eval

(* * [interpret s] interpret [s] by lexing and parsing it,
    evaluating it, and converting the result to a string. *)
(* let interp (s : string) : string =
  s |> parse |> eval |> string_of_val *) *)
