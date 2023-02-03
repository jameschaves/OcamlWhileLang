open Ast

(** [parse s] parses [s] into an AST. *)
let parse (s : string) : stmt = 
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog Lexer.read_token lexbuf in 
  ast


 
(** [string_of_val e] converts [e] to a string.
    Requires: [e] is a value. *)
let string_of_val (e : stmt) : string = 
  match e with
  | IfThenElse (_, _, _) -> failwith "TODO"
  (* | Stmt(Unop _) -> failwith "14 precondition violated" *)

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
| Add, Int a, Int b -> Int (a + b)
| Sub, Int a, Int b -> Int (a - b)
| Mult, Int a, Int b -> Int (a * b)
| _ -> failwith "32 precondition violated"

(** [eval e] fully evaluates [e] to a value [v].*)
let rec eval (e : 'a) : 'a = 
  if is_value e then e else 
    e |> step |> eval

(* * [interpret s] interpret [s] by lexing and parsing it,
    evaluating it, and converting the result to a string. *)
let interp (s : string) : string =
  s |> parse |> eval |> string_of_val
