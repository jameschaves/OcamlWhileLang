open Ast

(** [parse s] parses [s] into an AST. *)
let parse (s : string) : expr = 
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog Lexer.read_token lexbuf in 
  ast

(** [string_of_val e] converts [e] to a string.
    Requires: [e] is a value. *)
let string_of_val (e : expr) : string = 
  match e with
  (* | Num n -> string_of_int n *)
  | Num i -> string_of_int i
  | Var v -> v
  | Stmt _ -> failwith "14 precondition violated"
  | AExp _ -> failwith "14 precondition violated"

(* [is_value e] is whether [e] is a value *)
  let is_value : 'a -> bool = function 
    | Var _ -> true
    (* | Num _ -> true *)
    | Var _ -> true
    | AExp _ -> false
    | Stmt _ -> false

(** [step e] takes a single step of evaluation of [e]. *)
let rec step : 'a -> 'a = function 
  | Num _ -> failwith "Does not step"
  | Var _ -> failwith "Does not step"
  | AExp (aExp, e1, e2) when is_value e1 && is_value e2 ->
      step_aExp aExp e1 e2
  | AExp (aExp, e1, e2) when is_value e1 -> AExp (aExp, e1, step e2)
  | AExp (aExp, e1, e2) -> AExp (aExp, step e1, e2)

  (* | Stmt (Assignment(var, e, l)) when is_value e1 && is_value e2 -> *)



  
(* [step_bop bop v1 v2] implements the primite operation 
   [v1 bop v2]. Requires: [v1] and [v2] are both values *)
and step_aExp aExp v1 v2 = match aExp, v1, v2 with
| Add, Num a, Num b -> Num (a + b)
| Sub, Num a, Num b -> Num (a - b)
| Mult, Num a, Num b -> Num (a * b)
  | _ -> failwith "32 precondition violated"

(** [eval e] fully evaluates [e] to a value [v].*)
let rec eval (e : expr) : expr = 
  if is_value e then e else 
    e |> step |> eval

(** [interpret s] interpret [s] by lexing and parsing it,
    evaluating it, and converting the result to a string. *)
  let interp (s : string) : string =
    s |> parse |> eval |> string_of_val
