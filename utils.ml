open Ast

(*A map for all arithmetics expression that appear in the program *)
module AexprSetProg = Set.Make(struct type t = expr let compare = compare end);;
module AexprMap = Map.Make(String);;

(* Range from 0 to n. *)
let range n =
  let rec range_ n acc =
    if n = -1 then
      acc
    else 
      range_ (n-1) (n::acc)
  in range_ n [];;

(* Fixed point operator. *)
let rec fix f x = f (fix f) x;;

(* Create a list having element a repeated n times. *)
let repeat a n =
  let rec repeat_ a n acc =
    if n == 0 then 
      acc
    else
      repeat_ a (n-1) (a::acc)
  in repeat_ a n [];;

let exp_has_variable expr x =
  let rec compute expr =
    match expr with
    | Ident x -> true
    | BinOp (_, a1, a2) -> let lh = compute a1 in compute a2
    | RelOp (_, a1, a2) -> let lh = compute a1 in compute a2
    | _ -> false
  in compute expr;;



let rec string_of_expr (e : expr) : string = 
  match e with
  | Int i -> string_of_int i
  | Ident x -> x
  | Bool b ->string_of_bool b
  | BinOp (binOP, a1, a2) -> begin
    match binOP with
    | Add -> "[" ^ string_of_expr a1 ^ " + " ^ string_of_expr a2 ^ "]"
    | Mult -> "[" ^ string_of_expr a1 ^ " * " ^ string_of_expr a2 ^ "]"
    | Sub -> "[" ^ string_of_expr a1 ^ " - " ^ string_of_expr a2 ^ "]"
  end
  | RelOp (relOp, a1, a2) -> begin
    match relOp with
    | Eq -> string_of_expr a1 ^ " == " ^ string_of_expr a2
    | Gt -> string_of_expr a1 ^ " > " ^ string_of_expr a2
    | Lt -> string_of_expr a1 ^ " - " ^ string_of_expr a2
  end
  | (Neg  | Bool _ | Not _
  | BoolOp (_, _, _) | Seq (_, _) | While (_, _) 
  | Assignment (_, _, Label _)| Skip (Label _) | Condition (_, Label _) 
  | IfThenElse (_, _, _)) -> failwith "14 precondition violated"
   
  (* let rec nonTrivialAExp expr = 
    let rec compute expr set = 
      match expr with
        | BinOp (binOP, a1, a2) -> AexprMap.add "x" expr set
        | RelOp (relOp, a1, a2) -> AexprMap.add "x" expr set
        | Assignment (_, e, _) -> compute e set
        | While (c, _) -> compute c set
        | IfThenElse (c, _, _) -> compute c set
        | Condition (b, _) -> compute b set
        | Seq (s1, s2) ->  
          let lh = nonTrivialAExp s1 in 
          let rh = nonTrivialAExp s2 in
          AexprMap.union lh rh
        | _ -> AexprMap.empty
      in compute expr AexprMap.empty;;
 *)
