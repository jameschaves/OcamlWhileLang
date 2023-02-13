let range n =
  let rec range_ n acc =
    if n = -1 then
      acc
    else 
      range_ (n-1) (n::acc)
  in range_ n [];;


module AexprSet = Set.Make(struct type t = expr let compare = compare end);;

module LabelSet = Set.Make(struct type t = EBSet.key let compare = compare end);;

module CIMap = Map.Make(struct type t = EBSet.key let compare = compare end);;

let find_aexp_node node aExpset = 
  match node with
    | { content = c ; children = _ } -> 
      match c with
      | Right condition_expr -> 
        (match condition_expr with
          | Condition (bexpr, _) -> 
          (match bexpr with
            | RelOp (_, a1, a2) -> AexprSet.add bexpr aExpset
          )
          | _ -> failwith "Error in condition" 
        )  
      | Left stmt ->
        (match stmt with
          | Assignment (_, aexpr, _) -> 
            (match aexpr with
            | BinOp (_, a1, a2) -> AexprSet.add aexpr aExpset
            )
          | _ -> failwith "Error in stmt"
        );;

let start_entry lab dfg =
  let node = EBSet.find lab dfg in
  find_aexp_node node AexprSet.empty;;

let input_fname = "programs/ppa_pg48_teste_vbe.while";;

let input_file = open_in input_fname;;
let lexer_buffer = Lexing.from_channel input_file;;
let ast = Parser.prog Lexer.read_token lexer_buffer;;
let (dfg, max_lab) = build_data_flow_graph ast;;


let start_point dfg max_lab = 
  List.fold_left (fun m n -> CIMap.add n ((start_entry n dfg), AexprSet.empty) m) CIMap.empty (range (max_lab - 1));;
