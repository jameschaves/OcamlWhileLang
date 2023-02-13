open Ast;;
open Data_flow;;
open Utils;;

(* module AexprSet = Set.Make(struct type t = expr let compare = compare end);; *)

module AexprSet = Set.Make(struct type t = expr let compare = compare end);;

(*A map for the labels*)
module LabelSet = Set.Make(struct type t = EBSet.key let compare = compare end);;

(*Identify the free arithmetics expressions for each assgn*)
let very_busy_aexpr expr =
  let rec vb_aexpr expr s =
  match expr with
  | BinOp (_, a1, a2) -> AexprSet.add expr s
  | _ -> AexprSet.empty
  in vb_aexpr expr AexprSet.empty;;

(*Identify the free boolean expression variable for each condition*)
let very_busy_bexpr expr =
  let rec compute expr s =
    match expr with
    | Not nexpr -> compute nexpr s
    | RelOp (_, a1, a2) ->
        let lh = very_busy_aexpr a1 in 
        let rh = very_busy_aexpr a2 in
        AexprSet.union lh rh
    | _ -> AexprSet.empty
  in compute expr AexprSet.empty;;
  
 (*Identiy the gen set of each assign block of expression*)
let genc c =
  match c with
  | Right condition_expr -> 
    (match condition_expr with
     | Condition (bexpr, _) -> very_busy_bexpr bexpr
     | _ -> AexprSet.empty 
    )  
  | Left stmt ->
    (match stmt with
     | Assignment (_, aexpr, _) -> very_busy_aexpr aexpr
     | _ -> AexprSet.empty (*The other statement do not gen VB*)
    );;

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
        )

let aExps_set dfg max_lab = 
  List.fold_left (fun aExpset lab ->
    let node = EBSet.find lab dfg in
    find_aexp_node node aExpset
  ) AexprSet.empty (range (max_lab - 1));;

      
let rec ident_filter x exp =
  match exp with
  | BinOp(_, a1, a2) -> eval_aexp a1 x || eval_aexp a2 x
  | RelOp(_, a1, a2) -> eval_aexp a1 x || eval_aexp a2 x
  | _ -> failwith "Error in filter type"
and eval_aexp aexp x =
  match aexp with 
    | Ident a -> a = x
    | _ -> false;;

 (*Identiy the kill set of each assign and condition block of expression*)
 let killc max_lab dfg c  =
  let aExpSet = aExps_set dfg max_lab in (*Creat a set of all aExp in the program*)
  match c with
  | Right _ -> AexprSet.empty (*Refer to condition. In VB the kill set is {}*)
  | Left stmt ->
      match stmt with
       | Assignment (x, expr, _) -> AexprSet.filter (ident_filter x) aExpSet (*Filter in all aExp those that have the identifier been modified in the right side hand*)
       | Skip _ -> AexprSet.empty (*For Skip, in VB the kill set is {}*)
       | _ -> failwith "Error in kill type"
      

let gen dfn =
  match dfn with
  | { content = c ; children = _ } -> genc c;;

let kill max_lab dfg dfn =
  match dfn with
  | { content = c ; children = _ } -> killc max_lab dfg c;;

let final_set dfg max_lab = 
  List.fold_left (fun finalset lab ->
    let node = EBSet.find lab dfg in
      match List.filter (fun chl -> chl > lab) node.children with
      | [] -> LabelSet.add lab finalset
      | _ -> finalset) LabelSet.empty (range (max_lab - 1));;

(*Create a new MAP with the set {assingment ; condition} index by labels (EBSet.key) from data_flow*)
module CIMap = Map.Make(struct type t = EBSet.key let compare = compare end);;

let start_entry lab dfg =
  let node = EBSet.find lab dfg in
  find_aexp_node node AexprSet.empty;;

(*Populate de CIMap. The entry and exist sets will receive this MAP as start*)
let start_point dfg max_lab = 
  List.fold_left (fun m n -> CIMap.add n (AexprSet.empty, AexprSet.empty) m) CIMap.empty (range (max_lab - 1));;

let ci_converged prev_it cur_it =
  let (prev_entry, prev_exit) = prev_it and
      (cur_entry, cur_exit) = cur_it in
      AexprSet.equal prev_entry cur_entry && AexprSet.equal prev_exit cur_exit;;

let vb_entry max_lab dfg exit node =
  AexprSet.union (AexprSet.diff exit (kill max_lab dfg node)) (gen node);;

let vb_exit dfg max_lab final_set n cmap node =
  if LabelSet.mem n final_set then 
    AexprSet.empty
  else 
    List.fold_left 
      (fun s l -> AexprSet.inter s (fst (CIMap.find l cmap))) 
      (aExps_set dfg max_lab)  node.children;;

let vb_iterate idfg final_set max_lab f cmap =
  let ncmap = List.fold_left (fun m n ->
    let (entry, exit) = CIMap.find n m in
    let node = EBSet.find n idfg in
    let nentry = vb_entry max_lab idfg exit node in
    let nexit = vb_exit idfg max_lab final_set n m node in
    CIMap.add n (nentry, nexit) m) cmap (range (max_lab - 1))
  in 
    if (CIMap.equal ci_converged cmap ncmap) then ncmap
    else f ncmap;;

let perform dfg max_lab =
  let sp = start_point dfg max_lab in
  let fset = final_set dfg max_lab in
  fix (vb_iterate dfg fset max_lab) sp;;
