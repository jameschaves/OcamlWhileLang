open Data_flow;;
open Ast;;
open Utils;;


(*A map for the variables that appear in the arithmetics expressions *)
module IdentSet = Set.Make(struct type t = ident let compare = compare end);;
(*A map for the labels*)
module LabelSet = Set.Make(struct type t = EBSet.key let compare = compare end);;

(*Identify the free arithmetics expressions for each assgn*)
let very_busy_aexpr expr =
  let rec vb_aexpr expr s =
  match expr with
  | Ident x -> IdentSet.add x s
  | BinOp (_, a1, a2) -> let lh = vb_aexpr a1 s in vb_aexpr a2 lh
  | _ -> IdentSet.empty
  in vb_aexpr expr IdentSet.empty;;

(*Identify the free boolean expression variable for each condition*)
let very_busy_bexpr expr =
  let rec compute expr s =
    match expr with
    | Not nexpr -> compute nexpr s
    | RelOp (_, a1, a2) ->
        let lh = very_busy_aexpr a1 in 
        let rh = very_busy_aexpr a2 in
        IdentSet.union lh rh
    | _ -> IdentSet.empty
  in compute expr IdentSet.empty;;
  
 (*Identiy the gen set of each assign block of expression*)
let genc c =
  match c with
  | Right condition_expr -> 
    (match condition_expr with
     | Condition (bexpr, _) -> very_busy_aexpr bexpr
     | _ -> IdentSet.empty 
    )  
  | Left stmt ->
    (match stmt with
     | Assignment (_, aexpr, _) -> very_busy_aexpr aexpr
     | _ -> IdentSet.empty (*The other statement do not gen VB*)
    );;

 (*Identiy the kill set of each assign and condition block of expression*)
 let killc c =
  match c with
  | Right _ -> IdentSet.empty
  | Left stmt ->
      (match stmt with
       | Assignment (x, _, _) -> IdentSet.singleton x
       | _ -> IdentSet.empty
      );;

let gen dfn =
  match dfn with
  | { content = c ; children = _ } -> genc c;;

let kill dfn =
  match dfn with
  | { content = c ; children = _ } -> killc c;;

let final_set dfg max_lab = 
  List.fold_left (fun finalset lab ->
    let node = EBSet.find lab dfg in
      match List.filter (fun chl -> chl > lab) node.children with
      | [] -> LabelSet.add lab finalset
      | _ -> finalset) LabelSet.empty (range (max_lab - 1));;

module CIMap = Map.Make(struct type t = EBSet.key let compare = compare end);;

let start_point max_lab = 
  List.fold_left (fun m n -> CIMap.add n (IdentSet.empty, IdentSet.empty) m) CIMap.empty (range (max_lab - 1));;

let ci_converged prev_it cur_it =
  let (prev_entry, prev_exit) = prev_it and
      (cur_entry, cur_exit) = cur_it in
    IdentSet.equal prev_entry cur_entry && IdentSet.equal prev_exit cur_exit;;

let vb_entry exit node =
  IdentSet.union (IdentSet.diff exit (kill node)) (gen node);;

let vb_exit final_set n cmap node =
  if LabelSet.mem n final_set then 
    IdentSet.empty
  else 
    List.fold_left 
      (fun s l -> IdentSet.inter s (fst (CIMap.find l cmap))) 
      IdentSet.empty node.children;;

let vb_iterate idfg final_set max_lab f cmap =
  let ncmap = List.fold_left (fun m n ->
    let (entry, exit) = CIMap.find n m in
    let node = EBSet.find n idfg in
    let nentry = vb_entry exit node in
    let nexit = vb_exit final_set n m node in
    CIMap.add n (nentry, nexit) m) cmap (range (max_lab - 1))
  in 
    if (CIMap.equal ci_converged cmap ncmap) then ncmap
    else f ncmap;;

let perform dfg max_lab =
  let sp = start_point max_lab in
  let fset = final_set dfg max_lab in
  fix (vb_iterate dfg fset max_lab) sp;;
