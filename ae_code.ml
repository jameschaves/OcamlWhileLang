open Ast;;
open Data_flow;;
open Utils;;

(* module AexprSet = Set.Make(struct type t = expr let compare = compare end);; *)

module AexprSet = Set.Make(struct type t = expr let compare = compare end);;

(*A map for the labels*)
(* module LabelSet = Set.Make(struct type t = EBSet.key let compare = compare end);; *)

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



  (*Filter over AExprset to find Aexp with x ident*)
let rec ident_filter x exp =
  match exp with
  | BinOp(_, a1, a2) -> eval_aexp a1 x || eval_aexp a2 x
  | RelOp(_, a1, a2) -> eval_aexp a1 x || eval_aexp a2 x
  | _ -> failwith "Error in filter type"
  and eval_aexp aexp x =
  match aexp with 
    | Ident a -> a = x
    | _ -> false;;

(*Identify the free arithmetics expressions for each assgn*)
let available_aexpr expr =
  let rec ae_aexpr expr s =
  match expr with
  | BinOp (_, a1, a2) -> AexprSet.add expr s
  | _ -> AexprSet.empty
  in ae_aexpr expr AexprSet.empty;;

(*Identify the free boolean expression variable for each condition*)
let available_bexpr expr =
  let rec compute expr s =
    match expr with
    | Not nexpr -> compute nexpr s
    | RelOp (_, a1, a2) ->
        let lh = available_aexpr a1 in 
        let rh = available_aexpr a2 in
        AexprSet.union lh rh
    | _ -> AexprSet.empty
  in compute expr AexprSet.empty;;
  
 (*Identiy the gen set of each assign block of expression*)
let genc aExpSet c =
  match c with
  | Right condition_expr -> 
    (match condition_expr with
     | Condition (bexpr, _) -> available_bexpr bexpr
     | _ -> AexprSet.empty 
    )  
  | Left stmt ->
    (match stmt with
    | Assignment (x, expr, _) -> AexprSet.diff (available_aexpr expr) (AexprSet.filter (ident_filter x) aExpSet) (*Filter in all aExp those that have the identifier been modified in the right side hand, then extract this set from the whole set of /AExp*)
    | _ -> AexprSet.empty (*The other statement do not gen AE*)
    );;

     
 (*Identiy the kill set of each assign and condition block of expression*)
 let killc aExpSet c  =
  match c with
  | Right _ -> AexprSet.empty (*Refer to condition. In AE the kill set is {}*)
  | Left stmt ->
      match stmt with
       | Assignment (x, expr, _) -> AexprSet.filter (ident_filter x) aExpSet (*Filter in all aExp those that have the identifier been modified in the right side hand*)
       | Skip _ -> AexprSet.empty (*For Skip, in AE the kill set is {}*)
       | _ -> failwith "Error in kill type"
      

let gen aExpSet dfn =
  match dfn with
  | { content = c ; children = _ } -> genc aExpSet c;;

let kill aExpSet dfn =
  match dfn with
  | { content = c ; children = _ } -> killc aExpSet c;;

(*Create a new MAP with the set {assingment ; condition} index by labels (EBSet.key) from data_flow*)
module CIMap = Map.Make(struct type t = EBSet.key let compare = compare end);;

let start_entry lab dfg =
  let node = EBSet.find lab dfg in
  find_aexp_node node AexprSet.empty;;

(*Populate de CIMap. The entry and exist sets will receive this MAP as start*)
(*Unlike the Live Variable analysis, the entry set is composed of the aExp that appear in the block*)
let start_point max_lab = 
  List.fold_left (fun m n -> CIMap.add n (AexprSet.empty, AexprSet.empty) m) CIMap.empty (range (max_lab - 1));;

let ci_converged prev_it cur_it =
  let (prev_entry, prev_exit) = prev_it and
      (cur_entry, cur_exit) = cur_it in
      AexprSet.equal prev_entry cur_entry && AexprSet.equal prev_exit cur_exit;;

let node_parents curLab max_lab dfg =
  List.fold_left(fun n lab ->    
    let node = EBSet.find lab dfg in
    if ( List.mem curLab node.children) then (n @ [lab]) else n 
  ) [] (range (max_lab - 1));;

let ae_entry max_lab dfg aExpSet lab  cmap node =
  let nodeparents = node_parents lab max_lab dfg in
  if lab = 0 then (*Init - If it is the first block*)
    AexprSet.empty
  else 
    List.fold_left  (fun s l -> AexprSet.inter s (snd (CIMap.find l cmap))) (*Second means the exit node*)
      aExpSet nodeparents;; (*In this forward analysis it is necessary iterate over the exit sets of the parants*)

let ae_exit aExpSet cmap entry node =
  AexprSet.union (AexprSet.diff entry (kill aExpSet node)) (gen aExpSet node);;

let ae_iterate idfg max_lab f cmap =
  let aExpSet = aExps_set idfg max_lab in (*Creat a set of all aExp in the program*)
  let ncmap = List.fold_left (fun m n ->
    let (entry, exit) = CIMap.find n m in (*Get the actual AExprSet for entry and exit sets of the label*)
    let node = EBSet.find n idfg in (*Get the node (Label, contentet[Left stmt, Right condition] and children)*)
    let nentry = ae_entry max_lab idfg aExpSet n m node in (*Recalculate the new AExprSet for the entry node*)
    let nexit = ae_exit aExpSet m entry node in (*Recalculate the new AExprSet for the exit node*)
    CIMap.add n (nentry, nexit) m) (*Replace the new calculeted AExprSet entry and exit nodes in the CIMap *)
    cmap (range (max_lab - 1)) 
  in 
    if (CIMap.equal ci_converged cmap ncmap) then ncmap (*If the convergence is achieved, end loop*)
    else f ncmap;; (*Otherwise iterate again*)

let perform dfg max_lab =
  let sp = start_point max_lab in
  fix (ae_iterate dfg max_lab) sp;;
