open Data_flow;;
open Ast;;
open Utils;;


(*A map for the labels*)
module IdentLabelSet = Set.Make(struct type t = (ident * EBSet.key) let compare = compare end);;


(*Identify the free arithmetic expression variable for each statment*)
let id_lab_aExpr expr lab =
  let rec rd_aExpr expr set =
  match expr with
  | Int _ -> set
  | Ident x -> IdentLabelSet.add (x, lab) set
  | BinOp (_, a1, a2) -> let lSet = rd_aExpr a1 set in rd_aExpr a2 lSet
  | Neg -> IdentLabelSet.empty
  | _ -> IdentLabelSet.empty
  in rd_aExpr expr IdentLabelSet.empty;;

(*Identify the free boolean expression variable for each statment*)
let id_lab_bExpr expr lab =
  let rec compute expr set =
    match expr with
    | Bool _ -> set
    | Not nexpr -> compute nexpr set
    | RelOp (_, a1, a2) ->
        let lSet = id_lab_aExpr a1 lab in 
        let rSet = id_lab_aExpr a2 lab in
        IdentLabelSet.union lSet rSet
    | BoolOp (_, b1, b2) ->
        let lSet = compute b1 set in compute b2 lSet
    | _ -> IdentLabelSet.empty
  in compute expr IdentLabelSet.empty;;

let find_ident_aexp node lab = 
  match node with
    | { content = c ; children = _ } -> 
      match c with
      | Right condition_expr -> 
        (match condition_expr with
          | Condition (bexpr, _) -> id_lab_bExpr bexpr lab
          | _ -> failwith "Error. Does not exist other constructor besides Condition in condition_expr type" 
        )  
      | Left stmt ->
        (match stmt with
          | Assignment (_, aexpr, _) -> id_lab_aExpr aexpr lab
          | _ -> failwith "Error in stmt"
        );;

let ident_assign node = 
  match node with
    | { content = c ; children = _ } -> 
      match c with
      | Right condition_expr -> "" 
      | Left stmt ->
        (match stmt with
          | Assignment (x, _, _) -> x
          | _ -> failwith "Error in stmt"
        );;

let all_ident_label_set max_lab dfg =
  List.fold_left (fun allIdentLabelSet lab ->
    let node = EBSet.find lab dfg in
    IdentLabelSet.union allIdentLabelSet (find_ident_aexp node (-1))  (*-1 represents the ? label*)
  ) IdentLabelSet.empty (range (max_lab - 1));;

let all_label_assign_set max_lab dfg =
  List.fold_left (fun allLabelAssignSet lab ->
    let node = EBSet.find lab dfg in
    let identassign = ident_assign node in
    if (identassign <> "") then IdentLabelSet.add (identassign, lab) allLabelAssignSet else allLabelAssignSet
  ) IdentLabelSet.empty (range (max_lab - 1));;

let node_parents curLab max_lab dfg =
  List.fold_left(fun n lab ->    
    let node = EBSet.find lab dfg in
    if ( List.mem curLab node.children) then (n @ [lab]) else n 
  ) [] (range (max_lab - 1));;

(*Identiy the gen set of each assign and condition block of expression*)
let genc lab c =
  match c with
  | Right condition_expr -> IdentLabelSet.empty
  | Left stmt ->
    (match stmt with
     | Assignment (x, _, _) -> IdentLabelSet.singleton (x, lab)
     | _ -> IdentLabelSet.empty
    );;

(*Identiy the kill set of each assign block of expression*)
let killc allLabelAssignSet allIdentLabelSet c =
  match c with
  | Right _ -> IdentLabelSet.empty
  | Left stmt ->
      (match stmt with
       | Assignment (x, _, _) -> IdentLabelSet.union (IdentLabelSet.filter (fun (id, l) -> id = x) allIdentLabelSet) (IdentLabelSet.filter (fun (id, l) -> id = x) allLabelAssignSet)
       | _ -> IdentLabelSet.empty);;

let gen lab dfn =
  match dfn with
  | { content = c ; children = _ } -> genc lab c;;

let kill allLabelAssignSet allIdentLabelSet dfn =
  match dfn with
  | { content = c ; children = _ } -> killc allLabelAssignSet allIdentLabelSet c;;

(*Create a MAP (CIMap) witch the key is the labels and the content are a tulpe of IdentLabelSet ({entry}, {exit}). See range in utils file. It return a list of labels, but starting on zero [0; 1; 2] *)
module CIMap = Map.Make(struct type t = EBSet.key let compare = compare end);;
let start_point max_lab = 
  List.fold_left (fun m n -> CIMap.add n (IdentLabelSet.empty, IdentLabelSet.empty) m) CIMap.empty (range (max_lab - 1));;

let ci_converged prev_it cur_it =
  let (prev_entry, prev_exit) = prev_it and
      (cur_entry, cur_exit) = cur_it in
      IdentLabelSet.equal prev_entry cur_entry && IdentLabelSet.equal prev_exit cur_exit;;
  
(*Create a new IdentLabelSet with all pairs of (x; lab ?). See pag 44 (table 2.2 - entry) - We will use -1 as ? (unknow label)*)
let rd_entry allIdentLabelSet max_lab dfg lab cmap  =
let nodeparents = node_parents lab max_lab dfg in
if lab = 0 then (*Init - If it is the first block*)
  allIdentLabelSet
else 
  List.fold_left  (fun s l -> IdentLabelSet.union s (snd (CIMap.find l cmap))) (*Second means the exit node*)
  IdentLabelSet.empty nodeparents;; (*In this forward analysis it is necessary iterate over the exit sets of the parants*)
  
  let rd_exit allLabelAssignSet allIdentLabelSet lab entry node =
    IdentLabelSet.union (IdentLabelSet.diff entry (kill allLabelAssignSet allIdentLabelSet node)) (gen lab node);;

let rd_iterate idfg max_lab f cmap =
  let allIdentLabelSet = all_ident_label_set max_lab idfg in
  let allLabelAssignSet = all_label_assign_set max_lab idfg in
  let ncmap = List.fold_left (fun m n ->
    let (entry, exit) = CIMap.find n m in (*The entry and exit node set receive the tuple (IdentLabelSet, IdentLabelSet) referent the label from CIMap *)
    let node = EBSet.find n idfg in
    let nentry = rd_entry allIdentLabelSet max_lab idfg n m in
    let nexit = rd_exit allLabelAssignSet allIdentLabelSet n entry node in
    CIMap.add n (nentry, nexit) m) cmap (range (max_lab - 1))
  in 
    if (CIMap.equal ci_converged cmap ncmap) then ncmap
    else f ncmap;;

let perform dfg max_lab = (*Receive the data flow graph of the program and the value of the max label*)
  let sp = start_point max_lab in (*See the comments in start_point expression*)
  fix (rd_iterate dfg max_lab) sp;; (*Execute rd_iterate until the fix point is achieved*)
