open Data_flow;;
open Rd_code;;
(* open Unparser;; *)
open Utils;;
(* open Elimination;; *)

let print_label lab =
  if lab = -1 then "?" else string_of_int (lab + 1)


let debug_rd rd_analysis max_lab = 
  let buf = Buffer.create 1024 in
  Buffer.add_string buf "REACHING DEFINITION ANALYSIS: ";
    List.iter (fun n ->
      let print_set_contents = 
        IdentLabelSet.iter (fun set -> Buffer.add_string buf ("(" ^ fst (set) ^ ", " ^ print_label (snd (set)) ^ ")")) in
        Buffer.add_string buf "Entry (";
        Buffer.add_string buf (string_of_int (n + 1));
        Buffer.add_string buf "): {";
      print_set_contents (fst (CIMap.find n rd_analysis));
      Buffer.add_string buf "} ";
      Buffer.add_string buf "Exit (";
      Buffer.add_string buf (string_of_int (n + 1));
      Buffer.add_string buf "): {";
      print_set_contents (snd (CIMap.find n rd_analysis));
      Buffer.add_string buf "} ";
      ) (range (max_lab-1));
      Buffer.contents buf;;

let xdebug_rd rd_analysis max_lab = 
  let buf = Buffer.create 1024 in
  Buffer.add_string buf "REACHING DEFINITION ANALYSIS: ";
    List.iter (fun n ->
      let print_set_contents = 
        IdentLabelSet.iter (fun set -> Buffer.add_string buf ("(" ^ fst (set) ^ ", " ^ print_label (snd (set)) ^ ")")) in
        Buffer.add_string buf "Entry (";
        Buffer.add_string buf (string_of_int (n + 1));
        Buffer.add_string buf "): {";
      print_set_contents (fst (CIMap.find n rd_analysis));
      Buffer.add_string buf "} ";
      ) ([0]);
      Buffer.contents buf;;

let debug_dfg dfg max_lab =
  let buf = Buffer.create 512 in
  Buffer.add_string buf "GENERATED DATA FLOW GRAPH: ";
  List.iter (fun n ->
    let print_children =
      List.iter (fun l -> Buffer.add_string buf ((string_of_int (l + 1)) ^ " ")) in
      Buffer.add_string buf ((string_of_int (n + 1)) ^ ": ");
      print_children (EBSet.find n dfg).children;
    ) (range (max_lab-1));
  Buffer.contents buf;;

let teste_rd input_fname =
  let input_file = open_in input_fname in
  let lexer_buffer = Lexing.from_channel input_file in
  let ast = Parser.prog Lexer.read_token lexer_buffer in 
  let (dfg, max_lab) = build_data_flow_graph ast in
  let rd_analysis = perform dfg max_lab in
    debug_rd rd_analysis max_lab;;


let teste_rd_dfg  input_fname =
  let input_file = open_in input_fname in
  let lexer_buffer = Lexing.from_channel input_file in
  let ast = Parser.prog Lexer.read_token lexer_buffer in 
  let (dfg, max_lab) = build_data_flow_graph ast in
    debug_dfg dfg max_lab;;

