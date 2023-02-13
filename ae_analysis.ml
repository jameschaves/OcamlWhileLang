open Data_flow;;
open Ae_code;;
open Utils;;

let debug_ae ae_analysis max_lab = 
    print_endline "AVAILABLE EXPRESSIONS ANALYSIS:";
    List.iter (fun n ->
      let print_set_contents = 
        AexprSet.iter (fun x -> print_string (string_of_expr x ^ " ")) in
      print_string "Entry (";
      print_string (string_of_int (n + 1));
      print_string "): ";
      print_set_contents (fst (CIMap.find n ae_analysis));
      print_newline();
      print_string "Exit (";
      print_string (string_of_int (n + 1));
      print_string "): ";
      print_set_contents (snd (CIMap.find n ae_analysis));
      print_newline()) (range (max_lab-1));;

let debug_dfg dfg max_lab =
  print_endline "GENERATED DATA FLOW GRAPH:";
  List.iter (fun n ->
    let print_children =
      List.iter (fun l -> print_string ((string_of_int (l + 1)) ^ " ")) in
    print_string ((string_of_int (n + 1)) ^ ": ");
    print_children (EBSet.find n dfg).children;
    print_newline()) (range (max_lab-1));;

let input_fname =
  if Array.length Sys.argv > 1 then
    Sys.argv.(1)
  else
    "programs/ppa_pg42_teste_ae.while";;

let main argv argc =
  let input_file = open_in input_fname in
  let lexer_buffer = Lexing.from_channel input_file in
  let ast = Parser.prog Lexer.read_token lexer_buffer in 
  let (dfg, max_lab) = build_data_flow_graph ast in
  let ae_analysis =  perform dfg max_lab  in
    debug_ae ae_analysis max_lab;
    debug_dfg dfg max_lab;;


main () ();;