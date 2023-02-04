open Data_flow;;
open Utils;;

let debug_dfg dfg max_lab =
  print_endline "GENERATED DATA FLOW GRAPH:";
  List.iter (fun n ->
    let print_children =
      List.iter (fun l -> print_string ((string_of_int l) ^ " ")) in
    print_string ((string_of_int n) ^ ": ");
    print_children (EBSet.find n dfg).children;
    print_newline()) (range (max_lab-1));;

let input_fname =
  if Array.length Sys.argv > 1 then
    Sys.argv.(1)
  else
    "programs/example.while";;

let main argv argc =
  let input_file = open_in input_fname in
  let lexbuf = Lexing.from_channel input_file in
  let ast = Parser.prog Lexer.read_token lexbuf in 
  let (dfg, max_lab) = build_data_flow_graph ast in
    debug_dfg dfg max_lab;
    print_endline "ELIMINATED CODE:";;

main () ();;
