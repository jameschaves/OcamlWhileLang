open OUnit2
open Ast
open Data_flow;;
open Ae_code;;
open Utils;;

let input_fname_ae = "programs/ppa_pg42_teste_ae.while";;

let teste_ae =
  let input_file = open_in input_fname_ae in
  let lexer_buffer = Lexing.from_channel input_file in
  let ast = Parser.prog Lexer.read_token lexer_buffer in 
  let (dfg, max_lab) = build_data_flow_graph ast in
  let ae_analysis =  perform dfg max_lab  in
    debug_ae ae_analysis max_lab;;
    (* debug_dfg dfg max_lab;; *)

let ae_analysy_result = "AVAILABLE EXPRESSIONS ANALYSIS:
Entry (1):
Exit (1): [a + b]
Entry (2): [a + b]
Exit (2): [a + b] [a * b]
Entry (3): [a + b]
Exit (3): [a + b]
Entry (4): [a + b]
Exit (4):
Entry (5): Exit (5): [a + b]"

let make_ae n i s = 
  n >:: (fun _ -> assert_equal ae_analysy_result (teste_ae s))
 
let tests = [
  (* make_i "int" 22 "22"; 
  make_i "add" 22 "11+11";
  make_i "mult" 22 "2*11";
  make_i "multi of multi" 40 "2*2*10";
  make_i "mult on right of add" 22 "2+2*10";
  make_i "mult on left of add" 14 "2*2+10";
  make_i "nested add" 22 "(10 + 1) + (5 + 6)"; *)
 ]

let _ = run_test_tt_main ("suite" >::: tests)