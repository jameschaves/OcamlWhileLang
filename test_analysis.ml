open OUnit2
open Rd_test;;


let rd_analysis_result = "REACHING DEFINITION ANALYSIS: Entry (1): {(x, ?)(y, ?)} Exit (1): {(x, 1)(y, ?)} Entry (2): {(x, 1)(y, ?)} Exit (2): {(x, 1)(y, 2)} Entry (3): {(x, 1)(x, 5)(y, 2)(y, 4)} Exit (3): {(x, 1)(x, 5)(y, 2)(y, 4)} Entry (4): {(x, 1)(x, 5)(y, 2)(y, 4)} Exit (4): {(x, 1)(x, 5)(y, 4)} Entry (5): {(x, 1)(x, 5)(y, 4)} Exit (5): {(x, 5)(y, 4)} "

let make_rd n a s = 
  n >:: (fun _ -> assert_equal a (teste_rd s))
 
let tests = [
  make_rd "RD Analysis: " rd_analysis_result "programs/ppa_pg43_teste_rd.while"; 
  (*make_i "add" 22 "11+11";
  make_i "mult" 22 "2*11";
  make_i "multi of multi" 40 "2*2*10";
  make_i "mult on right of add" 22 "2+2*10";
  make_i "mult on left of add" 14 "2*2+10";
  make_i "nested add" 22 "(10 + 1) + (5 + 6)"; *)
 ]

let _ = run_test_tt_main ("suite" >::: tests)