open Notations
open PrintTools
open Tools
open Slsyntax

module Parser = Simplifier_parser
module Lexer = Simplifier_lexer
module SatResult = Smttoz3.SatcheckResult

(* read from file *)
let inputstr_stdin () =
let x = ref "" in
try
while true do
x := !x ^ (input_line stdin) ^ "\n"
done ;
"" (* dummy *)
with End_of_file -> !x ;;

let inputstr_file filename =
  let x = ref "" in
  let ic = open_in filename in
  try
	while true do
	  x := !x ^ (input_line ic) ^ "\n"
	done ;
	"" (* dummy *)
  with End_of_file -> close_in ic;!x
;;

(* Options *)
let _fname = ref "";;
let _debugflag = ref false;;
let _quickflag = ref false;;
let _timeout: float option ref = ref None;;
let f_help () = print_endline "help";;
let set_filename fname = _fname := fname;;
let set_debug () = _debugflag := true;;
let set_quick () = _quickflag := true;;
let set_timeout sec = _timeout := Some sec;;
  
let msgUsage =
"USAGE: tmcompare -f <filename>";;

let speclist = [
    ("-f", Arg.String set_filename, "Input file (mandatory)");
    ("-d", Arg.Unit set_debug, "debug mode");
    ("-q", Arg.Unit set_quick, "quick-check mode (check without assumptions)");
  ];;

(* parser *)
let parse str = 
  Parser.main Lexer.token
    (Lexing.from_string str)
;;
let () =
  let display_message () = print_endline msgUsage in
  Arg.parse speclist print_endline msgUsage;
  let check_fname () = if !_fname = "" then (display_message (); exit 0) else () in
  check_fname();
  let start_time_parse = Unix.gettimeofday () in
  let (p,ss) = parse (inputstr_file !_fname) in
  let end_time_parse = Unix.gettimeofday () in
  let elapsed_time_parse = end_time_parse -. start_time_parse in
  Printf.printf "Execution time: %f seconds\n" elapsed_time_parse;
  Fmt.printf "@[[Pure-formula]@.";
  Fmt.printf "@[%a@." P.pp p;  
  Fmt.printf "@[[Spatial-formula]@.";
  Fmt.printf "@[%a@." SS.pp ss;

  Tmcompare.exec !_debugflag !_quickflag p ss;
  ()

