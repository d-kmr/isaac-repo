open Notations
open PrintTools
open Tools
open Slsyntax
open Wdg


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
let _rawflag = ref false;;
let _modelflag = ref false;;
let _ucflag = ref false;;
let _bnflag = ref false;;
let _timeout = ref None;;
let _stats = ref false;;
let _normalize = ref false;;
let _serialize = ref false;;
let _pretty_print = ref false;;
let _debugflag = ref false;;
let _quickflag = ref false;;
let f_help () = print_endline "help";;
let set_filename fname = _fname := fname;;
let set_raw () = _rawflag := true;;
let set_model () = _modelflag := true;;
let set_unsatcore () = _ucflag := true;;
let set_foption opt = p_opt := opt :: !p_opt;;
let set_timeout sec = _timeout := Some sec;;
let set_stats () = _stats := true;;
let set_normalize () = _normalize := true;;
let set_serialize () = _serialize := true;;
let set_pretty_print () = _pretty_print := true;;
let set_debug () = _debugflag := true;;
let set_quick () = _quickflag := true;;
  
let msgUsage =
"USAGE: simplifier [-d <TAG>|-b|-0|-t|-s] -f <filename>";;

let speclist = [
    ("-f", Arg.String set_filename, "Input file (mandatory)");
    ("-d", Arg.String set_foption,
     "Set Foption
      Z3: show the translation result (smt2 input for Z3)
      UC: produce & show unsatcore when an input is unsat
      MD: produce & show a model when an input is sat");
    ("-0", Arg.Unit set_raw, "Use raw z3 (Only checking the pure-part with Z3 ignoring the spat-part)");
    ("-n", Arg.Unit set_normalize, "Use partial application of reduction algorithm to conjunctions (input will not be normalized to DNF)");
    ("-t", Arg.Int set_timeout, "Set timeout [sec] (default:4294967295)");
    ("-s", Arg.Unit set_stats, "Reports execution stats (execution time for now)");
    ("-g", Arg.Unit set_serialize, "Generates dot code to visualize graphs");
    ("-p", Arg.Unit set_pretty_print, "Prints graph in a human readable format");
    ("-b", Arg.Unit set_debug, "debug mode for z3");
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

  if !_normalize then (
    let p' =  Simplifier.simplify_pure_spat p ss !_stats !_debugflag !_quickflag !_serialize !_pretty_print in
    Fmt.printf "@[[Simplified formula]@.";
    Fmt.printf "@[%a@." DisjSH.ppln p';
  )
  else (
  let p' = Simplifier.partial_simplify_pure_spat p ss !_stats !_debugflag !_quickflag !_serialize !_pretty_print in
    Fmt.printf "@[[Simplified formula]@.";
    Fmt.printf "@[%a@." P.pp p'; 
    Fmt.printf "@[&&@.";
    Fmt.printf "@[%a@." SS.pp ss;
  ) 
  
(*  
  let (startMesRaw,ssMes) = if !_rawflag then ("RAW-MODE ","Ignored") else ("","") in
  Fmt.printf "@[Satchecker %s@." startMesRaw;
  Fmt.printf "@[[INPUT]@.";
  Fmt.printf "@[Pure: %a@." P.pp p;
  Fmt.printf "@[Spat: %a\n@." SS.pp ss;
  let sh = (p,ss) in
  pf_s "MD" set_model ();
  pf_s "UC" set_unsatcore ();
  let result =
    if !_rawflag
    then Smttoz3.checkSatExp !_modelflag !_ucflag (Sltosmt.mkExp_p p)
    else Satcheck.satcheck_hat !_modelflag !_ucflag sh
  in
  Fmt.printf "@[[RESULT]@.";
  match result,!_modelflag,!_ucflag with
  | SatResult.Model model,true,_ ->
     Fmt.printf "@[SAT\n@.";
     Fmt.printf "@[[Model]\n%a@." SatResult.pp_model model
  | SatResult.Model model,false,_ ->
     Fmt.printf "@[SAT@."          
  | SatResult.UnsatCore uc,_,true ->
     Fmt.printf "@[UNSAT\n@.";
     Fmt.printf "[Unsatcore]\n%a@." SatResult.pp_unsatcore uc
  | SatResult.UnsatCore uc,_,false ->
     Fmt.printf "@[UNSAT@."
  | SatResult.Unknown,_,_ ->
     Fmt.printf "@[UNKNOWN@."
 *)
;;
