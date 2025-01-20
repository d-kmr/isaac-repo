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
let f_help () = print_endline "help";;
let set_filename fname = _fname := fname;;
let set_raw () = _rawflag := true;;
let set_model () = _modelflag := true;;
let set_unsatcore () = _ucflag := true;;
let set_foption opt = p_opt := opt :: !p_opt;;
let set_timeout sec = _timeout := Some sec;;
  
let msgUsage =
"USAGE: simplifier [-d <TAG>|-b|-0|-t] -f <filename>";;

let speclist = [
    ("-f", Arg.String set_filename, "Input file (mandatory)");
    ("-d", Arg.String set_foption,
     "Set Foption
      Z3: show the translation result (smt2 input for Z3)
      UC: produce & show unsatcore when an input is unsat
      MD: produce & show a model when an input is sat");
    ("-0", Arg.Unit set_raw, "Use raw z3 (Only checking the pure-part with Z3 ignoring the spat-part)");
    ("-t", Arg.Int set_timeout, "Set timeout [sec] (default:4294967295)");
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
  let (p,ss) = parse (inputstr_file !_fname) in
  Fmt.printf "@[[Pure-formula]@.";
  Fmt.printf "@[%a@." P.pp p;  
  Fmt.printf "@[[Spatial-formula]@.";
  Fmt.printf "@[%a@." SS.pp ss;

  let p' = Simplifier.simplify_pure p in 
    
  Fmt.printf "@[[Simplified Pure-formula]@.";
  Fmt.printf "@[%a@." P.pp p';

  let g = WDGraph.create () in

  (* Dynamically add edges (nodes are automatically added) *)
  let _ = WDGraph.add_edge g 0 1 1 in
  let _ = WDGraph.add_edge g 2 2 0 in
  let _ = WDGraph.add_edge g 2 3 1 in
  let _ = WDGraph.add_edge g 3 0 2 in

  (* Traverse edges *)
  let edges = WDGraph.traverse_edges g in
  List.iter (fun (u, v, w) ->
      Printf.printf "Edge: %d -> %d (Weight: %d)\n"  u v w
    ) edges;
  
  let red_cycle = WDGraph.forms_cycle_with_red g in
    if red_cycle then
    Printf.printf "Red cycle found\n";

  
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
