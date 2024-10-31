open Notations

(* Print functions *)
(* Color printf *)
let printf_color color fmt =
  let buf = Buffer.create 0 in
  let ppf = Fmt.formatter_of_buffer buf in
  let sty = [ANSITerminal.Bold; ANSITerminal.Foreground color] in
  Fmt.kfprintf (fun ppf -> Fmt.pp_print_flush ppf (); ANSITerminal.printf sty "%s" (Buffer.contents buf)) ppf fmt

let printf_yellow fmt = printf_color ANSITerminal.Yellow fmt
let printf_red fmt = printf_color ANSITerminal.Red fmt
let printf_white fmt = printf_color ANSITerminal.White fmt
let printf_blue fmt = printf_color ANSITerminal.Blue fmt
                      
(* Conditional fprintf *)
let cfprintf cond ppf = if cond then Fmt.fprintf ppf else Fmt.ifprintf ppf 
;;
let cprintf cond = cfprintf cond Fmt.std_formatter
;;
let cprintf_color cond color fmt =
  if cond
  then
    printf_color color fmt
    (*
    let buf = Buffer.create 0 in
    let ppf = Fmt.formatter_of_buffer buf in
    let sty = [ANSITerminal.Bold; ANSITerminal.Foreground color] in
    Fmt.kfprintf (fun ppf -> Fmt.pp_print_flush ppf (); ANSITerminal.printf sty "%s" (Buffer.contents buf)) ppf fmt
     *)
  else
    Fmt.ikfprintf (fun ppf -> ()) Fmt.std_formatter fmt
;;

(* Error handling
Example: try_or_exit cmd "%s" "error message" 
This executes cmd. If an exception is raised, then immediately exit with printing "error message" *)
let try_or_exit cmd fmt = cprintf (try cmd; true with _ -> false) fmt

let printf_and_exit fmt =
  let buf = Buffer.create 0 in
  let ppf = Fmt.formatter_of_buffer buf in
  Fmt.kfprintf (fun ppf -> Fmt.pp_print_flush ppf (); Fmt.printf "@[%s@." (Buffer.contents buf); exit 0) ppf fmt
;;                        
                        
(* Debugging tag lists *)
let p_opt : string list ref = ref []
             
let p str = Fmt.printf "@[%s@]" str
let pn str = Fmt.printf "@[%s@." str
let pw str = Fmt.printf "@[%s @]" str
(* let pi str = pn (string_of_int str) *)
(* let pl str = p (string_of_int str) *)
let pb b = if b then p "True" else p "False"

let pf_s tag f s = if (tag |<- !p_opt) || ("ALL" |<- !p_opt) then f s

let p_s tag s = pf_s tag p s

let pn_s tag s = pf_s tag pn s

let mkIndent n = String.make (2*n) ' '

let pp_indent ppf n = Fmt.fprintf ppf "%s" (mkIndent n)
                
let dbg tag c f d = if tag |<- !p_opt then (Fmt.printf "@[%s @]" c; f d; Fmt.printf "@[@.") else ()

let dbg_iter tag c f dd = dbg tag c (List.iter f) dd
                  
let dbgf tag = cprintf (tag |<- !p_opt)
             
let dbg_blue tag = cprintf_color (tag |<- !p_opt) ANSITerminal.Blue
;;
let dbg_red tag = cprintf_color (tag |<- !p_opt) ANSITerminal.Red
;;
let dbg_yellow tag = cprintf_color (tag |<- !p_opt) ANSITerminal.Yellow
;;
let dbg_green tag = cprintf_color (tag |<- !p_opt) ANSITerminal.Green
;;
(* ANSITerminal.(printf [Bold; Foreground White]) "\nBEGIN: Biabduction\n"; *)

let pp_sep_fmt fmt = fun ppf () -> Format.fprintf ppf fmt

let pp_list_with pp_a fmt ppf l = Fmt.pp_print_list ~pp_sep:(pp_sep_fmt fmt) pp_a ppf l
                                
let rec pt str = function
	| 0 -> p str
	| n -> p "    "; pt str (n-1)
               
let raiseMes mes e = (print_endline ("Error: " ^ mes); raise e);;

let raiseError mes = raiseMes mes (Error mes);;

let fontDebug1 = ANSITerminal.([Foreground Yellow]);;

let fontDebug2 = ANSITerminal.([Foreground Green]);;

let print_debug1 mes = ANSITerminal.printf fontDebug1 "%s" mes;;

let println_debug1 mes = ANSITerminal.printf fontDebug1 "%s\n" mes;;

let print_debug2 mes = ANSITerminal.printf fontDebug2 "%s" mes;;

let println_debug2 mes = ANSITerminal.printf fontDebug2 "%s\n" mes;;

let stdout = Fmt.std_formatter;;

let pp_opt none pp ppf opt =
  match opt with
  | None -> Fmt.fprintf ppf "%s" none
  | Some u -> Fmt.fprintf ppf "%a" pp u
;;
let pp_bool ppf b =
  match b with
  | true -> Fmt.fprintf ppf "true"
  | false -> Fmt.fprintf ppf "false"
;;
let pp_list base sep pp ppf xx =
  match xx with
  | [] -> Fmt.fprintf ppf "@[%s@]" base
  | _ -> Fmt.fprintf ppf "@[<h 100>%a@]" (Fmt.pp_print_list ~pp_sep:(fun _ _ -> Fmt.fprintf ppf sep) pp) xx
;;
let pp_list_ln base sep pp ppf xx = (* if xx <> [] then finish with a newline *)
  match xx with
  | [] -> Fmt.fprintf ppf "@[%s@]" base
  | _ -> Fmt.fprintf ppf "@[<h 100>%a@." (Fmt.pp_print_list ~pp_sep:(fun _ _ -> Fmt.fprintf ppf sep) pp) xx
;;
let pp_list_comma pp = pp_list "" "," pp 
;;
let pp_list_space pp = pp_list "" " " pp 
;;
let pp_list_space0 fmt pp = pp_list_space (fun ppf -> Fmt.fprintf ppf fmt pp)
;;
let pp_list_nospace pp = pp_list "" "" pp 
;;
let pp_list_newline pp = pp_list "" "\n" pp
;;
let pp_list_newline0 fmt pp = pp_list_newline (fun ppf -> Fmt.fprintf ppf fmt pp)
;;
let pp_list_newline_ln pp = pp_list_ln "" "\n" pp
;;
let pp_list_semicol pp = pp_list "" ";" pp
;;
let pp_one fmt pp ppf x = Fmt.fprintf ppf fmt pp x
;;  
let pp_pair0 fmt pp1 pp2 ppf (x1,x2) = Fmt.fprintf ppf fmt pp1 x1 pp2 x2
;;
let pp_pair pp1 pp2 = pp_pair0 "@[<h>(%a,%a)@]" pp1 pp2
;;
let pp_triple0 fmt pp1 pp2 pp3 ppf (x1,x2,x3) = Fmt.fprintf ppf fmt pp1 x1 pp2 x2 pp3 x3
;;
let pp_triple pp1 pp2 pp3 = pp_triple0 "@[<h>(%a,%a,%a)@]" pp1 pp2 pp3
;;
let pp_string = Fmt.pp_print_string 
;;
let pp_string_list_comma = pp_list_comma pp_string
;;
let pp_int = Fmt.pp_print_int
;;
let print_string' str = print_string str; flush_all()
;;
let pp_V base sep pp ppf xx = Fmt.fprintf ppf "%a" (pp_list base sep (pp_pair pp_string pp)) (V.bindings xx)
;;
let pp_V_comma pp = pp_V "" "," pp 
;;
let pp_V_space pp = pp_V "" " " pp 
;;
let pp_V_nospace pp = pp_V "" "" pp 
;;
let pp_V_newline pp = pp_V "" "\n" pp 
;;
let pp_V_semicol pp = pp_V "" ";" pp
;;
