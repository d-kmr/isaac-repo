open Notations
open PrintTools
open Tools
open Slsyntax
   
module SatResult = Smttoz3.SatcheckResult
                 
(* extract the consistent condition (written in a pure formula) of ss *)
(* gamma (t->_ * Arr(a,b) * Str(c,d)) is (a <= b & c <= d & Disj(t,t,a,b) & Disj(t,t,c,d) & Disj(a,b,c,d) *)
let gamma ss : P.t list =
  let seg = List.map S.mkInterval ss in
  let condSeg = List.flatten @@ List.map (fun (t,u) -> [zero <.< t; t <.= u]) seg in
  let condDisj = applyDiff (fun (ti,ui) (tj,uj) -> _Disj ti ui tj uj) seg in
  List.rev_append condDisj condSeg
;;

let get_term_relations debugflag quickflag p ss =
  let pp_ss = gamma ss in
  let pp_asmp = if quickflag then [] else p::pp_ss in
  let tt_p: Tset.t = P.terms p in (* extract the set of terms in p *)
  let tt_ss: Tset.t = SS.terms ss in (* extract the set of terms in ss *)
  let ttl: T.t list = Tset.elements (Tset.union tt_p tt_ss) in
  let ttl_nc: T.t list = List.filter (fun t -> not(T.isConst t)) ttl in
  let ttl_c: T.t list = List.filter (fun t -> T.isConst t) ttl in
  let ttl = ttl_nc @ ttl_c in
  let tt: T.t array = Array.of_list ttl in
  let tt_nc: T.t array = Array.of_list ttl_nc in
  let len = List.length ttl in
  let len_nc = List.length ttl_nc in
  let total = ((len_nc-1)*len_nc)/2 + (len-len_nc)*len_nc in (* # of (t,u) + # of (t,n) *)
  let res_eq = ref [] in
  let res_lt = ref [] in    
  let res_le = ref [] in
  let counter = ref 1 in
  Fmt.printf "@[Assumption: %a@." (pp_list "" " & " P.pp) pp_asmp;
  Fmt.printf "@[# of terms@.";
  Fmt.printf "@[- all: %d@." len;
  Fmt.printf "@[- non-const: %d@." len_nc;
  if debugflag then Fmt.printf "@[{%a}@." (pp_list "" ", " T.pp) ttl_nc else ();  
  Fmt.printf "@[- const: %d@." (len-len_nc);
  if debugflag then Fmt.printf "@[{%a}@." (pp_list "" ", " T.pp) ttl_c else ();  
  Fmt.printf "@[- total: %d@." total;
  (* main routine *)
  let myexec report = 
    for i = 0 to len_nc-1 do
      for j = i+1 to len-1 do
        let ti,tj = tt_nc.(i),tt.(j) in
        if debugflag then Fmt.printf "@[[%d/%d] Checking (%a,%a): @]" !counter total T.pp ti T.pp tj else ();
        if Sltosmt.entailPure pp_asmp (P.Atom(P.Eq,[ti;tj]))
        then
          (if debugflag then Fmt.printf "@[=@." else ();
           res_eq := (ti,tj) :: !res_eq)
        else
          if Sltosmt.entailPure pp_asmp (P.Atom(P.Lt,[ti;tj]))
          then
            (if debugflag then Fmt.printf "@[<@." else ();
             res_lt := (ti,tj) :: !res_lt)
          else
            if Sltosmt.entailPure pp_asmp (P.Atom(P.Lt,[tj;ti]))
            then
              (if debugflag then Fmt.printf "@[>@." else ();
               res_lt := (tj,ti) :: !res_lt)
            else
              if Sltosmt.entailPure pp_asmp (P.Atom(P.Le,[ti;tj]))
              then
                (if debugflag then Fmt.printf "@[<=@." else ();
                 res_le := (ti,tj) :: !res_le)
              else
                if Sltosmt.entailPure pp_asmp (P.Atom(P.Le,[tj;ti]))
                then
                  (if debugflag then Fmt.printf "@[>=@." else ();
                   res_le := (tj,ti) :: !res_le)
                else (if debugflag then Fmt.printf "@[None@." else ());
        report 1; (* add 1 to the (internal) counter for each execution *)
        counter := !counter + 1
      done;
    done
  in
  (* execution with a progress bar *)
  let module PLine = Progress.Line in
  let myline = PLine.list [PLine.bar total; PLine.count_to total] in (* progress-bar format, like:"[###--] 100/200" *)
  Progress.with_reporter myline myexec; (* execute myexec with a progress-bar in the above format *)
  (!res_eq,!res_lt,!res_le)

let exec debugflag quickflag p ss =
  let (eq,lt,le) = get_term_relations debugflag quickflag p ss in
  List.iter (fun (t,u) -> Fmt.printf "@[%a = %a@." T.pp t T.pp u) eq;
  List.iter (fun (t,u) -> Fmt.printf "@[%a < %a@." T.pp t T.pp u) lt;
  List.iter (fun (t,u) -> Fmt.printf "@[%a <= %a@." T.pp t T.pp u) le
  
