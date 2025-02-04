(*
  Simplifier of Symbolic Heaps
*)
open Slsyntax
open Wdg

(* 
Currently the pure formullae follows the following grammar (Quantifier free formulae):

x,y,... ∈ Variables
t ::= x | n ∈ Z | t + t | t - t | t * t | t / t | t & t | t || t | t ⊕ t | ~t | t mod n  for  n ∈ Z | t << t | t >> t
p ::= t = t | t != t | t < t | t <= t | t > t | t >= t | True | False 
P ::= p | P ∧ P$ | P v P | P -> P | ¬P

*)

(* Remove implications and biconditionals *)
let rec remove_implications (p: SHpure.t) : SHpure.t =
  match p with
  | True -> p
  | False -> p
  | Atom _ -> p 
  | Neg f -> Neg (remove_implications f)
  | And clauses -> And (List.map remove_implications clauses)
  | Or clauses -> Or (List.map remove_implications clauses)
  | Imp (a, b) -> Or [Neg (remove_implications a); remove_implications b]
  | _ -> p (*TODO: Cover All, Ex nodes*)

(* Push negations inward using De Morgan's *)
let rec push_negations (p: SHpure.t) : SHpure.t =
  match p with
  | True -> p
  | False -> p
  | Atom _ -> p
  | Neg (Atom _ as l) -> SHpure.dual l
  | Neg (Neg f) -> push_negations f  (* Double negation elimination *)
  | Neg (And clauses) ->
      Or (List.map (fun f -> push_negations (Neg f)) clauses)  (* De Morgan's *)
  | Neg (Or clauses) ->
      And (List.map (fun f -> push_negations (Neg f)) clauses)  (* De Morgan's *)
  | And clauses -> And (List.map push_negations clauses)
  | Or clauses -> Or (List.map push_negations clauses)
  | _ -> failwith "ERROR: Unexpected formula structure during negation push"


(* Distribute conjunctions over disjunctions *)
let rec distribute (p: SHpure.t) : SHpure.t=
  match p with
  | Or clauses -> Or (List.map distribute clauses)  (* Apply recursively to ORs *)
  | And [a; b] ->
      let a' = distribute a in
      let b' = distribute b in
      (match (a', b') with
       | (Or a_clauses, _) ->
           Or (List.map (fun a_clause -> distribute (And [a_clause; b'])) a_clauses)
       | (_, Or b_clauses) ->
           Or (List.map (fun b_clause -> distribute (And [a'; b_clause])) b_clauses)
       | _ -> And [a'; b'])  (* Already in AND form, no further distribution needed *)
  | And clauses -> And (List.map distribute clauses)
  | _ -> p

(*let identity_element p = 
  match p with
  | Add _ -> 0
  | Sub _ -> 0
  | Mul _ -> 1
  | Div _ -> 1
  | Mod _ -> 1
  | Shr _ -> 0
  | Shl _ -> 0
  | Band _ -> 1
  | Bor _ -> 0*)

let rec filter_identities (e : Slsyntax.SHterm.t) : Slsyntax.SHterm.t =
  match e with
  |SHterm.Add args -> 
    let neutral_elem_zero = List.filter (function SHterm.Int 0 -> false | _ -> true) args in
    SHterm.Add (List.map filter_identities neutral_elem_zero)
  |SHterm.Sub args -> 
    let neutral_elem_zero = List.filter (function SHterm.Int 0 -> false | _ -> true) args in
    SHterm.Sub (List.map filter_identities neutral_elem_zero)
  
  |Mul t0, Int 1 -> t0
  |Mul Int 1, t1 -> t1
  |Mul Int x, Int y -> Int (x*y)
  |Mul t0, t1 -> Mul t0, t1

  |Div t0, Int 1 -> t0
  |Div Int x, Int y -> Int (x/y)
  |Div t0, t1 -> Div t0, t1

  |Mod _, Int 1 | Mod Int 0, _ -> Int 0
  |Mod Int 1, _ -> Int 1
  |Mod Int x, Int y -> Int (x%y)
  |Mod t0, t1 -> Mod t0, t1

  |Shr t0, Int 0 -> t0
  |Shr Int x, Int y -> Int (x>>y)
  |Shr t0, t1 -> Shr t0, t1

  |Shl t0, Int 0 -> t0
  |Shl Int x, Int y -> Int (x<<y)
  |Shl t0, t1 -> Shl t0, t1

  |SHterm.Band args -> 
    let neutral_elem_one = List.filter (function SHterm.Int 1 -> false | _ -> true) args in
    SHterm.Band (List.map filter_identities neutral_elem_one)
  |SHterm.Bor args -> 
    let neutral_elem_zero = List.filter (function SHterm.Int 0 -> false | _ -> true) args in
    SHterm.Bor (List.map filter_identities neutral_elem_zero)
  | _ -> e 

let rec group_constants (e :Slsyntax.SHterm.t) : Slsyntax.SHterm.t = e 

let rec remove_mirror_terms (e :Slsyntax.SHterm.t) : Slsyntax.SHterm.t = e 

(* Remove same variables in both equation sides *)

(* Preprocess an Atom s.t. its terms are minimal, i.e. reducing and evaluating all possible exoresions *)
let rec preprocess_and_eval_atom (p : Slsyntax.SHpure.t) : Slsyntax.SHpure.t =
  (* Apply arithmetic, identities and same variable elimination on both sides, also #size >= 0  implicit (on post process avoid this ones) *)
  match p with
  | Atom (op, tt) ->
    let t0 = List.nth tt 0 in
    let t1 = List.nth tt 1 in
    let tt' = [filter_identities t0; filter_identities t1] in
    begin match op with 
    | Eq -> p
    | Neq -> p
    | Lt -> 
      begin match tt' with [Var (x, a); Add ([Int 1; Var (y, b)] | [Var (y, b); Int 1])] -> Atom (Le, [Var (x, a); Var (y, b)]) end (* Unit boundary simplification: x < y+1 -> x<=y *)
    | Le -> 
      begin match tt' with [Var (x, a); Sub ([Var (y, b); Int 1])] -> Atom (Lt, [Var (x, a); Var (y, b)]) end (* Unit boundary simplification: x <= y-1 -> x<y *)
    end
  | _ -> p

(* Normalize associativity for And and Or nodes *)
let rec normalize_associativity (p: SHpure.t) : SHpure.t =
  match p with
  | And clauses ->
      let flattened = 
        clauses
        |> List.map normalize_associativity  (* Recursively normalize clauses *)
        |> List.fold_left (fun acc clause ->
            match clause with
            | SHpure.And inner_clauses -> acc @ inner_clauses  (* Flatten nested AND *)
            | _ -> acc @ [clause]) []
      in
      And flattened
  | Or clauses ->
      let flattened = 
        clauses
        |> List.map normalize_associativity  (* Recursively normalize clauses *)
        |> List.fold_left (fun acc clause ->
            match clause with
            | SHpure.Or inner_clauses -> acc @ inner_clauses  (* Flatten nested OR *)
            | _ -> acc @ [clause]) []
      in
      Or flattened
  | Neg f -> Neg (normalize_associativity f)  (* Normalize within negation *)
  | Atom (_, _) -> preprocess_and_eval_atom p
  | _ -> p  (* True, False are already normalized *)


(* Convert arbitrary formula to DNF *)
let to_dnf (p: SHpure.t) : SHpure.t =
  p
  (*|> SHpure.unfold_indirect      (* Replace indirect references *)*)
  |> remove_implications         (* Remove implications and biconditionals *)
  |> push_negations              (* Push negations inward using dual *)
  |> distribute                  (* Apply distributive law for DNF *)
  |> normalize_associativity     (* Normalize associativity of And/Or *)
  (*|> SHpure.syntactical_simplL   (* Simplify resulting formula *)
  |> SHpure.extinguish_phantoms  (* Remove phantom variables *)*)

let process_conjunctions (p : SHpure.t) (_stats : bool) : SHpure.t =
  match p with
  | Atom (_, _) -> p
  | And conjunctions ->
      let g = WDGraph.create () in

      let start_time_build = Unix.gettimeofday () in
      let _ = WDGraph.add_conjunctions g conjunctions in 
      let end_time_build = Unix.gettimeofday () in
      let elapsed_time_build = end_time_build -. start_time_build in
      if _stats then
        Printf.printf "Execution time build graph: %f seconds\n" elapsed_time_build;
      
      let start_time_simplify = Unix.gettimeofday () in
      let _ = WDGraph.simplify g in 
      let end_time_simplify = Unix.gettimeofday () in
      let elapsed_time_simplify = end_time_simplify -. start_time_simplify in
      if _stats then
        Printf.printf "Execution time simplify graph: %f seconds\n" elapsed_time_simplify;

      let start_time_rebuild = Unix.gettimeofday () in
      let simplified_conjunctions = WDGraph.get_conjunctions g in 
      let end_time_rebuild = Unix.gettimeofday () in
      let elapsed_time_rebuild = end_time_rebuild -. start_time_rebuild in
      if _stats then
        Printf.printf "Execution time re-build graph: %f seconds\n" elapsed_time_rebuild;

      begin match simplified_conjunctions with
      | [False] -> False
      | _ -> And simplified_conjunctions
      end
  | _ -> failwith "ERROR: Unexpected formula structure during process_conjunctions. Expected: And"

(* Currently just filtering falses *)
let rec process_disjunction (p : SHpure.t list) : SHpure.t list = 
  List.filter(fun p' -> p' <> SHpure.False) p

(* Currently do nothing *)
let simplify_pure (p : SHpure.t) (_stats : bool) : SHpure.t =
  let start_time_dnf = Unix.gettimeofday () in
  let dnf_p = to_dnf p in
  let end_time_dnf = Unix.gettimeofday () in
  let elapsed_time_dnf = end_time_dnf -. start_time_dnf in
  if _stats then
    Printf.printf "Execution time DNF conversion: %f seconds\n" elapsed_time_dnf;
  match dnf_p with
  | Or clauses -> Or (process_disjunction(List.map (fun clause -> process_conjunctions clause _stats) clauses))
  | And _ -> process_conjunctions dnf_p _stats
  | _ -> dnf_p 
  
;;
