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
  | Neg (True) -> False
  | Neg (False) -> True
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

let rec filter_identities_and_eval (e : Slsyntax.SHterm.t) : Slsyntax.SHterm.t =
  match e with
  |Add [t0; Int 0] -> t0
  |Add [Int 0; t1] -> t1
  |Add [Int x; Int y] -> Int (x+y)

  |Sub [t0; Int 0] -> t0
  (*|Sub Int 0, t1 -> t1  special case if the variable is the one substracting *)
  |Sub [Int x; Int y] -> Int (x-y)
  
  |Mul (t0, Int 1) -> t0
  |Mul (Int 1, t1) -> t1
  |Mul (Int x, Int y) -> Int (x*y)

  |Div (t0, Int 1) -> t0
  |Div (Int x, Int y) -> Int (x/y)

  |Mod (_, Int 1) | Mod (Int 0, _) -> Int 0
  |Mod (Int 1, _) -> Int 1
  |Mod (Int x, Int y) -> Int (x mod y)

  |Shr (t0, Int 0) -> t0
  |Shr (Int x, Int y) -> Int (x lsr y)

  |Shl (t0, Int 0) -> t0
  |Shl (Int x, Int y) -> Int (x lsl y)

  |Band (t0, Int 1) -> t0
  |Band (Int 1, t1) -> t1
  |Band (Int x, Int y) -> Int (x land y)

  |Bor (t0, Int 1) -> t0
  |Bor (Int 1, t1) -> t1
  |Bor (Int x, Int y) -> Int (x lor y)

  |Bxor (t0, Int 1) -> t0
  |Bxor (Int 1, t1) -> t1
  |Bxor (Int x, Int y) -> Int (x lxor y)

  | _ -> e 

let rec group_constants (e :Slsyntax.SHterm.t) : Slsyntax.SHterm.t = e 

let rec remove_mirror_terms (e :Slsyntax.SHpure.t) : Slsyntax.SHpure.t =
  let toList t =
    match t with
    | T.Add tt -> tt
    | _ -> [t]
  in
  let fromList tt =
    match tt with
    | [] -> T.Int 0
    | [t] -> t
    | _ -> T.Add tt
  in
  let rec aux tt uu =
    match tt,uu with
    | t0::tt0,u0::uu0 when t0 = u0 -> aux tt0 uu0
    | _,_ -> (fromList tt,fromList uu)
  in
  match e with
  |Atom(Le, [t;u]) -> let tt, uu = aux (toList t) (toList u) in Atom(Le, [filter_identities_and_eval tt; filter_identities_and_eval uu])
  |Atom(Lt, [t;u]) -> let tt, uu = aux (toList t) (toList u) in Atom(Lt, [filter_identities_and_eval tt; filter_identities_and_eval uu])
  |Atom(Eq, [t;u]) -> let tt, uu = aux (toList t) (toList u) in Atom(Eq, [filter_identities_and_eval tt; filter_identities_and_eval uu])
  |Atom(Neq, [t;u]) -> let tt, uu = aux (toList t) (toList u) in Atom(Neq, [filter_identities_and_eval tt; filter_identities_and_eval uu])

(* Remove same variables in both equation sides *)

(* Preprocess an Atom s.t. its terms are minimal, i.e. reducing and evaluating all possible exoresions *)
let rec preprocess_and_eval_atom (p : Slsyntax.SHpure.t) : Slsyntax.SHpure.t =
  (* Apply arithmetic, identities and same variable elimination on both sides, also #size >= 0  implicit (on post process avoid this ones) *)
  match p with
  | Atom (op, [t0;t1]) ->
    let tt' = [filter_identities_and_eval t0; filter_identities_and_eval t1] in
    begin match op with 
    | Lt -> 
      begin match tt' with |[a; Add ([Int 1; b] | [b; Int 1])] -> remove_mirror_terms (Atom (Le, [a;b])) |_ -> remove_mirror_terms p  end (* Unit boundary simplification: x < y+1 -> x<=y *)
    | Le -> 
      begin match tt' with |[a; Sub ([b; Int 1])] -> remove_mirror_terms (Atom (Lt, [a; b])) |_ -> remove_mirror_terms p end (* Unit boundary simplification: x <= y-1 -> x<y *)
    |_ -> p
    end
  | _ -> remove_mirror_terms p

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
  |> normalize_associativity    (* Normalize associativity of And/Or *)
  (*|> SHpure.syntactical_simplL   (* Simplify resulting formula *)
  |> SHpure.extinguish_phantoms  (* Remove phantom variables *)*)

let process_conjunctions (p : SHpure.t) (_stats : bool) (_postprocess: bool) : SHpure.t =
  match p with
  | Atom (_, _) -> p
  | And conjunctions ->
      let g = WDGraph.create () in

      (*let start_time_build = Unix.gettimeofday () in*)
      let _ = WDGraph.add_conjunctions g conjunctions in 
      (*let end_time_build = Unix.gettimeofday () in
      let elapsed_time_build = end_time_build -. start_time_build in
      if _stats then
        Printf.printf "Execution time build graph: %f seconds\n" elapsed_time_build;*)
      
      (*let start_time_simplify = Unix.gettimeofday () in*)
      let _ = WDGraph.simplify g in 
      (*let end_time_simplify = Unix.gettimeofday () in
      let elapsed_time_simplify = end_time_simplify -. start_time_simplify in
      if _stats then
        Printf.printf "Execution time simplify graph: %f seconds\n" elapsed_time_simplify;*)

      (*let start_time_rebuild = Unix.gettimeofday () in*)
      let simplified_conjunctions = if _postprocess then WDGraph.get_conjunctions_eval_atom g else WDGraph.get_conjunctions g in 
      (*let end_time_rebuild = Unix.gettimeofday () in
      let elapsed_time_rebuild = end_time_rebuild -. start_time_rebuild in
      if _stats then
        Printf.printf "Execution time re-build graph: %f seconds\n" elapsed_time_rebuild;*)

      begin match simplified_conjunctions with
      | [False] -> False
      | _ -> And simplified_conjunctions
      end
  | _ -> failwith "ERROR: Unexpected formula structure during process_conjunctions. Expected: And"

(* Currently just filtering falses *)
let rec process_disjunction (p : SHpure.t list) : SHpure.t list = 
  List.filter(fun p' -> p' <> SHpure.False) p

let rec dnf_atom_size (p: SHpure.t) : int = 
  match p with 
  | False | True | Atom(_) -> 1
  | And pp -> List.length pp
  | Or pp -> pp |> List.map(fun e -> dnf_atom_size e) |> List.fold_left(fun e acc -> e + acc) 0
(* Currently do nothing *)
let simplify_pure (p : SHpure.t) (_stats : bool) (_preprocess: bool) (_postprocess: bool) : SHpure.t =
  let start_time_dnf = Unix.gettimeofday () in
  let dnf_p = to_dnf p in
  let end_time_dnf = Unix.gettimeofday () in
  let elapsed_time_dnf = end_time_dnf -. start_time_dnf in
  if _stats then 
    Printf.printf "Execution time DNF conversion: %f seconds\n" elapsed_time_dnf;
  match dnf_p with
  | Or clauses -> 
    let start_time_simplify = Unix.gettimeofday () in
    let red_dnf_p = SHpure.Or (process_disjunction(List.map (fun clause -> process_conjunctions clause _stats _postprocess) clauses)) in
    let end_time_simplify = Unix.gettimeofday () in
    let elapsed_time_simplify = end_time_simplify -. start_time_simplify in
    if _stats then 
      Printf.printf "Execution time reduction: %f seconds\n" elapsed_time_simplify;
      Printf.printf "Size of DNF formulae (atoms): %d\n" (dnf_atom_size dnf_p);
      Printf.printf "Size of reduced formulae (atoms): %d\n" (dnf_atom_size red_dnf_p);
    red_dnf_p
  | And _ -> 
    let start_time_simplify = Unix.gettimeofday () in
    let red_dnf_p = process_conjunctions dnf_p _stats _postprocess in 
    let end_time_simplify = Unix.gettimeofday () in
    let elapsed_time_simplify = end_time_simplify -. start_time_simplify in
    if _stats then 
      Printf.printf "Execution time reduction: %f seconds\n" elapsed_time_simplify;
      Printf.printf "Size of DNF formulae (atoms): %d\n" (dnf_atom_size dnf_p);
      Printf.printf "Size of reduced formulae (atoms): %d\n" (dnf_atom_size red_dnf_p);
    red_dnf_p
  | _ -> 
    let eval_atom a = 
      match a with
      |SHpure.Atom(Le, [Int x; Int y]) -> if x <= y then SHpure.True else SHpure.False
      |SHpure.Atom(Lt, [Int x; Int y]) -> if x < y then SHpure.True else SHpure.False
      |SHpure.Atom(Neq, [Int x; Int y]) -> if x != y then SHpure.True else SHpure.False
      |SHpure.Atom(Eq, [Int x; Int y]) -> if x == y then SHpure.True else SHpure.False
      |_ -> a
    in
    eval_atom dnf_p 
  
;;
