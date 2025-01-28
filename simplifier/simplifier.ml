(*
  Simplifier of Symbolic Heaps
*)
open Slsyntax

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
  | _ -> p  (* Atoms, True, False are already normalized *)


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
 

(* Currently do nothing *)
let simplify_pure (p: SHpure.t) : SHpure.t = to_dnf p


  
;;
