open Graph
open Slsyntax
open Str

module NodeSet = Set.Make(struct
  type t = SHterm.t
  let compare = SHterm.compare
end)

type edge_label = 
  | Red of bool (* Boolean value used to indicate hidden relation i.e. if true then the atom is not shown in the final formula as it was not in original input *)
  | Blue of bool (* Boolean value used to indicate hidden relation i.e. if true then the atom is not shown in the final formula as it was not in original input *)
  | Yellow
  | Orange
  | Green of string (* String value used to store the fieldterm *)

(* Define the graph module using OCamlgraph's Persistent.Digraph.ConcreteLabeled functor *)
module WDGraph = struct
  (* Define a custom graph with integer nodes and edges labeled with weights *)
  module G = Persistent.Digraph.ConcreteLabeled(struct
    type t = Slsyntax.SHterm.t  (*Using terms as nodes*)
    let compare = SHterm.compare
    let hash = Hashtbl.hash
    let equal = (=)
  end)(struct
    type t = edge_label
    let compare x y = 
      match (x, y) with
      | Red _, _ -> -1
      | _, Red _-> 1
      | Blue _, _ -> -1
      | _, Blue _ -> 1
      | Yellow, _ -> -1
      | _, Yellow -> 1
      | Orange, _ -> -1
      | _, Orange -> 1
      | Green s1, Green s2 -> String.compare s1 s2
      | _, _ -> 0
    let default = Red false
  end)

  (* Define a record type for the graph structure *)
  type t = {
    mutable graph : G.t; (* The OCamlgraph graph *)
    mutable red_edges : (SHterm.t * SHterm.t) list; (* List of edges with weight 0 *)
    mutable eq_representative_pairs : (SHterm.t * SHterm.t) list; (* List of pairs node*representative *)
    mutable unsat : bool; (* Indicates if the graph has become unsat or not *)
    mutable black_edges : (SHterm.t * SHterm.t, unit)  Hashtbl.t; (* Hashtable to update and keep track of inequalities - black edges *)
    mutable n_scc : int; (* Number of SCCs present in the graph *)
    mutable f_scc: (G.V.t -> int) option; (* Membership function, node -> SCC id *)
    mutable r_scc: (int -> G.V.t) option; (* Representative function, SCC id -> representant node *)
    mutable quotient_graph : G.t; (* The OCamlgraphquotient graph *)
  }

  (* Initialize an empty graph structure *)
  let create () : t = {
    graph = G.empty;
    red_edges = [];
    eq_representative_pairs = [];
    unsat = false;
    black_edges = Hashtbl.create 32;
    n_scc = -1;
    f_scc = None;
    r_scc = None;
    quotient_graph = G.empty;
  }

  (* Orders a pair of nodes depending of `SHterm.compare` *)
  let normalize_term_pair (u : SHterm.t) (v : SHterm.t) : SHterm.t * SHterm.t  =
    if SHterm.compare u v <= 0 then (u, v) else (v, u)

  (* Add an edge to the graph *)
  let add_edge (g : t) (u : SHterm.t) (v : SHterm.t) (w : edge_label) : unit =
    if not (g.unsat) then
      (* Make sure nodes exist *)
      let g' = G.add_vertex (G.add_vertex g.graph u) v in
      let black_pair = normalize_term_pair u v in
        (* Check if there is an existing black edge between u and v *)
        try
          let _ = Hashtbl.find g.black_edges black_pair in
          let g' = G.add_edge_e g' (u, Red false, v) in
          g.graph <- g';
          g.red_edges <- (u, v) :: g.red_edges;
          Hashtbl.remove g.black_edges black_pair
        with Not_found ->
          try
            let edge = G.find_edge g' u v in
            match edge with
            | (_,w',_) ->
              if w <> w' then
                (* Update the weight to 0 if the weights differ *)
                let g' = G.remove_edge_e g' (u, w', v) in
                let g' = G.add_edge_e g' (u, Red false, v) in
                g.graph <- g';
                g.red_edges <- (u, v) :: g.red_edges;
          with Not_found ->
            (* If no edge exists, simply add it *)
            let g' = G.add_edge_e g' (u, w, v) in
            g.graph <- g';
            if w = Red false then g.red_edges <- (u, v) :: g.red_edges

  (* Add an edge to the quotient graph *)
  let add_quotient_edge (g : t) (u : SHterm.t) (v : SHterm.t) (w : edge_label) : unit =
    if not (g.unsat) then
      try
        let edge = G.find_edge g.quotient_graph u v in
        match edge with
        | (_,w',_) ->
          if w <> w' then
            (* Update the weight to 0 if the weights differ *)
            let g' = G.remove_edge_e g.quotient_graph (u, w', v) in
            let g' = G.add_edge_e g' (u, Red false, v) in
            g.quotient_graph <- g'
        | _ -> let g' = G.add_edge_e g.quotient_graph (u, w, v) in
          g.quotient_graph <- g'
      with Not_found -> 
        let g' = G.add_edge_e g.quotient_graph (u, w, v) in
        g.quotient_graph <- g'

  (* Check if any of the red edges forms a cycle. Red contradiction *)
  let forms_cycle_with_red (g : t) : bool =
    let module Path = Path.Check(G) in
    let pc = Path.create(g.graph) in 
    List.exists (fun (u, v) -> Path.check_path pc v u) g.red_edges

  (* Postprocess an Atom s.t. its terms are minimal *) (* #TODO: filter identities like we do in `filter_identities_and_eval` at `simplifier.ml` *)
  let rec postprocess_and_eval_terms (g : t) (a : Slsyntax.SHterm.t) : Slsyntax.SHterm.t =
    (* on complex epesion try to recursively match terms into representative method until u find one and stop *)
    let r_scc = match g.r_scc with | Some f -> f | _ -> failwith "r_scc not computed before `postprocess_and_eval_terms`" in
    let f_scc = match g.f_scc with  | Some f -> f | _ -> failwith "f_scc not computed before `postprocess_and_eval_terms`" in
    match a with 
    | Var _ -> a
    | Int _ -> a
    | PosInf -> a
    | NegInf -> a
    | Add tt -> let tt' = List.map(fun t -> try r_scc (f_scc t) with Not_found -> postprocess_and_eval_terms g t)tt in begin match tt' with |[Int a; Int b] -> Int (a+b) |_ -> Add(tt') end 
    | Sub tt -> let tt' = List.map(fun t -> try r_scc (f_scc t) with Not_found -> postprocess_and_eval_terms g t)tt in begin match tt' with |[Int a; Int b] -> Int (a-b) |_ -> Sub(tt') end 
    | Mul (t0, t1) -> let tt = List.map(fun t -> try r_scc (f_scc t) with Not_found -> postprocess_and_eval_terms g t)[t0;t1] in begin match tt with |[Int a; Int b] -> Int (a*b) |_ -> Mul(List.nth tt 0, List.nth tt 1) end (* If two ints then eval, else return atom *)
    | Div (t0, t1) -> let tt = List.map(fun t -> try r_scc (f_scc t) with Not_found -> postprocess_and_eval_terms g t)[t0;t1] in begin match tt with |[Int a; Int b] -> Int (a/b) |_ -> Div(List.nth tt 0, List.nth tt 1) end 
    | Mod (t0, t1) -> let tt = List.map(fun t -> try r_scc (f_scc t) with Not_found -> postprocess_and_eval_terms g t)[t0;t1] in begin match tt with |[Int a; Int b] -> Int (a mod b) |_ -> Mod(List.nth tt 0, List.nth tt 1) end
    | Shr (t0, t1) -> let tt = List.map(fun t -> try r_scc (f_scc t) with Not_found -> postprocess_and_eval_terms g t)[t0;t1] in begin match tt with |[Int a; Int b] -> Int (a lsr b) |_ -> Shr(List.nth tt 0, List.nth tt 1) end
    | Shl (t0, t1) -> let tt = List.map(fun t -> try r_scc (f_scc t) with Not_found -> postprocess_and_eval_terms g t)[t0;t1] in begin match tt with |[Int a; Int b] -> Int (a lsl b) |_ -> Shl(List.nth tt 0, List.nth tt 1) end
    | Band (t0, t1) -> let tt = List.map(fun t -> try r_scc (f_scc t) with Not_found -> postprocess_and_eval_terms g t)[t0;t1] in begin match tt with |[Int a; Int b] -> Int (a land b) |_ -> Band(List.nth tt 0, List.nth tt 1) end
    | Bor (t0, t1) -> let tt = List.map(fun t -> try r_scc (f_scc t) with Not_found -> postprocess_and_eval_terms g t)[t0;t1] in begin match tt with |[Int a; Int b] -> Int (a lor b) |_ -> Bor(List.nth tt 0, List.nth tt 1) end
    | Bxor (t0, t1) -> let tt = List.map(fun t -> try r_scc (f_scc t) with Not_found -> postprocess_and_eval_terms g t)[t0;t1] in begin match tt with |[Int a; Int b] -> Int (a lxor b) |_ -> Bxor(List.nth tt 0, List.nth tt 1) end
    | Bnot t -> begin try Bnot (r_scc (f_scc t)) with Not_found -> Bnot (postprocess_and_eval_terms g t) end
    | Fcall (f, ts) -> begin Fcall (f, (List.map(fun t -> try r_scc (f_scc t) with Not_found -> postprocess_and_eval_terms g t) ts)) end
    (* eval them and reduce integers *)
  
  (* Given a list of Atoms (conjunction of them) extract the terms and type of edge and add it to the graph *)
  let add_conjunctions (g : t) (atoms : SHpure.t list): unit = 
      List.iter (fun a ->
        if not (g.unsat) then
          match a with
          | SHpure.False -> g.unsat <- true;
          | SHpure.True -> ()
          | SHpure.Atom (op, tt) ->
            let a' =  a in
            match a' with
            | SHpure.Atom (op, tt) ->
              let t0 = List.nth tt 0 in
              let t1 = List.nth tt 1 in
                match op with
                | Eq -> 
                    add_edge g t0 t1 (Blue false);
                    add_edge g t1 t0 (Blue false);
                | Neq -> if t0 = t1 then g.unsat <- true else (  (* Black contradiction: `x != x` *)
                  g.graph <- G.add_vertex (G.add_vertex g.graph t0) t1;
                  Hashtbl.replace g.black_edges (normalize_term_pair t0 t1) ();
                  )
                | Le -> add_edge g t0 t1 (Blue false);
                | Lt -> add_edge g t0 t1 (Red false);
        ) atoms

  (* Simplify the graph, i.e. post-analyssis of diferent properties *)
  let simplify (g : t) : unit = 
    if not (g.unsat) then
      (* Check red contradiction *)
      if forms_cycle_with_red g then g.unsat <- true
      (* Compute SCCs *)
      else
        (* Call scc method*)
        let module SCC = Components.Make(G) in
        let n_scc, f_scc = SCC.scc(g.graph) in
        g.n_scc <- n_scc;
        g.f_scc <- Some f_scc;
        let black_pairs_in_same_scc = Hashtbl.fold (fun (u, v) _ acc -> acc || try (f_scc u == f_scc v) with Not_found -> false) g.black_edges false in
        if black_pairs_in_same_scc then g.unsat <- true (* Black contradiction 2: Inside an SCC there exists 2 nodes that are equivalent and diferent at the same time: `x = y and y != x` *)
        else 
            (* Compute representatives for SCCs *)
            let scc_nodes = Hashtbl.create n_scc in
            G.iter_vertex (fun v -> Hashtbl.add scc_nodes (f_scc v) v) g.graph;
            let representatives = Array.make n_scc (SHterm.Int 0) (* Placeholder initial value *) in
            for i = 0 to n_scc - 1 do
              let nodes = Hashtbl.find_all scc_nodes i in
              let int_terms = List.filter (function SHterm.Int _ -> true | SHterm.Sub [Int _; Int _] -> true | _ -> false) nodes in  (* SHterm.Sub [Int a; Int b] refers to negative numbers that are stored as 0-n *)
              let chosen_rep = 
                begin match int_terms with
                | [a] -> Array.set representatives i a; a (* Exactly one Int term *)
                | _ when List.length int_terms > 1 ->  (* Check blue contradiction / more than one int term within a SCC *)
                    g.unsat <- true; List.hd int_terms
                | _ -> 
                    let var_nodes = List.filter (function SHterm.Var _ -> true | _ -> false) nodes in
                    let chosen = 
                      if var_nodes <> [] then List.hd var_nodes 
                      else List.hd nodes 
                    in
                    Array.set representatives i chosen;
                    chosen
                end
              in
              List.iter(fun u -> 
                if u <> chosen_rep then 
                  g.eq_representative_pairs <- (u, chosen_rep) :: g.eq_representative_pairs
                ) nodes
            done;

            let r_scc = (fun (id : int) ->  Array.get representatives id) in
            g.r_scc <- Some r_scc;
            (* Build quotient graph / reduce graph *)
            Array.iter(fun rep -> 
              let g' = G.add_vertex g.quotient_graph rep in 
              g.quotient_graph <- g') representatives;
            G.iter_edges_e (fun (u, w, v) ->
               let r_u = r_scc (f_scc u) in
               let r_v = r_scc (f_scc v) in
               if r_u <> r_v then  (* avoid redundant edges within the same SCC *)
                add_quotient_edge g r_u r_v w) 
            g.graph;
            (* clean expresions in nodes *)
            g.quotient_graph <- G.map_vertex(fun u -> postprocess_and_eval_terms g u) g.quotient_graph

  (* Given a graph extract the terms and type of relation from edge and return a new conjunction list with its terms and atoms evaluated if possible *)
  let get_conjunctions_eval_atom (g : t) : SHpure.t * SHspat.t = 
    let eval_atom a =  (* Evaluate atoms if all information is known *)
      match a with
      |SHpure.Atom(Le, [Int x; Int y]) -> if x <= y then SHpure.True else SHpure.False
      |SHpure.Atom(Lt, [Int x; Int y]) -> if x < y then SHpure.True else SHpure.False
      |SHpure.Atom(Neq, [Int x; Int y]) -> if x != y then SHpure.True else SHpure.False
      |SHpure.Atom(Eq, [Int x; Int y]) -> if x == y then SHpure.True else SHpure.False
      |_ -> a
    in 
    if g.unsat then 
      (False, [])
    else (
      let rb_atoms = ref [] in (* Red / Blue edges (Pure) *)
      let yo_atoms = ref [] in (* Yellow / Orange edges (Spatial *)
      let g_edges_info = Hashtbl.create 32 in (* Green edges (Spatial) *)
      let unique_key_nodes = ref NodeSet.empty in (* To avoid repeating pointer atoms for each field, this happens due to limitation in internal implementation of hash tables iterators (can't iterate over keys but just associations) *)
      G.iter_edges_e (fun (u, w, v) -> 
        match w with  (* Rebuild atoms or expresions from edges *)
        | Red hidden when hidden = false -> rb_atoms := eval_atom(SHpure.Atom(Lt, [u; v])) :: !rb_atoms
        | Blue hidden when hidden = false -> rb_atoms := eval_atom(SHpure.Atom(Le, [u; v])) :: !rb_atoms
        | Yellow -> yo_atoms := SHspatExp.Arr(u,v) :: !yo_atoms
        | Orange -> yo_atoms := SHspatExp.Str(u,v) :: !yo_atoms
        | Green f -> Hashtbl.add g_edges_info u (f, v); unique_key_nodes := NodeSet.add u !unique_key_nodes 
        | _ -> failwith "ERROR rebuilding graph, edge label (color) not suported"
      ) g.quotient_graph;
      let black_atoms = Hashtbl.fold (fun (u, v) _ acc -> eval_atom(SHpure.Atom(Neq, [u; v])) :: acc ) g.black_edges [] in (* Rebuilding inequality edges *)
      (* Rebuilding equality information *) 
      let eq_atoms = List.map(fun (u, v) -> eval_atom(SHpure.Atom(Eq, [u; v]))) g.eq_representative_pairs in (*redundant information as the equalities are treated by representatives, adding it just for readability in final formula *)
      let pure_atoms = eq_atoms @ !rb_atoms @ black_atoms in 
      let g_atoms = ref [] in (* Need some extra processing to rebuild the fieldterm_seq of the pointers*)
      NodeSet.iter (fun key ->
          let values = Hashtbl.find_all g_edges_info key in
          match values with
          | [("", b)] when key = b -> g_atoms := SHspatExp.Pto(key, []) :: !g_atoms
          | _ -> g_atoms := SHspatExp.Pto(key, values) :: !g_atoms
      ) !unique_key_nodes; (* Format in [({key} SHPure.Atom, [{value}(field, SHPure.Atom)]) *)
      let spat_atoms = !g_atoms @ !yo_atoms in
      (* DO a final simplification looking for false atoms in SHPure and filtering true atoms *)
      if List.exists(fun e -> e == SHpure.False) pure_atoms then (False, []) 
      else (SHpure.And (List.filter(fun e -> e != SHpure.True) pure_atoms), spat_atoms)
    )

    let get_partial_conjunctions_eval_atom (g : t) : SHpure.t list = 
      let eval_atom a =  (* Evaluate atoms if all information is known *)
        match a with
        |SHpure.Atom(Le, [Int x; Int y]) -> if x <= y then SHpure.True else SHpure.False
        |SHpure.Atom(Lt, [Int x; Int y]) -> if x < y then SHpure.True else SHpure.False
        |SHpure.Atom(Neq, [Int x; Int y]) -> if x != y then SHpure.True else SHpure.False
        |SHpure.Atom(Eq, [Int x; Int y]) -> if x == y then SHpure.True else SHpure.False
        |_ -> a
      in 
      if g.unsat then 
        [False]
      else (
        let rb_atoms = ref [] in (* Red / Blue edges (Pure) *)
        G.iter_edges_e (fun (u, w, v) -> 
          match w with  (* Rebuild atoms or expresions from edges *)
          | Red hidden when hidden = false -> rb_atoms := eval_atom(SHpure.Atom(Lt, [u; v])) :: !rb_atoms
          | Blue hidden when hidden = false -> rb_atoms := eval_atom(SHpure.Atom(Le, [u; v])) :: !rb_atoms
          | Yellow -> ()
          | Orange -> ()
          | Green _ -> ()
          | _ -> failwith "ERROR rebuilding graph, edge label (color) not suported"
        ) g.quotient_graph;
        let black_atoms = Hashtbl.fold (fun (u, v) _ acc -> eval_atom(SHpure.Atom(Neq, [u; v])) :: acc ) g.black_edges [] in (* Rebuilding inequality edges *)
        (* Rebuilding equality information *) 
        let eq_atoms = List.map(fun (u, v) -> eval_atom(SHpure.Atom(Eq, [u; v]))) g.eq_representative_pairs in (*redundant information as the equalities are treated by representatives, adding it just for readability in final formula *)
        let pure_atoms = eq_atoms @ !rb_atoms @ black_atoms in 
        
        if List.exists(fun e -> e == SHpure.False) pure_atoms then [False]
        else 
          let filtered_true_atoms = List.filter(fun e -> e != SHpure.True) pure_atoms in
          if filtered_true_atoms = [] then [True] else filtered_true_atoms
      )

  (* Add pointer edges in the quotient graph and evaluates any inconsistency *)
  let add_ptr (g : t) (ptr_spat : (SHterm.t * (string * SHterm.t) list) list) : unit =
    let check_no_green_edges_before r_a =  (* returns true if any green edge present i.e. the node is already pointing to some other node/s *)
      try
        let edges = G.succ_e g.quotient_graph r_a in
        let green_edges = List.filter (fun (_, w, _) -> match w with Green _ -> true | _ -> false) edges in
        List.length green_edges > 0
      with Invalid_argument _ -> false in (* If node not found in the quotioent graph *)
    if not (g.unsat) then (
    let r_scc = match g.r_scc with | Some r_scc -> r_scc | _ -> failwith "SCCs not computed before checking spatial pointers" in
    let f_scc = match g.f_scc with | Some f_scc -> f_scc | _ -> failwith "SCCs not computed before checking spatial pointers" in
    List.iter(fun (a,bs) -> if not (g.unsat) then (
      let r_a = try r_scc (f_scc a) with | Not_found -> a in
      match r_a with 
      | Int i when i <= 0 -> g.unsat <- true
      | Sub [Int x; Int y] when x-y <=0 -> g.unsat <- true (* Check for negative address *)
      | _ -> (* Add edge and check for consistency *)
        if check_no_green_edges_before r_a then g.unsat <- true else match bs with
          | [] -> (* adding self pointing green edge. Case: x -> () *)
            let g' = G.add_edge_e g.quotient_graph (r_a, Green "", r_a) in 
            g.quotient_graph <- g'
          | _ -> (* Fieldterm_seq case, adding edges to every node in the seq. Case: x -> (f0:t0,f1:t1, ...) *)
            List.iter(fun (f, b) -> 
                let r_b = try r_scc (f_scc b) with | Not_found -> b in
                let g' = G.add_edge_e g.quotient_graph (r_a, Green f, r_b) in 
                g.quotient_graph <- g';
              ) bs
      )) ptr_spat
    )
  
  (* Add memory edges (array+string) in the quotient graph and evaluates any inconsistency *)
  let add_mem_spat (g : t) (arr_spat : (SHterm.t * SHterm.t) list) (str_spat : (SHterm.t * SHterm.t) list) (ptr_spat : (SHterm.t * (string * SHterm.t) list) list) :  unit = 
    if not (g.unsat) then
      let r_scc = match g.r_scc with | Some r_scc -> r_scc | _ -> failwith "SCCs not computed before checking array and string pointers" in
      let f_scc = match g.f_scc with | Some f_scc -> f_scc | _ -> failwith "SCCs not computed before checking array and string pointers" in
      let mem_spat = arr_spat @ str_spat in
      (* Add array edges checking for negative addresses *)
      List.iter(fun (a,b) -> if not (g.unsat) then (
        let r_a = try r_scc (f_scc a) with | Not_found -> a in
        let r_b = try r_scc (f_scc b) with | Not_found -> b in
        match r_a with 
        | Int i when i <= 0 -> g.unsat <- true
        | Sub [Int x; Int y] when x-y <=0 -> g.unsat <- true (* Check for negative address in a *)
        | _ -> match r_b with
          | Int i when i <= 0 -> g.unsat <- true
          | Sub [Int x; Int y] when x-y <=0 -> g.unsat <- true (* Check for negative address in b *)
          | _ -> (* Add edge *)
            let g' = G.add_edge_e g.quotient_graph (r_a, Yellow, r_b) in 
            g.quotient_graph <- g'
        )) arr_spat;
    if not (g.unsat) then
      (* Add string edges checking for negative addresses *)
      List.iter(fun (a,b) -> if not (g.unsat) then (
        let r_a = try r_scc (f_scc a) with | Not_found -> a in
        let r_b = try r_scc (f_scc b) with | Not_found -> b in
        match r_a with 
        | Int i when i <= 0 -> g.unsat <- true
        | Sub [Int x; Int y] when x-y <=0 -> g.unsat <- true (* Check for negative address in a *)
        | _ -> match r_b with
          | Int i when i <= 0 -> g.unsat <- true
          | Sub [Int x; Int y] when x-y <=0 -> g.unsat <- true (* Check for negative address in b *)
          | _ -> (* Add edge *)
            let g' = G.add_edge_e g.quotient_graph (r_a, Orange, r_b) in 
            g.quotient_graph <- g'
      )) str_spat;
    (* Check for no cycles for all pairs array+string. Avoiding "back edges", after quotient graph creation a DAG is generated, if adding any new edge generates a cycle
      we got that we are trying to allocate memmory giving inverted address i.e. Arr(a,b) but b < a and should be  Arr(b,a) this is evaluated as False, not Emp *)
    if not (g.unsat) then ( 
      let module Path = Path.Check(G) in
      let pc = Path.create(g.quotient_graph) in 
      List.iter(fun (a,b) -> if not (g.unsat) then (
        let r_a = try r_scc (f_scc a) with | Not_found -> a in
        let r_b = try r_scc (f_scc b) with | Not_found -> b in
        if r_b != r_a && Path.check_path pc r_b r_a then g.unsat <- true) (* The case Arr(x,x) is valid *)
      ) mem_spat
    );
    (* Main algorithm to check overlaps in memory. Checks for common nodes contained in each segment of memory *)
    if not (g.unsat) then (
      let nodes_in_all_paths a b =
        let r_a = try r_scc (f_scc a) with | Not_found -> a in
        let r_b = try r_scc (f_scc b) with | Not_found -> b in
        (* Compute nodes reachable from A, forward reachability *)
        let forward_reachable_nodes = G.fold_succ (fun x acc -> NodeSet.add x acc) g.quotient_graph r_a (NodeSet.add r_a NodeSet.empty) in
        (* Compute nodes that can reach B, backward reachability *)
        let backward_reachable_nodes = G.fold_pred (fun x acc -> NodeSet.add x acc) g.quotient_graph r_b (NodeSet.add r_b NodeSet.empty) in
        
        (* Intersection of forward and backward reachable nodes, this implementation is efficient with sparse graphs*) 
        (* for more dense graphs a reachability precomputation and store the information beforehand might outperform the current implementation *)
        NodeSet.inter forward_reachable_nodes backward_reachable_nodes 
      in
      let used_memory = ref NodeSet.empty in
      List.iter(fun (a,_) -> try used_memory := NodeSet.add (r_scc (f_scc a)) !used_memory with | Not_found -> used_memory := NodeSet.add a !used_memory) ptr_spat;
      let segment_intervals = List.map (fun (a, b) -> nodes_in_all_paths a b) mem_spat in
      List.iter(fun pi -> if not (g.unsat) then
        if not (g.unsat) && NodeSet.inter !used_memory pi != NodeSet.empty then g.unsat <- true else used_memory := NodeSet.union !used_memory pi
      )segment_intervals
    )
end

module DotSerializer = struct
  
  (* Helper function to escape special characters in node labels *)
  let escape_label s =
    let s = String.escaped s in
    (* Additional escaping for Graphviz *)
    Str.global_replace (Str.regexp "\"") "\\\"" s
  
  let _serialize graph =
    let buf = Buffer.create 1024 in
    Buffer.add_string buf "digraph G {\n";
    Buffer.add_string buf "  node [shape=box, style=rounded];\n";
    
    (* Add all vertices *)
    WDGraph.G.iter_vertex (fun v ->
      let label = escape_label (SHterm.to_string v) in
      Buffer.add_string buf (Printf.sprintf "  \"%s\" [label=\"%s\"];\n" label label)
    ) graph;
    
    (* Add all edges *)
    WDGraph.G.iter_edges_e (fun (v1, lbl, v2) ->
      let src = escape_label (SHterm.to_string v1) in
      let dst = escape_label (SHterm.to_string v2) in
      let edge_attrs = match lbl with
        | Red _ -> " [color=red, penwidth=2.0]"
        | Blue _ -> " [color=blue, penwidth=2.0]"
        | Yellow -> " [color=yellow, penwidth=2.0]"
        | Orange -> " [color=orange, penwidth=2.0]"
        | Green s -> Printf.sprintf " [color=green, label=\"%s\", penwidth=2.0]" s
      in
      Buffer.add_string buf (Printf.sprintf "  \"%s\" -> \"%s\"%s;\n" src dst edge_attrs)
    ) graph;
    
    Buffer.add_string buf "}\n";
    Buffer.contents buf
  
  let serialize_graph (wdg : WDGraph.t) : string = _serialize wdg.graph
  let serialize_quotient_graph (wdg : WDGraph.t) : string = _serialize wdg.quotient_graph
end

module TextPrinter = struct
  let edge_label_to_string = function
    | Red _ -> "Red"
    | Blue _ -> "Blue"
    | Yellow -> "Yellow"
    | Orange -> "Orange"
    | Green s -> "Green(" ^ s ^ ")"

  let _pp graph =
    Printf.printf "Vertices: %d\n" (WDGraph.G.nb_vertex graph);
    Printf.printf "Edges: %d\n" (WDGraph.G.nb_edges graph);
    
    Printf.printf "\nVertices:\n";
    WDGraph.G.iter_vertex (fun v ->
      Printf.printf "  • %s\n" (SHterm.to_string v)
    ) graph;
    
    Printf.printf "\nEdges:\n";
    WDGraph.G.iter_edges_e (fun (v1, lbl, v2) ->
      Printf.printf "  • %s --[%s]--> %s\n"
        (SHterm.to_string v1)
        (edge_label_to_string lbl)
        (SHterm.to_string v2)
    ) graph
  
  let _pp_black (wdg : WDGraph.t) = 
    Hashtbl.iter (fun (u, v) _ -> Printf.printf "  • %s <--[Black]--> %s\n" (SHterm.to_string u) (SHterm.to_string v)) wdg.black_edges
  
  let print_graph (wdg : WDGraph.t) : unit = if wdg.unsat then Printf.printf "Unsat graph\n" else (_pp wdg.graph; _pp_black wdg)
  let print_quotient_graph (wdg : WDGraph.t) : unit = if wdg.unsat then Printf.printf "Unsat graph\n" else (_pp wdg.quotient_graph; _pp_black wdg)
end