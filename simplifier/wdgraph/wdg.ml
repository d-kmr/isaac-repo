open Graph
open Slsyntax

(* Define the graph module using OCamlgraph's Persistent.Digraph.ConcreteLabeled functor *)
module WDGraph = struct
  (* Define a custom graph with integer nodes and edges labeled with weights *)
  module G = Persistent.Digraph.ConcreteLabeled(struct
    type t = Slsyntax.SHterm.t  (*Using terms as nodes*)
    let compare = compare
    let hash = Hashtbl.hash
    let equal = (=)
  end)(struct
    type t = int  (* label of edges *)
    let compare = compare
    let default = 0
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
    black_edges = Hashtbl.create 1;
    n_scc = -1;
    f_scc = None;
    r_scc = None;
    quotient_graph = G.empty;
  }

  let normalize_term_pair (u : SHterm.t) (v : SHterm.t) : SHterm.t * SHterm.t  =
    if SHterm.compare u v <= 0 then (u, v) else (v, u)

  (* Add an edge to the graph. #TODO:Maybe can be shortened removing the 3rd if statement *)
  let add_edge (g : t) (u : SHterm.t) (v : SHterm.t) (w : int) : unit =
    if w = (-1) && u = v then g.unsat <- true; (* Black contradiction *)
    if not (g.unsat) then
      (* Make sure nodes exist *)
      let g' = G.add_vertex (G.add_vertex g.graph u) v in
      let black_pair = normalize_term_pair u v in
        (* Check if there is an existing black edge between u and v *)
        try
          let _ = Hashtbl.find g.black_edges black_pair in
          let g' = G.add_edge_e g' (u, 0, v) in
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
                let g' = G.add_edge_e g' (u, 0, v) in
                g.graph <- g';
                g.red_edges <- (u, v) :: g.red_edges;
          with Not_found ->
            (* If no edge exists, simply add it *)
            let g' = G.add_edge_e g' (u, w, v) in
            g.graph <- g';
            if w = 0 then g.red_edges <- (u, v) :: g.red_edges

  let add_quotient_edge (g : t) (u : SHterm.t) (v : SHterm.t) (w : int) : unit =
    if not (g.unsat) then
      try
        let edge = G.find_edge g.quotient_graph u v in
        match edge with
        | (_,w',_) ->
          if w <> w' then
            (* Update the weight to 0 if the weights differ *)
            let g' = G.remove_edge_e g.quotient_graph (u, w', v) in
            let g' = G.add_edge_e g' (u, 0, v) in
            g.quotient_graph <- g'
      with Not_found -> 
        let g' = G.add_edge_e g.quotient_graph (u, w, v) in
        g.quotient_graph <- g'

  (* Check if any of the red edges forms a cycle *)
  let forms_cycle_with_red (g : t) : bool =
    let module Path = Path.Check(G) in
    let pc = Path.create(g.graph) in 
    List.exists (fun (u, v) -> Path.check_path pc v u) g.red_edges
  
  (* Preprocess an Atom s.t. its terms are minimal, i.e. reducing and evaluating all possible exoresions. #TODO:This might be better to do it while transforing formula to dnf *)
  let preprocess_and_eval_atom (a : SHpure.t) : SHpure.t = a (* #FIXME:Missing implementation *)

  (*let eval_sum_dif (a : SHpure.t) : SHpure.t = 
    match a with 
    |Add tt -> let [tt_i; tt_v] = List.partition(fun e -> e == Int _) tt in let sum = List.fold_left(fun e, acc -> e+acc) tt_i 0 in Add(tt_v :: [Int sum])
    |Sub tt -> let [tt_i; tt_v] = List.partition(fun e -> e == Int _) tt in let sum = List.fold_left(fun e, acc -> e+acc) tt_i 0 in Sub(tt_v :: [Int sum])
    |_ -> a*)
  (* Postprocess an Atom s.t. its terms are minimal *)
  let rec postprocess_and_eval_terms (g : t) (a : Slsyntax.SHterm.t) : Slsyntax.SHterm.t =
    (* on complex epesion try to recursively match terms into representative method until u find one and stop *)
    let r_scc = begin match g.r_scc with 
    | Some f -> f
    | _ -> failwith "r_scc not computed before `postprocess_and_eval_terms`"
    end in
    let f_scc = begin match g.f_scc with 
    | Some f -> f
    | _ -> failwith "f_scc not computed before `postprocess_and_eval_terms`"
    end in
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
          | SHpure.Atom (op, tt) ->
            let a' = preprocess_and_eval_atom a in
            match a' with
            | SHpure.Atom (op, tt) ->
              let t0 = List.nth tt 0 in
              let t1 = List.nth tt 1 in
                match op with
                | Eq -> 
                    add_edge g t0 t1 1;
                    add_edge g t1 t0 1;
                | Neq -> 
                  g.graph <- G.add_vertex (G.add_vertex g.graph t0) t1;
                  Hashtbl.replace g.black_edges (normalize_term_pair t0 t1) ();
                | Le -> add_edge g t0 t1 1;
                | Lt -> add_edge g t0 t1 0;
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
        let black_pairs_in_same_scc = Hashtbl.fold (fun (u, v) _ acc -> acc || (f_scc u == f_scc v)) g.black_edges false in
        if black_pairs_in_same_scc then g.unsat <- true (* Black contradiction 2 *)
        else 
            (* Compute representatives for SCCs *)
            let scc_nodes = Hashtbl.create n_scc in
            G.iter_vertex (fun v -> Hashtbl.add scc_nodes (f_scc v) v) g.graph;
            
            let representatives = Array.make n_scc (SHterm.Int 0) (* Placeholder initial value *) in
            for i = 0 to n_scc - 1 do
              let nodes = Hashtbl.find_all scc_nodes i in
              let int_terms = List.filter (function SHterm.Int _ -> true | _ -> false) nodes in
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
  
  (* Given a graph extract the terms and type of relation from edge and return a new conjunction list (all elements will be Atoms) *)
  let get_conjunctions (g : t) : SHpure.t list = 
    if g.unsat then 
      [False]
    else 
      let rb_atoms = 
      G.fold_edges_e (fun (u, w, v) acc -> 
        match w with
        | 0 -> SHpure.Atom(Lt, [u; v]) :: acc
        | 1 -> SHpure.Atom(Le, [u; v]) :: acc
        | _ -> failwith "ERROR rebuilding graph, edge label (color) not suported"
      ) g.quotient_graph [] in
      let black_atoms = Hashtbl.fold (fun (u, v) _ acc -> SHpure.Atom(Neq, [u; v]) :: acc ) g.black_edges [] in
      let eq_atoms = List.map(fun (u, v) -> SHpure.Atom(Eq, [u; v])) g.eq_representative_pairs in
      eq_atoms@rb_atoms@black_atoms

  let get_conjunctions_eval_atom (g : t) : SHpure.t list = 
    let eval_atom a = 
      match a with
      |SHpure.Atom(Le, [Int x; Int y]) -> if x <= y then SHpure.True else SHpure.False
      |SHpure.Atom(Lt, [Int x; Int y]) -> if x < y then SHpure.True else SHpure.False
      |SHpure.Atom(Neq, [Int x; Int y]) -> if x != y then SHpure.True else SHpure.False
      |SHpure.Atom(Eq, [Int x; Int y]) -> if x == y then SHpure.True else SHpure.False
      |_ -> a
    in
    if g.unsat then 
      [False]
    else 
      let rb_atoms = 
      G.fold_edges_e (fun (u, w, v) acc -> 
        match w with
        | 0 -> eval_atom(SHpure.Atom(Lt, [u; v])) :: acc
        | 1 -> eval_atom(SHpure.Atom(Le, [u; v])) :: acc
        | _ -> failwith "ERROR rebuilding graph, edge label (color) not suported"
      ) g.quotient_graph [] in
      let black_atoms = Hashtbl.fold (fun (u, v) _ acc -> eval_atom(SHpure.Atom(Neq, [u; v])) :: acc ) g.black_edges [] in
      let eq_atoms = List.map(fun (u, v) -> eval_atom(SHpure.Atom(Eq, [u; v]))) g.eq_representative_pairs in
      let red_atoms = eq_atoms@rb_atoms@black_atoms in
      if List.exists(fun e -> e == SHpure.False) red_atoms then [False] 
      else List.filter(fun e -> e != SHpure.True) red_atoms
end

