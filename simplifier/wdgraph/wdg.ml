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
    type t = int  (* Weight of edges *)
    let compare = compare
    let default = 0
  end)

  (* Define a record type for the graph structure *)
  type t = {
    mutable graph : G.t;                  (* The OCamlgraph graph *)
    mutable red_edges : (Slsyntax.SHterm.t * Slsyntax.SHterm.t) list; (* List of edges with weight 0 *)
    mutable unsat : bool;                 (* Indicates if the graph has become unsat or not *)
    mutable black_edges : (Slsyntax.SHterm.t * Slsyntax.SHterm.t, unit)  Hashtbl.t;  (* Hashtable to update and keep track of inequalities - black edges *)
  }

  (* Initialize an empty graph structure *)
  let create () : t = {
    graph = G.empty;
    red_edges = [];
    unsat = false;
    black_edges = Hashtbl.create 1;
  }

  let normalize_term_pair (u : Slsyntax.SHterm.t) (v : Slsyntax.SHterm.t) : Slsyntax.SHterm.t * Slsyntax.SHterm.t  =
    if Slsyntax.SHterm.compare u v <= 0 then (u, v) else (v, u)

  (* Add an edge to the graph. #TODO:Maybe can be shortened removing the 3rd if statement *)
  let add_edge (g : t) (u : Slsyntax.SHterm.t) (v : Slsyntax.SHterm.t) (w : int) : unit =
    if w = (-1) && u = v then g.unsat <- true; (* Black contradiction *)
    if not (g.unsat) then
      (* Check if both nodes exist in the variable_mapping *)
      if G.mem_vertex g.graph u && G.mem_vertex g.graph v then begin
        (* Check if there is an existing edge between u and v *)
        try
          let edge = G.find_edge g.graph u v in
          match edge with
          | (_,w',_) ->
            if w <> w' then (* #TODO:Should check what happens when the u!=v is present and want to add v<u *)
              (* Update the weight to 0 if the weights differ *)
              let g' = G.remove_edge_e g.graph (u, w', v) in
              let g' = G.add_edge_e g' (u, 0, v) in
              g.graph <- g';
              g.red_edges <- (u, v) :: g.red_edges;
              if w' = (-1) then Hashtbl.remove g.black_edges (normalize_term_pair u v)

        with Not_found ->
          (* If no edge exists, simply add it *)
          let g' = G.add_edge_e g.graph (u, w, v) in
          g.graph <- g';
          if w = 0 then g.red_edges <- (u, v) :: g.red_edges;
          if w = (-1) then Hashtbl.replace g.black_edges (normalize_term_pair u v) ()
        end
      else
        (* Add the nodes if they don't exist *)
        let g' = G.add_vertex (G.add_vertex g.graph u) v in
        let g' = G.add_edge_e g' (u, w, v) in
        g.graph <- g';
        (* Add to red_edges if the weight is 0 *)
        if w = 0 then g.red_edges <- (u, v) :: g.red_edges;
        if w = (-1) then Hashtbl.replace g.black_edges (normalize_term_pair u v) ()

  (* Traverse all edges and return a list of (source, target, weight) *)
  let traverse_edges (g : t) : (Slsyntax.SHterm.t * Slsyntax.SHterm.t * int) list =
    G.fold_edges_e (fun (u, w, v) acc -> (u, v, w) :: acc) g.graph []

  (* Check if any of the red edges forms a cycle *)
  let forms_cycle_with_red (g : t) : bool =
    List.exists (fun (u, v) ->
        let module Path = Path.Check(G) in
        let pc = Path.create(g.graph) in 
        Path.check_path pc v u
      ) g.red_edges

  (* Preprocess an Atom s.t. its terms are minimal, i.e. reducing and evaluating all possible exoresions. #TODO:This might be better to do it while transforing formula to dnf *)
  let preprocess_atom (a : Slsyntax.SHpure.t) : Slsyntax.SHpure.t = a (* #FIXME:Missing implementation *)
  
  (* Given a list of Atoms (conjunction of them) extract the terms and type of edge and add it to the graph *)
  let add_conjunctions (g : t) (atoms : Slsyntax.SHpure.t list): unit = 
      List.iter (fun a ->
        if not (g.unsat) then
          match a with
          | Slsyntax.SHpure.False -> g.unsat <- true;
          | Slsyntax.SHpure.Atom (op, tt) ->
            let a' = preprocess_atom a in
            match a' with
            | Slsyntax.SHpure.Atom (op, tt) ->
              let t0 = List.nth tt 0 in
              let t1 = List.nth tt 1 in
                match op with
                | Eq -> 
                    add_edge g t0 t1 1;
                    add_edge g t1 t0 1;
                | Neq -> 
                    add_edge g t0 t1 (-1);
                    add_edge g t1 t0 (-1);
                | Le -> add_edge g t0 t1 1;
                | Lt -> add_edge g t0 t1 0;
        ) atoms

  (* Simplify the graph, i.e. post-analyssis of diferent properties *)
  let simplify (g : t) : unit = 
    if not (g.unsat) then
      Printf.printf "Entering `simplify`.\n" (* #FIXME: Missing implementation *)
  
  (* Given a graph extract the terms and type of relation from edge and return a new conjunction list (all elements will be Atoms) *)
  let get_conjunctions (g : t) : Slsyntax.SHpure.t list = 
    if g.unsat then 
      [False]
    else 
      let edges = traverse_edges g in
      let rb_atoms = 
      List.filter (fun (u, v, w) -> w != (-1)) edges |>
      List.map (fun (u, v, w) ->
        match w with
        | 0 -> Slsyntax.SHpure.Atom(Lt, [u; v])
        | 1 -> Slsyntax.SHpure.Atom(Le, [u; v])
        | _ -> failwith "ERROR rebuilding graph, edge label (color) not suported"
      ) in
      let black_atoms = Hashtbl.fold (fun (u, v) _ acc -> Slsyntax.SHpure.Atom(Neq, [u; v]) :: acc ) g.black_edges [] in
      rb_atoms@black_atoms
end

