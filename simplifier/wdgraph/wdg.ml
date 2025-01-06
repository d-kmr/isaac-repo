open Graph

(* Define the graph module using OCamlgraph's Persistent.Digraph.ConcreteLabeled functor *)
module WDGraph = struct
  type node = {
    id : int;
    alias : string;
  }
  module Node = struct
    type t = node
    let compare n1 n2 = compare n1.id n2.id
    let hash n = Hashtbl.hash n.id
    let equal n1 n2 = n1.id = n2.id
  end
  (* Define a custom graph with custom nodes and edges labeled with weights *)
  module G = Persistent.Digraph.ConcreteLabeled(Node)(struct
    type t = int  (* Weight of edges *)
    let compare = compare
    let default = 0
  end)

  (* Define a record type for the graph structure *)
  type t = {
    mutable graph : G.t;                  (* The OCamlgraph graph *)
    mutable red_edges : (node * node) list;  (* List of edges with weight 0 *)
  }

  (* Initialize an empty graph structure *)
  let create () : t = {
    graph = G.empty;
    red_edges = [];
  }

  let node_id(v: node) : int = v.id

  (* Add an edge to the graph *)
  let add_edge (g : t) (u : node) (v : node) (w : int) : unit =
    (* Add vertices if they don't exist and add the edge *)
    let g' = G.add_vertex (G.add_vertex g.graph u) v in
    let g' = G.add_edge_e g' (u, w, v) in
    g.graph <- g';
    (* Add to red_edges if the weight is 0 *)
    if w = 0 then g.red_edges <- (u, v) :: g.red_edges

  (* Traverse all edges and return a list of (source, target, weight) *)
  let traverse_edges (g : t) : (node * node * int) list =
    G.fold_edges_e (fun (u, w, v) acc -> (u, v, w) :: acc) g.graph []

  (* Check if any of the red edges forms a cycle *)
  let forms_cycle_with_red (g : t) : bool =
    List.exists (fun (u, v) ->
        let module Path = Path.Check(G) in
        let pc = Path.create(g.graph) in
        Path.check_path pc v u
      ) g.red_edges
end

