open Graph

(* Define the graph module using OCamlgraph's Persistent.Digraph.ConcreteLabeled functor *)
module WDGraph = struct
  (* Define a custom graph with integer nodes and edges labeled with weights *)
  module G = Persistent.Digraph.ConcreteLabeled(struct
    type t = int
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
    mutable red_edges : (int * int) list;  (* List of edges with weight 0 *)
  }

  (* Initialize an empty graph structure *)
  let create () : t = {
    graph = G.empty;
    red_edges = [];
  }

  (* Add an edge to the graph *)
  let add_edge (g : t) (u : int) (v : int) (w : int) : unit =
    (* Add vertices if they don't exist and add the edge *)
    let g' = G.add_vertex (G.add_vertex g.graph u) v in
    let g' = G.add_edge_e g' (u, w, v) in
    g.graph <- g';
    (* Add to red_edges if the weight is 0 *)
    if w = 0 then g.red_edges <- (u, v) :: g.red_edges

  (* Traverse all edges and return a list of (source, target, weight) *)
  let traverse_edges (g : t) : (int * int * int) list =
    G.fold_edges_e (fun (u, w, v) acc -> (u, v, w) :: acc) g.graph []

  (* Check if any of the red edges forms a cycle *)
  let forms_cycle_with_red (g : t) : bool =
    List.exists (fun (u, v) ->
        let module Path = Path.Check(G) in
        let pc = Path.create(g.graph) in
        Path.check_path pc v u
      ) g.red_edges
end

