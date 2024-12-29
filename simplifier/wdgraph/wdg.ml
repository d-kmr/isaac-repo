module WDGraph = struct
  (* Type definitions *)
  type edge = { target : int; weight : int }
  type graph = {
    adj_list : (int, edge list) Hashtbl.t;  (* Adjacency list *)
    mutable red_edges : (int * int) list;  (* List of weight-0 edges *)
  }

  (* Create an empty graph *)
  let create_graph () : graph =
    { adj_list = Hashtbl.create 1; red_edges = [] }

  (* Ensure a node exists in the graph *)
  let ensure_node (g : graph) (u : int) : unit =
    if not (Hashtbl.mem g.adj_list u) then
      Hashtbl.add g.adj_list u []

  (* Add an edge to the graph, dynamically adding nodes if needed *)
  let add_edge (g : graph) (u : int) (v : int) (w : int) : unit =
    (* Ensure both nodes exist *)
    ensure_node g u;
    ensure_node g v;
    (* Add the edge *)
    let edges = Hashtbl.find g.adj_list u in
    Hashtbl.replace g.adj_list u ({ target = v; weight = w } :: edges);
    if w = 0 then g.red_edges <- (u, v) :: g.red_edges

  (* Helper function to perform DFS *)
  let dfs (g : graph) (visited : bool array) (start : int) (target : int) : bool =
    let rec visit node =
      if visited.(node) then false
      else begin
        visited.(node) <- true;
        let neighbors = Hashtbl.find_opt g.adj_list node |> Option.value ~default:[] in
        List.exists (fun { target = next_node; _ } -> next_node = target || visit next_node) neighbors
      end
    in
    visit start

  (* Check if the addition of an edge creates a cycle with a weight-0 edge *)
  let forms_cycle_with_red (g : graph) : bool =
    List.exists (fun (u, v) ->
        let max_node = Hashtbl.fold (fun k _ acc -> max k acc) g.adj_list 0 in
        let visited = Array.make (max_node + 1) false in
        dfs g visited v u
      ) g.red_edges

  (* Traverse all edges in the graph *)
  let traverse_edges (g : graph) : (int * int * int) list =
    Hashtbl.fold (fun u edges acc ->
        List.fold_left (fun acc { target; weight } -> (u, target, weight) :: acc) acc edges
      ) g.adj_list []
end

