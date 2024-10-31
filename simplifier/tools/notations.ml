exception Error of string
exception EXCEPT of string
exception Succeed
exception Fail
exception UNKNOWN
exception Skip
exception Break
exception NotWhite

exception StError of string
exception NoRealizationForQuantifier of string
exception MemoryLeak of string
exception IndexOutOfBound of string
exception NoProc of string
exception NullPointerException of string
exception ExpToBExp
exception NotAVariable of string

let raiseStError mes = (print_endline ("StError: " ^ mes); raise (StError mes));;
        
module V = Map.Make(String)
module I = Map.Make(Int)
module Fmt = Format
         
(** Applying a function to all elements of a list (same as List.map)
    Input: A list of arbitrary values
    Output: A list of values obtained from applying the function on the the elements of the given list of values
    Example: ((+)1) |>>| [0;1;2;3] = [1;2;3;4],  fst |>>| [(1,0);(2,0);(3,0)] = [1;2;3]  *)
let (|>>|) f vs = List.map f vs

(** Filters a list of values which are satisfied by a given funcion *)
let (|>-) f vs = List.filter f vs

let (|->>) f (a, vs) = List.fold_left f a vs

let (|<-) k xs = List.mem k xs;;

(* let (:=) z y x = if x = z then y else x *)

(** Set equality *)
let rec (|==|) xs = function
	| [] -> xs = []
	| y::ys ->
		let (z, zs) = List.partition ((=) y) xs in
		z = [y] && zs |==| ys

let ( $ ) g f = fun x -> g (f x)

let (@@@) x y =
  let x' = List.filter (fun x1 -> not (x1 |<- y)) x in
  x' @ y
                       
module List = struct

  include List

  let union xx yy = List.fold_left (fun zz x -> if x |<- zz then zz else x::zz) yy xx

  let map_union f xx = List.fold_left (fun zz x -> union (f x) zz) [] xx

  let rec assoc3 key ls =
    match ls with
    | [] -> raise Not_found
    | (k,a,b)::ls1 when k = key -> (a,b)
    | c :: ls1 -> assoc3 key ls1
                     
end
;;
module L = List
                
