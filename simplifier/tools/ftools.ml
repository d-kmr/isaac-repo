open Notations
open PrintTools
   
let headerInit = "[slac-init]"

let headerCapture = "[slac-capture]"

let headerParserCabs = "[slac-parser-cabs]"

let headerParser = "[slac-parser]"
                  
let headerTransformer = "[slac-transformer]"
                  
let headerAnalyzer = "[slac-analyzer]"

let headerAnalyzerMarshal = "[slac-analyzer-marshal]"                   

   
(** The logical or operation among a list of boolean values
    Input: A list of boolean values
    Output: Result of OR operations among the input values
    Example: l_or [] = false,  l_or [false;true;false] = true *)
let l_or lst = List.fold_left (||) false lst

(** The logical and operation among a list of boolean values
    Input: A list of boolean values
    Output: Result of AND operations among the input values
    Example: l_and [] = true, l_and [false;true;false] = false *)
let l_and lst = List.fold_left (&&) true lst

let rec valid = function
	| [] -> None
	| Some x :: _ -> Some x
	| None :: t -> valid t

let rec valids_only = function
	| [] -> []
	| None :: t -> valids_only t
	| Some x :: t -> x :: valids_only t
;;
(** Drop common elements from two lists *)
let rec drop_common xs = function
	| [] -> (xs, [])
	| h::t ->
	   let (a, b) = List.partition ((=) h) xs in
	   match a with
	   | [] -> let (c, d) = drop_common b t in (c, h::d)
	   | _ ->  let (c, d) = drop_common b t in (c, d)
;;
let rec common xs = function
	| [] 		-> []
	| h::t 	->
		let (a, b) = List.partition ((=) h) xs in
		match a with
		| [] -> let c = common b t in c
		| _ ->  let c = common b t in h::c
;;
let rec has_duplicate = function
	| [] -> false
	| x::xs -> (x |<- xs) || (has_duplicate xs)
;;
let concat_options r1 r2 =
  match r1, r2 with
  | None, _ -> r2
  | _, None -> r1
  | Some rr1, Some rr2 -> Some (rr1@rr2)
;;
           
let rec concatS s f = function
	| [] -> ""
	| [o] -> f o
	| h::t -> (f h) ^ s ^ (concatS s f t)

let fstrL f s () =
  concatS s (f ())
  
let rec iterS f delim = function
	| [] -> p ""
	| [x] -> f x
	| h::t -> f h; p delim; iterS f delim t

(*
	(x, [a,b,c])  [[(y,p)], [(y,q)]] = [[(x,a),(y,p)],	[(x,b),(y,p)],	[(x,c),(y,p)]] @	[[],	[],	[]]
 *)
let multiply accum (x, xs) = if xs = [] then accum else
	match accum with
	| [] -> (fun a -> [(x, a)]) |>>| xs
	| _ -> (fun h -> ((fun a -> (x, a)::h) |>>| xs)) |>>| accum |> List.concat

let cross (ls:('b * 'a list) list) = (multiply) |->> ([], ls)

(** Find all permutations *)
(*
let rec permute2 xs =
  let rec f all pre = function
  	| [] -> (pre, [])::all
  	| x::xs as l -> f ((pre, l)::all) (pre @ [x]) xs
  in
  let insert x xs = (fun (ws,vs) -> ws @ (x::vs)) |>>| (f [] [] xs) in
  match xs with
  | [] -> []
	| z::[] -> [[z]]
  | z::zs -> List.concat ((insert z) |>>| (permute2 zs))
 *)

let rec permute xs =
  let rec del x = function
	| [] -> []
	| y::ys -> if x = y then ys else y::(del x ys)
  in
  match xs with
  | [] -> []
  | [x] -> [[x]]
  | _ -> (fun ac x -> ac @ ((fun zs -> x::zs) |>>| (permute (del x xs)))) |->> ([], xs)


let (>><<) xs ys =
  let f zs x = (fun z -> (z,x)) |>>| zs in
  List.flatten ((f xs) |>>| ys)

let uniq xs =
  let rec uniq' ys = function
    | [] -> ys
    | x::xs -> if x |<- ys then uniq' ys xs else uniq' (x::ys) xs
  in
  List.rev (uniq' [] xs)

let cassert b c = if b then () else raiseStError ("Assert failed: " ^ c)

let is_main mn =
  if String.length mn > 5
  then String.sub mn 0 5 = "main@"
  else false

let _List_hd ls =
  try
    List.hd ls
  with
    _ -> raiseStError "LIST HD PROBLEM"

let rec parallel_subs f e = function
  | [] -> e
  | (to_be, by)::xs ->
     let matched, unmatched = List.partition (fun (to_be', _) -> to_be' = by) xs in
     if List.length matched = 0 then 
       let e' = f to_be by e in
       parallel_subs f e' xs
     else
       parallel_subs f e (matched@((to_be, by)::unmatched))

let opcat s1 s2 =
  match s1, s2 with
  | None, _ -> s2
  | _, None -> s1
  | Some x1, Some x2 -> Some (x1@@@x2)

let op_p f = function
  | Some a -> f a
  | None -> p "<NONE>"

let print_pairs p1 sp p2 spn = iterS (fun (a,b) -> p1 a; p sp; p2 b) spn
  
let rec take n = function
    [] when n = 0 -> []
  | [] -> raiseStError ((string_of_int n) ^ " is more than the length of list")
  | _::_ when n = 0 -> []
  | x::xs -> x::take (n-1) xs;;

let string_of_list f xs =
  let rec aux = function
      [] -> ""
    | [x] -> f x
    | x::xs ->
       f x ^ ";" ^ aux xs
  in
  "[" ^ aux xs ^ "]"


let print_list f xs =
  let rec aux = function
      [] -> p ""
    | [x] -> f x
    | x::xs ->
       f x; p ";"; aux xs
  in
  p "["; aux xs; p "]"
;;

let print_gc stat =
  Fmt.printf "@[major words:%f@." stat.Gc.major_words;
  Fmt.printf "@[minor words:%f@." stat.Gc.minor_words;
  Fmt.printf "@[major collections:%d@." stat.Gc.major_collections;
  Fmt.printf "@[heap words: %d@." stat.Gc.heap_words;
  Fmt.printf "@[free words: %d@." stat.Gc.free_words;
  Fmt.printf "@[live words: %d@." stat.Gc.live_words;
  Fmt.printf "@[live blocks: %d@." stat.Gc.live_blocks;
  Fmt.printf "@[free blocks: %d@." stat.Gc.free_blocks;  
  Fmt.printf "@[compaction: %d@." stat.Gc.compactions
;;

let is_debug = ref false;;

let pause msg =
  if !is_debug then
    begin
      if msg = "" then pn "Paused. Press ENTER to continue." else p msg;
      let _ = read_line () in
      ()
    end
  else
    ()
;;

let foldri n f : 'a list =
  let rec foldri acc = function
    | 0 -> acc
    | i -> foldri (f (i-1) :: acc) (i-1)
  in
  foldri [] n
;;

let split delim (str : string) : string list =
  if str = "" then
    []
  else
    let ls : char list = List.init (String.length str) (String.get str) in
    let to_string l_chars =
      (fun s c -> s ^ (String.make 1 c)) |->> ("", l_chars)
    in
    let f (prevs, cur) c =
      if c = delim then
        (to_string (List.rev cur)::prevs, [])
      else
        (prevs, c::cur)
    in
    let (prevs, cur) = List.fold_left f ([],[]) ls in
    List.rev (to_string (List.rev cur)::prevs)
;;

(** Compute largest number from a list.  maxi [1;2;0;0] = 2,  maxi [] = 0 *)  
let rec maxi xs =
  let max a b = if a > b then a else b in
  match xs with
  | [] -> 0
  | [x] -> x
  | x::xs -> max x (maxi xs)
;;

let fork_and_call prog args =
  try
    let pid = Unix.fork () in
    if (pid = 0)
    then prog args
    else ignore(Unix.wait ())
  with
  | Unix.Unix_error (err,s1,s2) ->
     Fmt.printf "@[Error: %s \"%s %s\"@." (Unix.error_message err) s1 s2;
     exit 0

