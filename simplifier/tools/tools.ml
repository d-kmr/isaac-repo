(*--------------------------------------------*)
(* Tools				*)
(*--------------------------------------------*)
open Notations
open PrintTools
   
(* For parse error message *)
(* (errstart,errend,errline) *)
exception ParseError of int * int * int;; 
                        
let fst3 (x,_,_) = x;;
let snd3 (_,y,_) = y;;
let thd3 (_,_,z) = z;;

let fst4 (x,_,_,_) = x;;
let snd4 (_,y,_,_) = y;;
let thd4 (_,_,z,_) = z;;
let fth4 (_,_,_,w) = w;;

let id x = x;;

let extract_opt none f_some opt =
  match opt with
  | Some x -> f_some x
  | None -> none

(* text_getaround range bytes i *)
(* get sub bytes around i-th character of bytes *)
(* output: (p,j,q-p) *)
(* p: max(i-range, pos of the last '\n' before the i-th character) *)
(* j: pos of the i-th character between [p,q] *)
(* q: min(i+range, pos of the first '\n' after the i-th character) *)
let text_getaround range bytes i =
  if (Bytes.get bytes i = '\n') then (i,0,1) else
  let p = ref i in
  let q = ref (i+1) in
  while !p>=0 && !p>=(i-range) && Bytes.get bytes !p <> '\n' do p := !p-1 done;
  while !q<Bytes.length bytes && !q<=(i+range) && Bytes.get bytes !q <> '\n' do q := !q+1 done;
  p := !p+1;
  (!p, i - !p, !q - !p)

let checkTime f arg =
  let tm1 = Sys.time () in
  let _ = f arg in
  let tm2 = Sys.time () in  
  print_endline (string_of_float (tm2 -. tm1))

module Strset = struct
  include Set.Make(String)

  type t = Set.Make(String).t

  let pp sep fmt vvv = Fmt.fprintf fmt "%a" (pp_list "" sep Fmt.pp_print_string) (elements vvv)
(*
  let pps sep (_:unit) vvv = Fmt.sprintf "%a" (pps_list "" sep pps_string) (elements vvv)

  let print vvv = Fmt.printf "@[%a@]" (pp ", ") vvv
                     
  let print vvv = Fmt.printf "@[%a@." (pp ", ") vvv

  let to_string sym vvv = pps sym () vvv
 *)                
  let mapUnion f xx = List.fold_left (fun s x -> union s (f x)) empty xx

  let unionL = mapUnion id

  let genFresh sym vvvAvoid =   
    let rec aux n =
      let v = sym^(string_of_int n) in
      if mem v vvvAvoid then aux (n+1) else v
    in aux 0

  let genFreshMany sym vvvAvoid len =
    let rec aux vvvNew vvvAvoid len = 
	  match len with
      | 0 -> vvvNew
      | _ -> let v = genFresh sym vvvAvoid in
	         aux (add v vvvNew) (add v vvvAvoid) (len-1)
    in
    aux empty vvvAvoid len
    
end
;;

module Intset = struct
  include Set.Make(Int)
        
  let mapUnion f xx = List.fold_left (fun s x -> union s (f x)) empty xx

  let unionL = mapUnion id
                    
  let to_string sym nnn =
    fold (fun x a ->
        let x' = string_of_int x in
        if a = "" then x' else x' ^ sym ^ a)
      nnn
      ""

  let println nnn = print_endline (to_string ", " nnn)
                  
end
;;
         
let rec compareList compare xx yy =
  match xx,yy with
  | [],[] -> 0
  | [],_ -> -1
  | _,[] -> 1
  | x::xx1,y::yy1 when compare x y = 0 -> compareList compare xx1 yy1
  | x::_,y::_ -> compare x y
;;                        
(* "to_abstract x" produces an abstract data (num,str,bb,xx) of x (bb is a list of base type) *)
(* "compare" is a comparison function of x's *)
let rec genCompare toAbstract baseCompare x y =
  let absX : int * string * 'a * 'b = toAbstract x in
  let absY : int * string * 'a * 'b = toAbstract y in
  match absX,absY with
  | (numX,_,_,_),(numY,_,_,_) when numX <> numY -> compare numX numY
  | (_,strX,_,_),(_,strY,_,_) when strX <> strY -> compare strX strY
  | (_,_,bb,_),(_,_,cc,_) when (compareList baseCompare bb cc) <> 0 -> compareList baseCompare bb cc
  | (_,_,_,xx),(_,_,_,yy) -> compareList (genCompare toAbstract baseCompare) xx yy
;;                        

(*
let print_warn tag mes = print_endline @@ "[W " ^ tag ^ "] " ^ mes

let print_error tag mes = print_endline @@ "[E " ^ tag ^ "] " ^ mes

let print_mes tag mes = print_endline @@ "[_ " ^ tag ^ "] " ^ mes
 *)

(* applyDiff f [a;b;c] --> [fab;fac;fbc] *)                        
let applyDiff (f: 'a -> 'a -> 'b) (ls: 'a list) : 'b list =
  let rec aux res ls = 
    match ls with
    | [] -> res
    | x::xl ->
       let res' = List.fold_left (fun res' y -> (f x y) :: res') res xl in
       aux res' xl
  in
  aux [] ls
;;

let size_of_list sz_one (someL: 'a list) = List.fold_left (fun n x -> n + sz_one x) 0 someL
;;                        
let size_of_stringL ss = size_of_list String.length ss
;;                      
                        
let myOrdinal n =
  let th = 
    if n = 11 || n = 12 then "-th"
    else
      match n mod 10 with
      | 1 -> "st"
      | 2 -> "nd"
      | 3 -> "rd"
      | _ -> "-th"
  in
  (string_of_int n) ^ th

let order1 v1 v2 = if v1 > v2 then 1 else if v1 < v2 then -1 else 0
;;
let order2 (v1,_) (v2,_) = order1 v1 v2
;;
let order3 (v1,_,_) (v2,_,_) = order1 v1 v2
;;
let order4 (v1,_,_,_) (v2,_,_,_) = order1 v1 v2
;;
let rec sum ls = if ls = [] then 0 else List.hd ls + sum (List.tl ls)
;;
let rec maxlist ls = List.fold_right max ls 0
;;
let setminus ls1 ls2 = List.filter (fun x -> not(List.mem x ls2)) ls1
;;
let belongsAll ll x = List.for_all (fun ls -> List.mem x ls) ll
;;
let rec union ls1 ls2 =
  match ls2 with
  | [] -> ls1
  | x::ls2' ->
     if List.mem x ls1
     then union ls1 ls2'
	 else union (x::ls1) ls2'
;;
let unionL (ll: 'a list list) : 'a list = List.fold_left (fun ls1 ls2 -> union ls1 ls2 ) [] ll
;;

let eqList eq ls1 ls2 =
  let rec eqListOne a lsCheck =
    match lsCheck with
    | [] -> raise Fail
    | (x,b) :: lsCheck1 when b = true && eq x a -> (x,false)::lsCheck1
    | hd :: lsCheck1 -> hd :: (eqListOne a lsCheck1)
  in
  let len1 = List.length ls1 in
  let len2 = List.length ls2 in
  try
    if len1 <> len2 then raise Fail else
    let _ls2 = ref (List.map (fun x -> (x,true)) ls2) in      
    List.iter (fun a -> _ls2 := eqListOne a !_ls2) ls1;
    true
  with
  | Fail -> false
;;

let eqList1 eq ls1 ls2 = eqList eq ls1 ls2
;;
let eqList2 eq lls1 lls2 = eqList (eqList1 eq) lls1 lls2
;;
let rec findOption cond ls =
  match ls with
  | [] -> None
  | hd::tail -> if cond hd then (Some hd) else findOption cond tail
;;
let findPosOption x ls = 
  let rec findPosRec x' ls' n = match ls' with
  | [] -> None
  | hd::tail -> if x' = hd then Some n else findPosRec x' tail (n+1)
  in findPosRec x ls 0
;;
let findItemOption key ls =
  try
    let itm = List.assoc key ls in
    Some itm
  with
    Not_found -> None
;;

let isSubList ls1 ls2 = 
List.fold_right (fun x b -> (List.mem x ls2)&& b) ls1 true;;

let rec isSubListSorted order ls1 ls2 = match ls1,ls2 with
  | [], _ -> true
  | x::ls1', y::ls2' ->
     if order x y = 0 then isSubListSorted order ls1' ls2
     else if order x y > 0 then isSubListSorted order ls1 ls2'
     else false
  | _, _ -> false
					     
  
let countElemLst x lst = 
  let rec countElemLstRec y ls n = match ls with
    | [] -> n
    | hd::tail -> if y = hd then countElemLstRec y tail (n+1)
		  else countElemLstRec y tail n
  in countElemLstRec x lst 0;;

let isLinearList x ls = 
  let n = countElemLst x ls in
  if n = 1 then true else false;;
  
let rec elimElemLst x lst = match lst with
  | [] -> []
  | hd::tail -> if x = hd then elimElemLst x tail else hd::(elimElemLst x tail);;

let rec elimElemLstL xlst lst = match xlst with
  | [] -> lst
  | x::xlst' -> elimElemLstL xlst' (elimElemLst x lst);;

let interLst ls1 ls2 = 
  let rec interLstRec lst1 lst2 rest = match lst2 with
  | [] -> rest
  | x::xl -> if List.mem x lst1 then interLstRec lst1 xl (x::rest) 
	else interLstRec lst1 xl rest
  in List.rev(interLstRec ls1 ls2 []);;

(* zipLst [1;2;3] [a;b;c] is [(1,a);(2,b);(3,c)] *)
let rec zipLst ls1 ls2 = 
  match ls1,ls2 with
  | (hd1::tl1,hd2::tl2) -> (hd1,hd2)::(zipLst tl1 tl2)
  | (_,_) -> [];;

let rec zipLst3 ls1 ls2 ls3 =
  match ls1,ls2,ls3 with
  | (hd1::tl1,hd2::tl2,hd3::tl3) -> (hd1,hd2,hd3)::(zipLst3 tl1 tl2 tl3)
  | (_,_,_) -> [];;

(* checkSameLists eq xl yl is true if |xl|=|yl| and eq(x,y) = true for all x in xl and y in yl *)
let checkSameLists eq xl yl = List.length xl = List.length yl && List.for_all eq (zipLst xl yl)

(* genLstDown 3 is [2;1;0] *)
let rec genLstDown n = if n = 0 then [] else (n-1)::(genLstDown (n-1))

(* genLst 3 is [0;1;2] *)                     
let genLst n =
  let rec aux res i = if i<0 then res else aux (i::res) (i-1) in
  aux [] (n-1)

let genLstAB n m =
  let _res = ref [] in
  for i = n to m do
    _res := i :: !_res;
  done;
  List.rev !_res
;;

let putIndexes ls =
  let len = List.length ls in
  let idxL = genLst len in
  zipLst idxL ls
;;

let rec genNumLL n len = if len = 0 then [[]] else 
     let res = genNumLL n (len-1) in
     let lstN = genLst n in
     let addHd n = List.map (fun l->n::l) res in
     List.concat (List.map (fun x-> addHd x) lstN);;

let rec genNbools len = 
  let i2b n = if n = 0 then false else true in
  let iL2bL ls = List.map i2b ls in
  List.map iL2bL (genNumLL 2 len);;

let rec genNtrues len = 
  let i2b n = true in
  let iL2bL ls = List.map i2b ls in
  List.map iL2bL (genNumLL 1 len);;

let rec allTrueMes cond lst = 
	match lst with
	| [] -> None
	| hd::tail -> if cond hd then allTrueMes cond tail 
		        else Some hd;;

let allTrue cond lst : bool = match allTrueMes cond lst with
  | None -> true
  | Some _ -> false;;

let put_index_to_list ls =
  let n = List.length ls in
  let indexL = genLst n in
  zipLst indexL ls

(* makeCombPairs [1;2;3] returns [(2,3);(1,3);(1,2)] *)
let makeCombPairs ls =
  let rec aux res xl =
    match xl with
    | [] -> res
    | x::xl1 -> aux (List.fold_left (fun yl y -> (x,y)::yl) res xl1) xl1
  in
  aux [] ls

(* makeCombPairs2 [1;2] ['A';'B'] returns [(3,'b'); (3,'a'); (2,'b'); (2,'a'); (1,'b'); (1,'a')] *)
let makeCombPairs2 ls1 ls2 =
  let rec aux res xl =
    match xl with
    | [] -> res
    | x::xl1 -> aux (List.fold_left (fun yl y -> (x,y)::yl) res ls2) xl1
  in
  aux [] ls1

(* makeDiffPairs [1;2;3] returns [(3,2); (3,1); (2,3); (2,1); (1,3); (1,2)] *)
let makeDiffPairs ls =
  let rec aux res xl =
    match xl with
    | [] -> res
    | x::xl1 -> aux (List.fold_left (fun yl y -> if x = y then yl else (x,y)::yl) res ls) xl1
  in
  aux [] ls
  
(* Generating Fresh Variables *)
let genFreshVar_list sym vlst =   
  let rec genFreshVarRec s l n =
    let newVar = s^(string_of_int n) in
    if List.mem newVar l then genFreshVarRec s l (n+1) 
    else newVar
  in genFreshVarRec sym vlst 0
;;
let rec genFreshVarL_list sym lst len = 
	if len = 0 then [] else
	let v = genFreshVar_list sym lst in
	v::(genFreshVarL_list sym (v::lst) (len-1))
;;
let string_of_list (f: 'a -> string) sepsym strL = 
	List.fold_right 
	(fun x y -> if y = "" then f x else (f x)^sepsym^y)
	strL ""
;;

let string_of_V (f: string -> 'a -> string) sepsym strV = 
	V.fold
	(fun k x y -> if y = "" then f k x else (f k x)^sepsym^y)
	strV ""
;;

let string_of_V' (f: 'a -> string) sepsym strV =
  let f' key x = f x in
  string_of_V f' sepsym strV
;;
let string_ends_with suffix s =
  let suffix_len = String.length suffix in
  (suffix_len <= String.length s) && suffix = String.sub s (String.length s - suffix_len) suffix_len
;;

(*let mapComma f strL = mapSymbol f (", ") ("") strL;;*)
let mapComma f strL = string_of_list f (", ") strL;;

let concatStrLComma = mapComma (fun s -> s);;

(*let mapNewLine f strL = mapSymbol f ("\n") ("") strL;;*)
let mapNewLine f strL = string_of_list f ("\n") strL;;

let concatStrLNewLine = mapNewLine (fun s -> s);;

let rec replLstNth n e ls = match ls with
  | [] -> []
  | hd::tl -> if n = 0 then e::tl else hd::(replLstNth (n-1) e tl);;

let permute_optlist (ols : 'a option list) : 'a list option = 
	if List.exists (fun x-> x = None) ols then None else
	  let ll = List.map (fun x -> match x with None -> [] | Some y -> [y]) ols in
	Some (List.concat ll);;

let func_option f (opt : 'a option) : 'b option = match opt with
  | None -> None
  | Some a -> Some (f a);;

let getPos v lst = 
  let rec getPosRec x l n result = match l with
    | [] -> result
    | hd::tl -> 
	if x = hd then getPosRec x tl (n+1) (n::result) 
	else getPosRec x tl (n+1) result
  in List.rev (getPosRec v lst 0 []);;

let rec isLinear lst = match lst with
  | [] -> true
  | x::xl -> if List.mem x xl then false else isLinear xl;;

let rec isLinearSorted ls = match ls with
  | [] -> true
  | x::ls' -> match ls' with
	      | [] -> true
	      | y::ls'' -> if x = y then false else isLinearSorted ls';;
  
(* occurLst ["a";"b";"b";"b"] returns ["a0";"b0";"b1";"b2"]  *)
let occurLst1 ls = 
    let rec occurLstRec ls rest memo = 
      match rest with
      | [] -> ls
      | x::xl -> 
	 let n = countElemLst x memo in
	 occurLstRec (ls@[(x,n)]) xl (x::memo)
    in occurLstRec [] ls [];;

let occurLst ls = List.map (fun (x,n)->x^(string_of_int n)) (occurLst1 ls);;

(* gatherKey2 [(1,"a","A");(2,"b","B");(1,"c","C");(1,"d","D")] returns [("a","A");("c","C");("d","D")]  *)
let gatherKey2 ls key = 
  let rec gatherKeyRec ls ky rest = match rest with
    | [] -> ls
    | (k,x,y)::xl -> if k = ky then gatherKeyRec (ls@[(x,y)]) ky xl else gatherKeyRec ls ky xl
  in gatherKeyRec [] key ls;;
  
let memEq eq x ls = List.exists (eq x) ls;;

let sublistEq eq ls1 ls2 = List.for_all (fun x -> memEq eq x ls2) ls1;;

let eqlistEq eq ls1 ls2 = (sublistEq eq ls1 ls2) && (sublistEq eq ls2 ls1);;

let strhd str = String.get str 0;;

let strtl str = 
  let len = String.length str in
  String.sub str 1 (len-1);;

let rec lexorder (ord : 'a -> 'a -> int) ls1 ls2 = 
  match (ls1, ls2) with
  | ([],[]) -> 0
  | (_,[]) -> 1
  | ([],_) -> -1
  | (_,_) -> 
       if ord (List.hd ls1) (List.hd ls2) > 0 then 1 
       else if ord (List.hd ls1) (List.hd ls2) < 0 then -1
       else lexorder ord (List.tl ls1) (List.tl ls2) ;;

let rec toCharList s = 
  let len = String.length s in
  if len = 0 then [] else 
  let hd = String.get s 0 in
  let tl = String.sub s 1 (len - 1) in
  hd::(toCharList tl);;

let strlexorder s1 s2 = 
  let chorder c1 c2 = if c1 > c2 then 1 else if c1 < c2 then -1 else 0 in
  let s1' = toCharList s1 in
  let s2' = toCharList s2 in
  lexorder chorder s1' s2';;
(*
(* mergeL (>) [[1;4;7];[2;5;8];[3;6;9]] returns [1;2;3;4;5;6;7;8;9]*)
let mergeL order = List.fold_left (fun l l' -> List.merge order l l') [];;
 *)
let mkEqClass elems eql = 
  let n = List.length elems in
  let numL = genLst n in
  let table = ref (zipLst elems numL) in
  let gatherElemIndex n = 
    let lst = List.filter (fun (x,i) -> i = n) !table in
    List.map (fun (x,_) -> x) lst 
  in 
  let rec updateIndexRec i j tbl rest = match tbl with
    | [] -> List.rev rest
    | (e,k)::tbl' -> if i = k then updateIndexRec i j tbl' ((e,j)::rest)
		     else updateIndexRec i j tbl' ((e,k)::rest)
  in 
  let updateIndex i j = table := updateIndexRec i j !table [] in
  let updateTable (a,b) = 
    let idxa = List.assoc a !table in
    let idxb = List.assoc b !table in
    let min, max = min idxa idxb, max idxa idxb in
    updateIndex max min 
  in 
  List.iter updateTable eql;
  List.filter (fun ls -> ls <> []) (List.map gatherElemIndex numL);;

let rec findClass clsL e = match clsL with
  | [] -> []
  | ls::clsL' -> if List.mem e ls then ls else findClass clsL' e;;

let cut_string (sym: char) str =
  (* sym is a separator *)
  let str' = str ^ (String.make 1 sym) in (* put sentinel *)
  let len = String.length str' in
  let _res = ref [] in
  let _pos = ref 0 in
  for i = 0 to len - 1 do
    if String.get str' i = sym then
      begin
        _res := (String.sub str' !_pos (i - !_pos)) :: !_res;
        _pos := i + 1;
      end
    else ()
  done;
  List.rev !_res
;;

let cut_string2 (sym: string) str =
  let max = String.length str in
  let isMatchIndex curIdx =
    if max < curIdx + (String.length sym) then false
    else String.sub str curIdx (String.length sym) = sym
  in
  let rec findNextMatchIndex curIdx =
    match max < curIdx + (String.length sym), isMatchIndex curIdx with
    | true,_ -> None
    | _,true -> Some curIdx
    | _,_ -> findNextMatchIndex (curIdx+1)
  in
  let rec aux res curIdx =
    match findNextMatchIndex curIdx with
    | None -> res @ [String.sub str curIdx (max-curIdx)]
    | Some nextIdx ->
       aux (res @ [String.sub str curIdx (nextIdx-curIdx)]) (nextIdx+(String.length sym))
  in
  aux [] 0
;;      
  
(* Simple Equality Check *)
(* simpleEqCheck [(a,b);(b,c);(c,d)] (a,d) checks a=b,b=c,c=d |= a=d *)
let simpleEqCheck eqs eq =
  let replace sub e3 =
    let (e1,e2) = sub in
    if e1 = e3 then e2 else e3
  in
  let update sub (e1,e2) = (replace sub e1, replace sub e2) in
  let rec aux eqs0 =
    match eqs0 with
    | [] -> false
    | [(e1,e2)] when e1 = e2 -> true
    | (e1,e2)::eqs1 ->
       let eqs1' = List.map (update (e1,e2)) eqs1 in
       aux eqs1'
  in
  aux (eqs @ [eq])
;;  

let genExp n =
  let rec aux res k = 
    match k with
    | 0 -> res
    | _ ->
       let res0 = List.map (fun l -> false::l) res in
       let res1 = List.map (fun l -> true::l) res in
       aux (res1@res0) (k-1)
  in
  aux [[]] n
;;

(* updateList [("x",1);("y",2)] "y" 5 returns [("x",1);("y",5)] *)
(* updateList [("x",1);("z",2)] "y" 5 returns [("x",1);("z",2);("y",5)] *)
let updateListFlag ls x u =
  let _updateflag = ref false in  
  let rec aux res ls0 =
    match ls0 with
    | [] ->
       _updateflag := true;
       List.rev_append res [(x,u)]
    | (y,v)::ls1 when x = y && v = u ->
       List.rev_append res ((y,v)::ls1)
    | (y,v)::ls1 when x = y  ->
       _updateflag := true;       
       List.rev_append res ((x,u)::ls1)
    | hd::ls1 -> aux (hd::res) ls1
  in
  (aux [] ls,!_updateflag)
;;

let updateList ls x u = fst (updateListFlag ls x u)
;;

(* updateList_strict [("x",1);("y",2)] "y" 5 returns [("x",1);("y",5)] *)
(* updateList_strict [("x",1);("z",2)] "y" 5 fails *)
let updateList_strict ls x u =
  let rec aux res ls0 =
    match ls0 with
    | [] -> raise Not_found
    | (y,_)::ls1 when x = y -> List.rev_append res ((x,u)::ls1)
    | hd::ls1 -> aux (hd::res) ls1
  in
  aux [] ls
;;       

(* updateList3 [("x",1,u);("y",2,v)] "y" 5 w returns [("x",1,u);("y",5,w)] *)
(* updateList3 [("x",1,u);("z",2,v)] "y" 5 w returns [("x",1,u);("z",2,v);("y",5,w)] *)
let updateList3 ls x u1 u2 =
  let rec aux res ls0 =
    match ls0 with
    | [] -> List.rev_append res [(x,u1,u2)]
    | (y,_,_)::ls1 when x = y -> List.rev_append res ((x,u1,u2)::ls1)
    | hd::ls1 -> aux (hd::res) ls1
  in
  aux [] ls
;;

(* updateList_strict [("x",1);("y",2)] "y" 5 returns [("x",1);("y",5)] *)
(* updateList_strict [("x",1);("z",2)] "y" 5 fails *)
let updateList3_strict ls x u1 u2 =
  let rec aux res ls0 =
    match ls0 with
    | [] -> raise Not_found
    | (y,_,_)::ls1 when x = y -> List.rev_append res ((x,u1,u2)::ls1)
    | hd::ls1 -> aux (hd::res) ls1
  in
  aux [] ls
;;       


(* updateListOrder [("x",1);("y",2)] "y" 5 returns [("x",1);("y",5)] *)
(* updateListOrder [("x",1);("z",2)] "y" 5 returns [("x",1);("y",5);("z",2)] *)
let updateListOrderFlag order ls x u =
  let _updateflag = ref false in
  let rec aux res ls0 =
    match ls0 with
    | [] ->
       _updateflag := true;
       List.rev_append res [(x,u)]
    | (y,v)::ls1 when order x y > 0 -> aux ((y,v)::res) ls1
    | (y,v)::ls1 when order x y < 0 ->
       _updateflag := true;
       List.rev_append ((y,v)::(x,u)::res) ls1
    | (_,v)::ls1 when u<>v ->
       _updateflag := true;         
       List.rev_append ((x,u)::res) ls1
    | (_,v)::ls1 ->
       List.rev_append ((x,u)::res) ls1
  in
  (aux [] ls,!_updateflag)
;;       

let updateListOrder order ls x u = fst (updateListOrderFlag order ls x u)
;;       


(* list_assoc3 [(n0,a0,b0);(n1,a1,b1);(n2,a2,b2)] n2 is (a2,b2) *)
let rec list_assoc3 key ls =
  match ls with
  | [] -> raise Not_found
  | (k,a,b)::ls1 when k = key -> (a,b)
  | c :: ls1 -> list_assoc3 key ls1
;;  
let rec list_assoc_compare compare key ls =
  match ls with
  | [] -> raise Not_found
  | (k,a)::ls1 when compare k key = 0 -> a
  | c :: ls1 -> list_assoc_compare compare key ls1
;;
let list_assoc_compare_opt compare key ls =
  try Some (list_assoc_compare compare key ls)
  with
    Not_found -> None
;;
let rec list_mem_assoc_compare compare key ls =
  match ls with
  | [] -> false
  | (k,a)::ls1 when compare k key = 0 -> true
  | c :: ls1 -> list_mem_assoc_compare compare key ls1
;;
let mapAppend_rev f xx = L.fold_left (fun ss x -> List.rev_append (f x) ss) [] xx

let mapAppend f xx = L.rev (mapAppend_rev f xx)

module List_tailrec = struct

  (* fold_int f base 3 = f (f (f base 0) 1) 2 *)
  let fold_int (f: 'a -> int -> 'a) xx m = List.fold_left f xx (genLst m)

  (* fold_int2 f base 1 2 = f (f (f base 0 0) 0 1) 0 2 *)
  let fold_int2 (f: 'a -> int -> int -> 'a) xx m n =
    let mLst = genLst m in
    let nLst = genLst n in
    List.fold_left
      (fun yy i ->
        List.fold_left
          (fun zz j -> f zz i j)
          yy
          nLst
      )
      xx
      mLst
  
  let rec rev1 res ls =
    match ls with
    | [] -> res
    | x::ls' -> rev1 (x::res) ls'

  let rev ls = rev1 [] ls 

  let rec append_rev ls1 ls2 = 
    match ls1 with 
    | [] -> ls2
    | x::ls1 -> append_rev ls1 (x::ls2)

  let append ls1 ls2 = 
    let ls1rev = rev ls1 in
    append_rev ls1rev ls2

  let rec map_rev1 f ls result =
    match ls with
    | [] -> result
    | x::xl -> map_rev1 f xl ((f x)::result)

  let map_rev f ls = map_rev1 f ls []

  let map f ls = rev (map_rev f ls)

  let map2 f ls1 ls2 = List.fold_left (fun ls x -> List.fold_left (fun lsX y -> (f x y)::lsX) ls ls2) [] ls1

  let map_state (f: 'state -> 'a -> 'state * 'a) stat aa =
    let rec aux stat res aa =
      match aa with
      | [] -> (stat,rev res)
      | a::aa1 ->
         let (stat1,a1) = f stat a in
         aux stat1 (a1::res) aa1
    in
    aux stat [] aa

  let rec concat_rev1 res ll =
    match ll with
    | [] -> res
    | hdL::ll' ->
       let res' = append_rev hdL res in
       concat_rev1 res' ll'

  let concat_rev ll = concat_rev1 [] ll

  let concat ll = rev (concat_rev ll)

  (* allChoice [[1;2];[3;4];[5;6]] returns *)
  (* [1;3;5];[1;3;6];[1;4;5];[1;4;6]	*)
  (* [2;3;5];[2;3;6];[2;4;5];[2;4;6]	*)
  let rec allChoice1 resll ll =
    match ll with
    | [] -> map rev resll
    | hdL::ll' ->
       let resll' = concat (map (fun i -> map (fun rl -> i::rl) resll) hdL) in
       allChoice1 resll' ll'

  let allChoice ll = allChoice1 [[]] ll


  let rec allChoiceBool1 res ll =
    match ll with
    | [] -> map (fun (b,l) -> (b,rev l)) res
    | (ls1,ls2)::ll' ->
       let res1 = concat (map_rev (fun x-> (map_rev (fun (b,l) -> (b,x::l)) res)) ls1) in
       let res2 = concat (map (fun x-> (map (fun (b,l) -> (true,x::l)) res)) ls2) in
       let res' = append_rev res1 res2 in
       allChoiceBool1 res' ll'

  let allChoiceBool ll = allChoiceBool1 [(false,[])] ll

  (* allChoiceTwo [([1;2],[3;4]);([5;6],[7;8])] returns lists	*)
  (* similar to the result of allChoice [[1;2;3;4];[5;6;7;8]],	*)
  (* except for the choices from [1;2] and [5;6]			*)
  (* That is, it returns						*)
  (* [1;7];[1;8];[2;7];[2;8];					*)
  (* [3;5];[3;6];[3;7];[3;8];[4;5];[4;6];[4;7];[4;8];		*)
  let allChoiceTwo ll =
    let llb = allChoiceBool ll in
    List.fold_left (fun xll (b,l) -> if b then l::xll else xll) [] llb;;

  (* dropsame order ls1 ls2 returns a sublist of ls1, which is obtained by dropping the elements in ls2 *)
  (* ls1 and ls2 are assumed to be sorted w.r.t. order *)
  let rec dropsame1 order res ls1 ls2 = match ls1,ls2 with
	| [],_ -> rev res
	| a::ls1',b::ls2' ->
	   if order a b < 0 then dropsame1 order (a::res) ls1' ls2
	   else if order a b = 0 then dropsame1 order res ls1' ls2
	   else dropsame1 order res ls1 ls2'
	| _,[] -> append_rev res ls1

  let dropsame order ls1 ls2 = dropsame1 order [] ls1 ls2

  let takeNth ls i = 
    let rec takeNthRec res lst pos =
      if lst = [] then failwith "takeNth" else 
        let hd = List.hd lst in
        let tl = List.tl lst in
        match pos with
        | 0 -> (hd, List.rev_append res tl)
        | _ -> takeNthRec (hd::res) tl (pos-1)
    in takeNthRec [] ls i

  let splitNth ls pos =
    let rec aux res ls j =
      match ls,j<pos with
      | [],_ -> (List.rev res,[],[])
      | x::xl,true -> aux (x::res) xl (j+1)
      | x::xl,_ -> (List.rev res,[x],xl)
    in
    aux [] ls 0
    
  let dropNth ls i = let (_,res) = takeNth ls i in res

  let replaceNth ls i a =
    let rec replaceNthRec res lst pos =
      if lst = [] then failwith "replaceNth" else
        let hd = List.hd lst in
        let tl = List.tl lst in
        match pos with
        | 0 -> List.rev_append res (a::tl)
        | _ -> replaceNthRec (hd::res) tl (pos-1)
    in replaceNthRec [] ls i 
     
  let rec allChoiceApply1 f chkfunc ll res = match ll with
    | [] -> f(List.rev res)
    | ls::ll' ->
       for i = 1 to List.length ls do
         try
	       allChoiceApply1 f chkfunc ll' (chkfunc ((List.nth ls (i-1))::res))
         with Skip -> ()
       done

  let allChoiceApply f chkfunc ll = allChoiceApply1 f chkfunc ll []

  let permApply f ls =
    let rec permApplyRec res len lst =
      if len = 0 then f res
      else
        for i = 0 to len - 1 do
	      let (x,lst') = takeNth lst i in
	      permApplyRec (x::res) (len-1) lst'
        done
    in
    permApplyRec [] (List.length ls) ls

  let permApply2 f ls1 ls2 =
    permApply (fun ls -> permApply (f ls) ls2) ls1

  (* permApplyL f lls makes all possible permutations of	*)
  (* the lists of lls then apply f to it			*)
  (* e.g. permApplyL f [[1;2];[3;4]] performs		*)
  (* f [[1;2];[3;4]]					*)
  (* f [[1;2];[4;3]]					*)
  (* f [[2;1];[3;4]]					*)
  (* f [[2;1];[4;3]]					*)
  let permApplyL f ll =
    let rec permApplyR rest restl ls lls =
      match ls,lls with
      | [],[] -> f (List.rev ((List.rev rest)::restl))
      | [],ls1::lls1 -> permApplyR [] ((List.rev rest)::restl) ls1 lls1
      | _,_ ->
         for i = 0 to List.length ls - 1 do
	       let (a,ls') = takeNth ls i in
	       permApplyR (a::rest) restl ls' lls
         done
    in
    match ll with
    | [] -> f []
    | ls1::ll1 -> permApplyR [] [] ls1 ll1

  let splitLst filter ls =
    let rec aux lsT lsF ls1 =
      match ls1 with
      | [] -> (List.rev lsT,List.rev lsF)
      | x::ls2 when filter x -> aux (x::lsT) lsF ls2
      | x::ls2 -> aux lsT (x::lsF) ls2
    in
    aux [] [] ls

  (* merge of two assoc lists *)
  let merge (f: 'b -> 'b -> 'b) (assoc1 : ('a * 'b) list) (assoc2 : ('a * 'b) list) : ('a * 'b) list =
    let rec aux res keys =
      match keys with
      | [] -> List.rev res
      | k::keys1 ->
         match List.assoc_opt k assoc1, List.assoc_opt k assoc2 with
         | None,Some x -> aux ((k,x)::res) keys1
         | Some x,None -> aux ((k,x)::res) keys1
         | Some x,Some y -> aux ((k,f x y)::res) keys1
         | None,None -> failwith "List_tailrec.merge"
    in
    let keys1 = List.map fst assoc1 in
    let keys2 = List.map fst assoc2 in
    aux [] (union keys1 keys2)

  (* zip two assoc-list: [(1,a);(2,b)] [(2,c);(3,d)] --> [(1,(a))] *)
  let zip_assoc none assoc1 assoc2 =
    let rec aux res keys =
      match keys with
      | [] -> List.rev res
      | k::keys1 ->
         match List.assoc_opt k assoc1, List.assoc_opt k assoc2 with
         | None,Some x -> aux ((k,(none,x))::res) keys1
         | Some x,None -> aux ((k,(x,none))::res) keys1
         | Some x,Some y -> aux ((k,(x,y))::res) keys1
         | None,None -> failwith "List_tailrec.zip_assoc"
    in
    let keys1 = List.map fst assoc1 in
    let keys2 = List.map fst assoc2 in
    aux [] (union keys1 keys2)

  let cut_by_cond cond ls =
    let rec aux res cur ls =
      match ls with
      | [] when cur = [] -> List.rev res
      | [] -> List.rev ((List.rev cur)::res)
      | x::xl when cond x -> aux ((List.rev cur)::res) [] xl
      | x::xl -> aux res (x::cur) xl
    in
    aux [] [] ls
    
end
;;

(* File reader *)
(*
let my_read_file filename =
  let x = ref "" in
  let ic = open_in filename in
  try
	while true do
	  x := !x ^ (input_line ic) ^ "\n"
	done ;
	"" (* dummy *)
  with End_of_file -> close_in ic;!x
;;
 *)

module List_mes = struct

  let hd mes ls =
    try
      List.hd ls
    with
      _ ->
      Fmt.printf "@[%s@." mes;
      failwith "List_mes.hd"

  let tl mes ls =
    try
      List.tl ls
    with
      _ ->
      Fmt.printf "@[%s@." mes;
      failwith "List_mes.tl"
      
  let nth mes ls n =
    try
      List.nth ls n
    with
      _ ->
      Fmt.printf "@[%s@." mes;
      failwith "List_mes.nth"

  let nth' mes print_func ls n =
    try
      List.nth ls n
    with
      _ ->
      Fmt.printf "@[Exception from List_mes.nth'!!@.";
      Fmt.printf "@[Mes: %s@." mes;
      Fmt.printf "@[List: @." ;
      List.iter print_func ls;
      Fmt.printf "@[Nth: %d@." n;
      failwith "List_mes.nth"
      
  let assoc mes key ls =
    try
      List.assoc key ls
    with
      _ ->
      Fmt.printf "@[%s@." mes;
      failwith "List_mes.assoc"

  let assoc3 mes key ls =
    try
      list_assoc3 key ls
    with
      _ ->
      Fmt.printf "@[%s@." mes;
      failwith "List_mes.assoc3"             
      
end
;;

