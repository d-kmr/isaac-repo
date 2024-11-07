open Notations
open PrintTools
open Tools

exception NotPresburger
exception NotSanitary
(* 
This exception will be raised when the sanitary checker finds: 
ASSUMPTION: order over hat-variables names ("" is the special name)
    "" < "a" < "b" < .. < "#size"

hatName(t) 
-- ("",0) (if t does not contain hat-var) 
-- (<name>,0) (if t has only one hat-var named <name>)
-- (<name>,1) (if t has two hat-vars #size and <name>)
-- raise NotSanitary (otherwise)

(name1,flag1) < (name2,flag2) := name1 < name2 or (name1 = name2 && flag1 < flag2)

Comparing two terms with the following BAD situation
(1) BAD condition for t < u 
errHAT not (hatName(t) < hatName(u))
errQSN (x? in t && hatName(u) <> ("",0)) or (x? in u && hatName(t) <> ("",0))
errTLD (x@tilde in t && hatName(u) <> ("",0)) or (x@tilde in u && hatName(t) <> ("",0))

(2) BAD condition for t <= u 
errHAT not (hatName(t) <= hatName(u))
errQSN (x? in t && hatName(u) <> "") or (x? in u && hatName(t) <> "")
errTLD (x@tilde in t && hatName(u) <> "") or (x@tilde in u && hatName(t) <> "")

(3) BAD condition for t = u 
errHAT not (hatName(t) = hatName(u))
errQSN (x? in t && hatName(u) <> "") or (x? in u && hatName(t) <> "")
errTLD (x@tilde in t && hatName(u) <> "") or (x@tilde in u && hatName(t) <> "")
*)

(* Simplification flag *)
(* syntactical simplification of formulas flag (default:true) *)
let simplFlag = ref true
let unset_simpl () = simplFlag := false
                       
(*----------------------------------*)
(* Terms of Symbolic Heap			*)
(*----------------------------------*)
module Attr = struct
  (* From vcpBase
    type attr = PTR | STRUCT of string | EXQ | ARRAY of int list | PARAM | PTRPTR | GLOBAL | HAT | BAR | EXTERN | PROTO | TILDE | CHECK | DOT
    Attributions kept in SHterm-data are 
    - types: "ptr", "$<name>", "arr" ("$<name>" is "struct <name>")
    - sorts: "hat", "bar", "tilde", "check", "dot" *)
  type t =
    | PTR | STRUCT of string | EXQ | ARRAY of int list | PARAM | PTRPTR | GLOBAL | SIMPLE of int
    | HAT | BAR | EXTERN | PROTO | FUNC | TILDE | CHECK | DOT | QUESTION | ACUTE | INDIRECT
    | TEMP | PHANTOM | OFFSET of string * string

  let to_int a =
    match a with
    | PTR -> 0
    | STRUCT _ -> 1
    | EXQ -> 2
    | ARRAY _ -> 3
    | PARAM -> 4
    | PTRPTR -> 5
    | GLOBAL -> 6
    | SIMPLE _ -> 7
    | HAT -> 8
    | BAR -> 9
    | EXTERN -> 10
    | PROTO -> 11
    | FUNC -> 12
    | TILDE -> 13
    | CHECK -> 14
    | DOT -> 15
    | QUESTION -> 17
    | ACUTE -> 19
    | INDIRECT -> 20
    | TEMP -> 21
    | PHANTOM -> 22
    | OFFSET _ -> 23
               
  let compare a1 a2 =
    match a1, a2 with
    | _,_ when to_int a1 > to_int a2 -> 1
    | _,_ when to_int a1 < to_int a2 -> -1
    | STRUCT s1,STRUCT s2 -> String.compare s1 s2
    | SIMPLE n1,SIMPLE n2 -> compare n1 n2
    | _,_ -> 0

  let pp fmt a =
    match a with
    | PTR -> () (* Format.fprintf fmt "@PTR" *)
    | STRUCT sname -> () (* Format.fprintf fmt "@STRUCT %s" sname *)
    | EXQ -> () (* Format.fprintf fmt "EXQ" *)
    | ARRAY nn -> () (* Format.fprintf fmt "@ARRAY[%a]" (pp_list_comma Format.pp_print_int) nn *)
    | PARAM -> () (* Format.fprintf fmt "@PARAM" *)
    | PTRPTR -> () (* Format.fprintf fmt "@PTRPTR" *)
    | GLOBAL -> () (* Format.fprintf fmt "@GLOBAL" *)
    | HAT -> Format.fprintf fmt "@HAT"
    | BAR -> Format.fprintf fmt "@BAR"
    | EXTERN -> Format.fprintf fmt "@EXTERN"
    | PROTO -> Format.fprintf fmt "@PROTO"
    | FUNC -> Format.fprintf fmt "@FUNC"
    | TILDE -> Format.fprintf fmt "@TILDE"
    | CHECK -> Format.fprintf fmt "@CHECK"
    | DOT -> Format.fprintf fmt "@DOT"
    | QUESTION -> Format.fprintf fmt "@QUESTION"
    | ACUTE -> Format.fprintf fmt "@AQUTE"
    | SIMPLE n -> () (* Format.fprintf fmt "@SIMPLE(%d)" n *)
    | INDIRECT -> Format.fprintf fmt "@INDIRECT"
    | TEMP -> Format.fprintf fmt "@TEMP"
    | PHANTOM -> Format.fprintf fmt "@PHANTOM"
    | OFFSET _ -> Format.fprintf fmt "@OFFSET"
            
  let isPTR a = to_int a = 0

  let isSTRUCT a = to_int a = 1

  let isARRAY a = to_int a = 3

  let isHAT a = to_int a = 8

  let isOFFSET a = to_int a = 23
              
  let getARRAYinfo a =
    match a with
    | ARRAY nn -> nn
    | _ -> []
         
  let getSIMPLEinfo a =
    match a with
    | SIMPLE n -> [n]
    | _ -> []

  let getSTRUCTinfo a =
    match a with
    | STRUCT sname -> [sname]
    | _ -> []

  let getOFFSETinfo a =
    match a with
    | OFFSET (strName,fld) -> [(strName,fld)]
    | _ -> []
         
end
            
module Attrs = struct
  include Set.Make(Attr)
  let mapUnion f xx = List.fold_left (fun s x -> union s (f x)) empty xx
                    
  let disjoint aa1 aa2 = is_empty (inter aa1 aa2)

  let pp fmt aa = pp_list_nospace Attr.pp fmt (elements aa)
                
  let hasPTR aa = exists Attr.isPTR aa
                
  let hasARRAY aa = exists Attr.isARRAY aa

  let hasSTRUCT aa = exists Attr.isSTRUCT aa

  let hasHAT aa = exists Attr.isHAT aa

  let hasOFFSET aa = exists Attr.isOFFSET aa
                   
  let getSTRUCTinfo aa = fold (fun a snameL -> List.rev_append (Attr.getSTRUCTinfo a) snameL) aa []

  let getSIMPLEinfo aa = fold (fun a nn -> List.rev_append (Attr.getSIMPLEinfo a) nn) aa []

  let getOFFSETinfo aa = fold (fun a nn -> List.rev_append (Attr.getOFFSETinfo a) nn) aa []

  let oneHAT = singleton (Attr.HAT)
             
  let oneSTRUCT sname = singleton (Attr.STRUCT sname)

  let onePROTO = singleton (Attr.PROTO)

  let oneARRAY nn = singleton (Attr.ARRAY nn)               
end

module SHterm = struct
  (* Term expressions *)
  (* 't' is used for them *)
  (* 'tt' is used for a list of them *)
  type t =
    | Var of string * Attrs.t (* Var(x,{hat;ptr}) *)
    | Int of int
    | PosInf
    | NegInf
    | Add of t list
    | Sub of t list (* left-assoc minus *)
    | Mul of t * t
    | Div of t * t
    | Mod of t * t
    | Shr of t * t
    | Shl of t * t
    | Band of t * t
    | Bor of t * t
    | Bxor of t * t
    | Bnot of t
    | Fcall of string * t list (* function call *)

  let rec pp fmt t =
    match t with
    | Var(v,attrs) when attrs = Attrs.empty -> Format.fprintf fmt "%s" v
    | Var(v,attrs) -> Format.fprintf fmt "%s%a" v Attrs.pp attrs
    | Int n -> if n >= 0 then Format.fprintf fmt "%d" n else Format.fprintf fmt "(%d)" n
    | PosInf -> Format.fprintf fmt "PosInf"
    | NegInf -> Format.fprintf fmt "NegInf"
    | Add tt -> Format.fprintf fmt "%a" (pp_list "ERROR" "+" pp1) tt
    | Sub tt -> Format.fprintf fmt "%a" (pp_list "ERROR" "-" pp1) tt
    | Mul(t1,t2) -> Format.fprintf fmt "%a*%a" pp1 t1 pp1 t2
    | Div(t1,t2) -> Format.fprintf fmt "%a/%a" pp1 t1 pp1 t2
    | Mod(t1,t2) -> Format.fprintf fmt "%a %% %a" pp1 t1 pp1 t2
    | Shr(t1,t2) -> Format.fprintf fmt "%a>>%a" pp1 t1 pp1 t2
    | Shl(t1,t2) -> Format.fprintf fmt "%a<<%a" pp1 t1 pp1 t2
    | Band(t1,t2) -> Format.fprintf fmt "%a band %a" pp1 t1 pp1 t2
    | Bor(t1,t2) -> Format.fprintf fmt "%a bor %a" pp1 t1 pp1 t2
    | Bxor(t1,t2) -> Format.fprintf fmt "%a bxor %a" pp1 t1 pp1 t2
    | Bnot t1 -> Format.fprintf fmt "~%a" pp1 t1
    | Fcall(g,tt) -> Format.fprintf fmt "%s(%a)" g (pp_list_comma pp) tt
  and pp1 fmt t =
    match t with
    | Var _ | Int _ | Mul(_,_) | Mod(_,_) -> Format.fprintf fmt "%a" pp t
    | _ -> Format.fprintf fmt "(%a)" pp t
         
  let rec pp_data fmt t =
    match t with
    | Var(v,attrs) -> Format.fprintf fmt "Var(%s,[%a])" v Attrs.pp attrs
    | Int n -> Format.fprintf fmt "Int(%d)" n
    | PosInf -> Format.fprintf fmt "PosInf"
    | NegInf -> Format.fprintf fmt "NegInf"
    | Add tt -> Format.fprintf fmt "Add [%a]" (pp_list "ERROR" "+" pp_data) tt
    | Sub tt -> Format.fprintf fmt "Sub [%a]" (pp_list "ERROR" "-" pp_data) tt
    | Mul(t1,t2) -> Format.fprintf fmt "Mul(%a,%a)" pp_data t1 pp_data t2
    | Div(t1,t2) -> Format.fprintf fmt "Div(%a,%a)" pp_data t1 pp_data t2
    | Mod(t1,t2) -> Format.fprintf fmt "Mod(%a,%a)" pp_data t1 pp_data t2
    | Shr(t1,t2) -> Format.fprintf fmt "Shr(%a,%a)" pp_data t1 pp_data t2
    | Shl(t1,t2) -> Format.fprintf fmt "Shl(%a,%a)" pp_data t1 pp_data t2
    | Band(t1,t2) -> Format.fprintf fmt "Band(%a,%a)" pp_data t1 pp_data t2
    | Bor(t1,t2) -> Format.fprintf fmt "Bor(%a,%a)" pp_data t1 pp_data t2
    | Bxor(t1,t2) -> Format.fprintf fmt "Bxor(%a,%a)" pp_data t1 pp_data t2
    | Bnot t1 -> Format.fprintf fmt "Bnot %a" pp_data t1
    | Fcall(g,tt) -> Format.fprintf fmt "Fcall(%s,%a)" g (pp_list_comma pp_data) tt
                  
  let print = Format.printf "@[%a@]" pp

  let println = Format.printf "@[%a@." pp
              
  let plusOne t =
    match t with
    | Int n -> Int (n+1)
    | PosInf -> PosInf
    | NegInf -> NegInf
    | Add [t1;Int n] -> Add [t1;Int (n+1)]
    | Sub [t1;Int 1] -> t1
    | Sub [t1;Int n] -> Sub [t1;Int (n-1)]
    | _ -> Add [t;Int 1]

  let minusOne t =
    match t with
    | Int n -> Int (n-1)
    | PosInf -> PosInf
    | NegInf -> NegInf
    | Add [t1;Int 1] -> t1
    | Add [t1;Int n] -> Add [t1;Int (n-1)]
    | Sub [t1;Int n] -> Sub [t1;Int (n-1)]
    | _ -> Sub [t;Int 1]

  let isInf t = t = PosInf || t = NegInf

  let rec getConsts t =
    match t with
    | Var _ -> Intset.empty
    | Int n -> Intset.singleton n
    | PosInf -> Intset.empty
    | NegInf -> Intset.empty
    | Add tt -> getConstsL tt
    | Sub tt -> getConstsL tt
    | Mul(t1,t2) -> getConstsL [t1;t2]
    | Div(t1,t2) -> getConstsL [t1;t2]
    | Mod(t1,t2) -> getConstsL [t1;t2]
    | Shr(t1,t2) -> getConstsL [t1;t2]
    | Shl(t1,t2) -> getConstsL [t1;t2]
    | Band(t1,t2) -> getConstsL [t1;t2]
    | Bor(t1,t2) -> getConstsL [t1;t2]
    | Bxor(t1,t2) -> getConstsL [t1;t2]
    | Bnot t1 -> getConsts t1
    | Fcall(g,tt) -> getConstsL tt
    and getConstsL tt = Intset.mapUnion getConsts tt
    
  let rec isConst t =
    match t with
    | Int _ | PosInf | NegInf -> true
    | Add tt | Sub tt -> List.for_all isConst tt
    | Mul(t1,t2) | Div(t1,t2) | Mod(t1,t2) | Shr(t1,t2) | Shl(t1,t2) | Band(t1,t2) | Bor(t1,t2) | Bxor(t1,t2)
      -> isConst t1 && isConst t2
    | Bnot t1 -> isConst t1
    | _ -> false

  let rec isIntConst t =
    match t with
    | Int _ -> true
    | Add tt | Sub tt -> List.for_all isIntConst tt
    | Mul(t1,t2) | Div(t1,t2) | Mod(t1,t2) -> isIntConst t1 && isIntConst t2
    | _ -> false
         
  let rec evalConst t =
    match t with
    | _ when not(isConst t) -> failwith "evalConst : non-constant"
    | Int n -> n
    | PosInf -> failwith "evalConst: PosInf"
    | NegInf -> failwith "evalConst: NegInf"
    | Add tt ->
       let nn = List.map evalConst tt in
       List.fold_right ( + ) nn 0
    | Sub tt -> 
       let nn = List.map evalConst tt in
       if nn = [] then 0 else 
       List.fold_left ( - ) (List.hd nn) (List.tl nn)
    | Mul(t1,t2) ->
       let n1,n2 = evalConst t1, evalConst t2 in
       n1 * n2
    | Div(t1,t2) ->
       let n1,n2 = evalConst t1, evalConst t2 in
       n1 / n2
    | Mod(t1,t2) -> 
       let n1,n2 = evalConst t1, evalConst t2 in
       n1 mod n2
    | Shr(t1,t2) ->
       let n1,n2 = evalConst t1, evalConst t2 in
       n1 lsr n2
    | Shl(t1,t2) -> 
       let n1,n2 = evalConst t1, evalConst t2 in
       n1 lsl n2
    | Band(t1,t2) -> 
       let n1,n2 = evalConst t1, evalConst t2 in
       n1 land n2
    | Bor(t1,t2) -> 
       let n1,n2 = evalConst t1, evalConst t2 in
       n1 lor n2
    | Bxor(t1,t2) ->
       let n1,n2 = evalConst t1, evalConst t2 in
       n1 lxor n2
    | Bnot t1 ->
       let n1 = evalConst t1 in
       lnot n1
    | _ -> failwith "evalConst : never occur"

  let rec isPb t =
    match t with
    | Var _ | Int _ | PosInf | NegInf
      -> true
    | Add tt | Sub tt
      -> List.for_all isPb tt
    | Mul (t1,t2)
      -> (isConst t1 && isPb t2) || (isConst t2 && isPb t1)
    | Div (t1,t2) | Mod (t1,t2) | Shr (t1,t2) | Shl (t1,t2)
      -> isPb t1 && isConst t2
    | Band (t1,t2) | Bor (t1,t2) | Bxor (t1,t2)
      -> (isConst t1 && isPb t2) || (isConst t2 && isPb t1)
    | Bnot t1
      -> isPb t1
    | Fcall _
      -> false

  let checkPresburger t = if isPb t then () else raise NotPresburger
      
  let hom f t =
    match t with
    | Add tt -> Add (List.map f tt)
    | Sub tt -> Sub (List.map f tt)
    | Mod (t1,t2) -> Mod(f t1,f t2)
    | Mul (t1,t2) -> Mul(f t1,f t2)
    | Div (t1,t2) -> Div(f t1,f t2)
    | Shr (t1,t2) -> Shr(f t1,f t2)
    | Shl (t1,t2) -> Shl(f t1,f t2)
    | Band (t1,t2) -> Band(f t1,f t2)
    | Bor (t1,t2) -> Bor(f t1,f t2)
    | Bxor (t1,t2) -> Bxor(f t1,f t2)
    | Bnot t1 -> Bnot (f t1)
    | Fcall (g,tt) -> Fcall (g,List.map f tt)
    | _ -> t
         
  let rec fv t =
    match t with
    | Var (v,_) -> Strset.singleton v
    | Int _ | PosInf | NegInf -> Strset.empty
    | Add tt | Sub tt | Fcall (_,tt) -> List.fold_left (fun s t -> Strset.union (fv t) s) Strset.empty tt
    | Mul(t1,t2) | Div(t1,t2) | Mod(t1,t2)| Shr(t1,t2) | Shl(t1,t2) | Band(t1,t2) | Bor(t1,t2) | Bxor(t1,t2)
      -> Strset.union (fv t1) (fv t2)
    | Bnot t1 -> fv t1
                               
  let getVarName t : Strset.t =
    match t with
    | Var (v,_) -> Strset.singleton v
    | _ -> Strset.empty
               
  (* About attributions *)
  let rec getAttrs t =
    match t with
    | Var (_,attrs) -> attrs
    | Add tt | Sub tt | Fcall (_,tt)
      -> Attrs.mapUnion getAttrs tt
    | Mul(t1,t2) | Div (t1,t2) | Mod (t1,t2) | Shr (t1,t2) | Shl (t1,t2) | Band (t1,t2) | Bor (t1,t2) | Bxor (t1,t2)
      -> Attrs.mapUnion getAttrs [t1;t2]
    | Bnot t1 -> getAttrs t1
    | _ -> Attrs.empty

  let isVarWithAttr t a = (* t is a variable of attribution a *)
    match t with 
    | Var (x,attrs) ->  Attrs.mem a attrs
    | _ -> false

  let isVarWithName t name = (* t is a variable of name v *)
    match t with
    | Var (v,_) when v = name -> true
    | _ -> false

  let isHatVar t = isVarWithAttr t Attr.HAT

  (* it checks hat-vars except #size@hat *)
  let isHatVar' t = (isHatVar t) && not(isVarWithName t "#size")

  let isDotVar t = isVarWithAttr t Attr.DOT
                 
  let isTildeVar t = isVarWithAttr t Attr.TILDE
                   
  let isBarVar t = isVarWithAttr t Attr.BAR
                 
  let isCheckVar t = isVarWithAttr t Attr.CHECK
                   
  let isBCDTVar t = (isBarVar t) || (isCheckVar t) || (isDotVar t) || (isTildeVar t)

  let isHCDTVar t = (isHatVar t) || (isCheckVar t) || (isDotVar t) || (isTildeVar t)
                  
  let isSignVar t = (isBarVar t) || (isCheckVar t) || (isDotVar t) || (isTildeVar t) || (isHatVar t)

  let isIndirectVar t = isVarWithAttr t Attr.INDIRECT

  let isPhantomVar t = isVarWithAttr t Attr.PHANTOM

  let hasGlobal t = isVarWithAttr t Attr.GLOBAL
                      
  let isLocalHat t = isHatVar t && not (hasGlobal t)

  let isNotLocalHat t = not (isLocalHat t)
                      
  let toAbstract t = 
    match t with
    | Var (v,_) when isHatVar' t -> (0,v,[],[])
   (*
    | Var _ when isBarVar t -> (1,to_string t,[],[])
    | Var _ when isDotVar t -> (2,to_string t,[],[])
    | Var _ when isTildeVar t -> (3,to_string t,[],[])
    | Var _ when isCheckVar t -> (4,to_string t,[],[])
    | Var _ when isIndirectVar t -> (5,to_string t,[],[])
   *)
    | Var (v,_) -> (6,v,[],[])
    | Int n -> (10,string_of_int n,[],[])
    | Add tt -> (20,"",tt,[])
    | Sub tt -> (21,"",tt,[])
    | Mul(t,u) -> (22,"",[t;u],[])
    | Div(t,u) -> (23,"",[t;u],[])
    | Mod(t,u) -> (24,"",[t;u],[])
    | Shr(t,u) -> (25,"",[t;u],[])
    | Shl(t,u) -> (26,"",[t;u],[])
    | Band(t,u) -> (30,"",[t;u],[])
    | Bor(t,u) -> (31,"",[t;u],[])
    | Bxor(t,u) -> (32,"",[t;u],[])
    | Bnot t -> (33,"",[t],[])
    | Fcall(f,tt) -> (70,f,tt,[])
    | PosInf -> (80,"",[],[])
    | NegInf -> (81,"",[],[])
                      
  (* comparison function for terms *)
  let rec compare t u = genCompare toAbstract compare t u
  let compare_rev t u = (-1) * (compare t u)
    
  let rec getSIMPLEinfo t =
    match Attrs.getSIMPLEinfo (getAttrs t) with
    | [] -> []
    | n::_ -> [n]
                                               
  let getTypes t aa =
    match Attrs.hasARRAY aa, Attrs.hasPTR aa, Attrs.hasSTRUCT aa with
    | true,false,false -> ["arr"]
    | true,_,_ -> raiseStError (Format.asprintf "%a has an illegal type: ARRAY + PTR/STRUCT" pp t)
    | _,true,_ -> "ptr" :: (Attrs.getSTRUCTinfo aa)
    | _,false,_ -> Attrs.getSTRUCTinfo aa

  let getTypeInfo t = getTypes t (getAttrs t)

  let checkTypeInfo aa =
    let dummy = Int 0 in
    try
      let _ = getTypes dummy aa in true
    with
      _ -> false

  let rec getStructName t = Attrs.getSTRUCTinfo (getAttrs t)

  let rec getHeadTerm t =
    match t with
    | Var (_,_) -> [t]
    | Add (Var(v,_) ::tt) when v = "#size" -> getHeadTerm (Add tt)
    | Add (t1::_) 
      | Sub (t1::_) -> getHeadTerm t1
      | _ -> []

  (* Substitution on terms *)
  let rec varRepl (repl : (string* string) list) t =
    match t with
    | Var (v,attrs) ->
       begin
	     match findItemOption v repl with
	     | Some w -> Var (w,attrs)
	     | None -> t
       end
    | _ -> hom (varRepl repl) t

  let rec subst (sub : (string * t) list) t =
    match t,sub with
    | _,[] -> t
    | Var (x,attrs),_ ->
       begin
         try
	       List.assoc x sub
         with Not_found -> t
       end
    | _,_ -> hom (subst sub) t

  (* normalization until Add-normal form *)
  (* Add[t0;t1;..;tn] *)
  (* ti are not Add-form *)
  (* t0 is a HAT-var if a hat var exists *)
  (* t1 may be #size if it exists *)
  let nf t =
    let rec aux hh vv n oo tt = (* (hatvars,vars,num,others) *)
      match tt with
      | [] -> (hh,vv,n,oo)
      | (Var(x,aa) as v)::tt1 when x <> "#size" && Attrs.hasHAT aa -> aux (v::hh) vv n oo tt1
      | (Var(_,aa) as v)::tt1 when Attrs.hasHAT aa -> aux (hh@[v]) vv n oo tt1
      | (Var _ as v)::tt1 -> aux hh (v::vv) n oo tt1
      | (Int m)::tt1 -> aux hh vv (n+m) oo tt1
      | (Add tt)::tt1 -> aux hh vv n oo (tt1@tt)
      | (Sub [Int m])::tt1 -> aux hh vv (n-m) oo tt1
      | u::tt1 -> aux hh vv n (u::oo) tt1
    in
    let (hh,vv,n,oo) = aux [] [] 0 [] [t] in
    match List.mem PosInf oo, List.mem NegInf oo, hh@vv@[Int n]@oo with
    | true,_,_ -> PosInf
    | _,true,_ -> NegInf
    | _,_,[u] -> u
    | _,_,uu -> Add uu       

  let eq t1 t2 = (nf t1) = (nf t2)

  let evalUnderPmodel_op t =
    match t with
    | Mul(_,_) -> ( * )
    | Div(_,_) -> ( / )
    | Mod(_,_) -> (mod)
    | Shr (_,_) -> (lsl)
    | Shl (_,_) -> (lsr)
    | Band (_,_) -> (land)
    | Bor (_,_) -> (lor)
    | Bxor (_,_) -> (lxor)
    | _ -> failwith ""

  let rec evalUnderPmodel pmodel t : int =
    match t with
    | Var (v,_) -> (try List.assoc v pmodel with Not_found -> 0)
    | Int n -> n
    | PosInf -> max_int
    | NegInf -> min_int              
    | Add ts ->
	   let nn = List.map (evalUnderPmodel pmodel) ts in
	   List.fold_right (+) nn 0
    | Sub ts ->
	   let nn = List.map (evalUnderPmodel pmodel) ts in
	   begin
	     match nn with
	     | [] -> 0
	     | k::kk -> List.fold_left (-) k kk
	   end
    | Mul(t1,t2) | Div(t1,t2) | Mod(t1,t2) | Shr(t1,t2) | Shl(t1,t2) | Band(t1,t2) | Bor(t1,t2) | Bxor(t1,t2)
      -> let op = evalUnderPmodel_op t in
	     let n1 = evalUnderPmodel pmodel t1 in
         let n2 = evalUnderPmodel pmodel t2 in
         op n1 n2
    | Bnot t1 -> lnot (evalUnderPmodel pmodel t1)
    | Fcall (f,u::_) when f = "#IN" -> (* special case for indirect-handling *)
       evalUnderPmodel pmodel u
    | Fcall _ -> failwith "evalUnderPmodel: fun.call cannot be evaluated"
                
  let extract_nonPb vvv_eqlist t =
    let replace_term vvv_eqlist t =
      let (vvv,eqlist) = vvv_eqlist in
      Format.printf "@[%a (replace_term)@." pp t;
      List.iter (fun (t,s) -> Format.printf "@[(%a,%s)!@." pp t s) eqlist;
      match List.assoc_opt t eqlist with
      | Some v ->
         (vvv_eqlist,Var(v,Attrs.empty))
      | None ->
         let v = Strset.genFresh "##" vvv in
         let vvv1 = Strset.add v vvv in
         let eqlist1 = (t,v) :: eqlist in
         ((vvv1,eqlist1), Var(v,Attrs.empty))
    in
    let rec aux vvv_eqlist t =
      match t with
      | Var _ | Int _ -> (vvv_eqlist,t)
      | Add tt ->
         let (vvv_eqlist1,tt1) = List_tailrec.map_state aux vvv_eqlist tt in         
         (vvv_eqlist1, Add tt1)
      | Sub tt ->
         let (vvv_eqlist1,tt1) = List_tailrec.map_state aux vvv_eqlist tt in
         (vvv_eqlist1, Sub tt1)
      | Mul(t1,t2) ->
         begin
           match isConst t1, isConst t2 with
           | false,false -> replace_term vvv_eqlist t
           | _,_ ->
              let (vvv_eqlist1,t1') = aux vvv_eqlist  t1 in
              let (vvv_eqlist2,t2') = aux vvv_eqlist1 t2 in
              (vvv_eqlist2, Mul(t1',t2'))
         end
      | _ -> replace_term vvv_eqlist t
    in
    let (vvv,eqlist) = vvv_eqlist in
    let vvv1 = Strset.union (fv t) vvv in (* used vars *)
    aux (vvv1,eqlist) t
    
  (* Syntactical simplification *)
  (* - flatten Add: Add[Add[t1;u1];v1;Add[t2;u2]] -->  Add[t1;u1;v1;t2;u2] *)
  (* - normalize const add: Add[3;t;2] --> Add[t;5] *)
  let syntactical_simpl t =
    let rec flattenAddL u = 
      match u with
      | Add uu -> List.fold_left (fun tt t -> List.rev_append (flattenAddL t) tt) [] uu
      | Sub [u;Int n] -> (Int ((-1) * n)) :: (flattenAddL u)
      | _ -> [u]
    in
    let rec normlizeCadd n tt uu =
      match uu,tt,n with
      | [],[],_ -> Int n
      | [],[u],0 -> u
      | [],_,0 -> Add (List.sort compare tt)
      | [],_,_ -> Add ((List.sort compare tt) @ [Int n])
      | (Int m)::uu1,_,_ -> normlizeCadd (m+n) tt uu1
      | t::uu1,_,_ -> normlizeCadd n (t::tt) uu1
    in
    let tt1 = flattenAddL t in
    normlizeCadd 0 [] tt1

  (* just replacing #IN(u,x) --> u *)
  let rec unfold_indirect t =
    match t with
    | Var _ | Int _ | PosInf | NegInf -> t
    | Add tt ->
       let tt' = List.map unfold_indirect tt in
       Add tt'
    | Sub tt ->
       let tt' = List.map unfold_indirect tt in
       Sub tt'
    | Mul (t1,t2) ->
       let t1',t2' = unfold_indirect t1, unfold_indirect t2 in
       Mul (t1',t2')
    | Shr (t1,t2) ->
       let t1',t2' = unfold_indirect t1, unfold_indirect t2 in
       Shr (t1',t2')
    | Shl (t1,t2) ->
       let t1',t2' = unfold_indirect t1, unfold_indirect t2 in
       Shl (t1',t2')
    | Band (t1,t2) ->
       let t1',t2' = unfold_indirect t1, unfold_indirect t2 in
       Band (t1',t2')
    | Bor (t1,t2) ->
       let t1',t2' = unfold_indirect t1, unfold_indirect t2 in
       Bor (t1',t2')
    | Bxor (t1,t2) ->
       let t1',t2' = unfold_indirect t1, unfold_indirect t2 in
       Bxor (t1',t2')
    | Div (t1,t2) ->
       let t1',t2' = unfold_indirect t1, unfold_indirect t2 in
       Div (t1',t2')
    | Mod (t1,t2) ->
       let t1',t2' = unfold_indirect t1, unfold_indirect t2 in       
       Mod (t1',t2')
    | Bnot t1 ->
       let t1' = unfold_indirect t1 in
       Bnot t1'
    | Fcall (f,u::_) when f = "#IN" -> unfold_indirect u
    | Fcall (f,uu) ->
       let uu' = List.map unfold_indirect uu in
       Fcall (f,uu')
    
end
;;

(* Short cuts for SHterms *)
module T = SHterm;;
let var v attrs = T.Var (v,attrs);;
let num n = T.Int n;;
let zero = num 0;;
let one = num 1;;
let ( +.+ ) t1 t2 = T.Add [t1;t2];;
let ( -.- ) t1 t2 = T.Sub [t1;t2];;
let ( *.* ) t1 t2 = T.Mul(t1,t2);;
let ( %.% ) t n = T.Mod(t,n);;
let ( =.= ) t u = T.compare t u = 0;;
let ( <.> ) t u = T.compare t u <> 0;;

module Tset = struct
  include Set.Make(SHterm)

  let mapUnion f xx = List.fold_left (fun s x -> union s (f x)) empty xx

  let rec fv_t t =
    match t with
    | T.Var _ -> singleton t
    | T.Int _ | T.PosInf | T.NegInf -> empty
    | Add tt | Sub tt | Fcall (_,tt)
      -> mapUnion fv_t tt
    | Mul(t1,t2) | Div(t1,t2) | Mod(t1,t2) | Shr(t1,t2) | Shl(t1,t2) | Band(t1,t2) | Bor(t1,t2) | Bxor(t1,t2)
      -> mapUnion fv_t [t1;t2]
    | Bnot t1 -> fv_t t1

  let rec getVarsByAttrs aa t =
    match t with
    | T.Var(v,attrs) when not (Attrs.disjoint aa attrs) (* && String.get v 0 <> '#' *) -> singleton t
    | T.Add tt | T.Sub tt | T.Fcall(_,tt)
      -> mapUnion (getVarsByAttrs aa) tt
    | T.Mul(t1,t2) | T.Div(t1,t2) | T.Mod(t1,t2) | T.Shr(t1,t2) | T.Shl(t1,t2) | T.Band(t1,t2) | T.Bor(t1,t2) | T.Bxor(t1,t2)
      -> union (getVarsByAttrs aa t1) (getVarsByAttrs aa t2)
    | T.Bnot t1 -> getVarsByAttrs aa t1
    | _ -> empty

  let getVarsByAttrsL aa tt = mapUnion (getVarsByAttrs aa) tt

  (* getting hat vars (hatVars' excludes #size@hat *)
  let hatVars u : t = filter T.isHatVar (getVarsByAttrs (Attrs.of_list [HAT]) u)
  let hatVarsL uu : t = filter T.isHatVar (getVarsByAttrsL (Attrs.of_list [HAT]) uu)
                      
  let hatVars' u : t = filter T.isHatVar' (getVarsByAttrs (Attrs.of_list [HAT]) u)
  let hatVarsL' uu : t = filter T.isHatVar' (getVarsByAttrsL (Attrs.of_list [HAT]) uu)
                 
  let barVars u : t = getVarsByAttrs (Attrs.of_list [BAR]) u
  let barVarsL uu : t = getVarsByAttrsL (Attrs.of_list [BAR]) uu
                
  let bcdtVars u : t = getVarsByAttrs (Attrs.of_list [BAR;CHECK;DOT;TILDE]) u
  let bcdtVarsL uu : t = getVarsByAttrsL (Attrs.of_list [BAR;CHECK;DOT;TILDE]) uu
                   
  let hcdtVars u : t = getVarsByAttrs (Attrs.of_list [HAT;CHECK;DOT;TILDE]) u
  let hcdtVarsL uu : t = getVarsByAttrsL (Attrs.of_list [HAT;CHECK;DOT;TILDE]) uu
                   
  let signVars u : t = getVarsByAttrs (Attrs.of_list [HAT;BAR;CHECK;DOT;TILDE]) u
  let signVarsL uu : t = getVarsByAttrsL (Attrs.of_list [BAR;CHECK;DOT;TILDE;HAT]) uu

  let hasHatVars' u = not(is_empty (hatVars' u))
  let hasHatVarsL' uu = not(is_empty (hatVarsL' uu))

  let haveDiffHatVarsL' tt0 tt1 =
    let vv0 = hatVarsL' tt0 in
    let vv1 = hatVarsL' tt1 in
    not(is_empty vv0) && not(is_empty vv1) && (disjoint vv0 vv1)
    
  (* Sanitary Checking *)
  (* 
    varProfile t
    (<name>, unlimited_flag)
    ("",0)      (t does not contain hat-var and is limited) 
    ("",1)      (t does not contain hat-var and is unlimited) 
    (<name>,0)  (t has only one hat-var named <name> and is limited)
    (<name>,1)  (t has two hat-vars #size and <name> and is unlimited)
    raise NotSanitary (otherwise) 
   *)
  let varProfile t =
    let vHatNames = Strset.mapUnion T.getVarName (elements (hatVars t)) in
    let vHatNames_wo_size = Strset.remove "#size" vHatNames in
    match Strset.cardinal vHatNames_wo_size with
    | 0 ->
       if is_empty (getVarsByAttrs (Attrs.of_list [BAR;DOT]) t)
       then ("",0)
       else ("",1)
    | 1 ->
       let name = Strset.choose vHatNames_wo_size in
       let flag = if Strset.mem "#size" vHatNames then 1 else 0 in
       (name,flag)
    | _ -> raise NotSanitary

  let print_vp vp =
    let (name,flag) = vp in
    let str = name ^ ": " ^ (if flag = 0 then "limited" else "unlimited") in
    print_endline str
         
  let checkSan t = let _ = varProfile t in ()
         
  let ( <|< ) t1 t2 =
    let vp1 = varProfile t1 in
    let vp2 = varProfile t2 in
    let cond1 = (vp1 = ("",1)) && ((fst vp2 <> "") || snd vp2 = 0) in
    let cond2 = (fst vp1 <> "") && (fst vp1 >= fst vp2) in
    cond1 || cond2

  let ( <|= ) t1 t2 =
    let vp1 = varProfile t1 in
    let vp2 = varProfile t2 in
    let cond1 = (vp1 = ("",1)) && ((fst vp2 <> "") || snd vp2 = 0) in
    let cond2 = (fst vp1 <> "") && (fst vp1 > fst vp2) in
    cond1 || cond2

  let ( =|= ) t1 t2 =
    let vp1 = varProfile t1 in
    let vp2 = varProfile t2 in
    let cond1 = (fst vp1 <> "") && (fst vp2 <> "") && (vp1 <> vp2) in
    let cond2 = (vp1 = ("",0)) && (fst vp2 <> "") in
    cond1 || cond2

  let hatcompare t1 t2 =
    try
      let tHat1 = choose (hatVars' t1) in
      let tHat2 = choose (hatVars' t2) in
      T.compare tHat1 tHat2
    with
    | Not_found -> failwith "hatcompare: No hat variables\n"
    
  let checkSanCompare op t1 t2 =
    match op with
    | "EQ" -> if t1 =|= t2 then raise NotSanitary else ()
    | "LT" -> if t1 <|< t2 then raise NotSanitary else ()
    | "LE" -> if t1 <|= t2 then raise NotSanitary else ()
    | _ -> ()

  (* denominator t is {u} if t is t'/u or t'%u. Otherwise {} *)
  (* This is used for biabduction *)
  let denominators t =
    let rec aux t' = 
      match t' with
      | T.Var _ | T.Int _ | T.PosInf | T.NegInf -> empty
      | T.Add tt | T.Sub tt -> mapUnion aux tt
      | T.Mul (t1,t2) | T.Shr (t1,t2) | T.Shl (t1,t2) | T.Band (t1,t2) | T.Bor (t1,t2) | T.Bxor (t1,t2)
        -> mapUnion aux [t1;t2]
      | T.Div (t1,t2) | Mod (t1,t2) -> add t2 (mapUnion aux [t1;t2])
      | T.Bnot t1 -> aux t1
      | T.Fcall _ -> empty   (* Reason: Fcall is ignored in the biabuduction *)
    in
    aux t

  let pp fmt x = pp_list_comma T.pp fmt (elements x)

  let println x = Format.printf "@[{%a}@." pp x
    
end
;;

module Subst = struct 
  type t = (string * SHterm.t) list
end
;;

(*--------------------------------*)
(* Pure Formulas                  *)
(* used for the pure-part of SH   *)
(* pure is no longer presburger   *)
(*--------------------------------*)
module SHpure = struct
  
  (* 'p' is used for them			*)
  (* (In,[t;a;b]) means "t in [a,b]"  *)
  (* (Out,[t;a;b]) means "t notin [a,b]"  *)
  (* (Disj,[a;b;c;d]) means "[a,b] and [c,d] are disjoint"  *)
  (* (Comm,[a;b;c;d]) means "[a,b] and [c,d] have a common element"  *)
  type op = Eq | Neq | Le | Lt | In | Out | Disj | Comm

  (* domain for All and Ex *)
  type domain = Nat | Int

  let pp_domain fmt dom =
    match dom with
    | Nat -> Format.fprintf fmt "nat"
    | Int -> Format.fprintf fmt "int"
    
  let string_of_domain dom =
    match dom with
    | Nat -> "nat"
    | Int -> "int"
                    
  (* Assumption: negations are already removed by de Morgan's law *)
  type t =
    | True (* true (it is used for SH with empty pure-part) *)
    | False
    | Atom of op * T.t list (* atomic formula *)
    | And of t list (* conjunction *)
    | Or of t list  (* disjunction *)
    | Imp of t * t (* implication *)
    | Neg of t (* negation *)
    | All of domain * Strset.t * t  (* universal *)
    | Ex of domain * Strset.t * t  (* existential *)

  let rec pp fmt p =
    match p with
    | True -> Format.fprintf fmt "%s" "True"
    | False -> Format.fprintf fmt "%s" "False"
    | Atom(Eq,[t0;t1]) -> Format.fprintf fmt "%a=%a" T.pp t0 T.pp t1
    | Atom(Eq,tt) -> Format.fprintf fmt "(= %a)" (pp_list "ERROR" " " T.pp) tt
    | Atom(Neq,[t0;t1]) -> Format.fprintf fmt "%a=/%a" T.pp t0 T.pp t1
    | Atom(Neq,tt) -> Format.fprintf fmt "(=/ %a)" (pp_list "ERROR" " " T.pp) tt
    | Atom(Lt,tt) -> pp_list "ERROR" "<" T.pp fmt tt
    | Atom(Le,tt) -> pp_list "ERROR" "<=" T.pp fmt tt
    | Atom(In,[t0;t1;t2]) -> Format.fprintf fmt "%a in [%a,%a]" T.pp t0 T.pp t1 T.pp t2
    | Atom(In,_) -> raiseError "P.pp: Invalid arguments of In"
    | Atom(Out,[t0;t1;t2]) -> Format.fprintf fmt "%a out [%a,%a]" T.pp t0 T.pp t1 T.pp t2
    | Atom(Out,_) -> raiseError "P.pp: Invalid arguments of Out"
    | Atom(Disj,[t0;t1;t2;t3]) -> Format.fprintf fmt "[%a,%a] disj [%a,%a]" T.pp t0 T.pp t1 T.pp t2 T.pp t3
    | Atom(Disj,_) -> raiseError "P.pp: Invalid arguments of Disj"
    | Atom(Comm,[t0;t1;t2;t3]) -> Format.fprintf fmt "[%a,%a] comm [%a,%a]" T.pp t0 T.pp t1 T.pp t2 T.pp t3
    | Atom(Comm,_) -> raiseError "P.pp: Invalid arguments of Comm"
    | And qq -> pp_list "True" " & " pp1 fmt qq
    | Or qq -> pp_list "False" " | " pp1 fmt qq
    | Imp (q0,q1) -> Format.fprintf fmt "%a => %a" pp1 q0 pp1 q1
    | Neg q -> Format.fprintf fmt "NOT %a" pp1 q
    | All(dom,vvv,q) -> Format.fprintf fmt "ALL%a[%a](%a)"
                          pp_domain dom
                          (pp_list_comma Format.pp_print_string) (Strset.elements vvv)
                          pp q
    | Ex(dom,vvv,q) -> Format.fprintf fmt "EX%a[%a](%a)"
                         pp_domain dom
                         (pp_list_comma Format.pp_print_string) (Strset.elements vvv)
                         pp q
  and pp1 fmt p =
    match p with
    | True | False | Atom(_,_) -> Format.fprintf fmt "%a" pp p
    | And qq | Or qq -> if List.length qq = 1 then Format.fprintf fmt "%a" pp p else Format.fprintf fmt "(%a)" pp p
    | _ -> Format.fprintf fmt "(%a)" pp p

  let print = Format.printf "@[%a@]" pp

  let println = Format.printf "@[%a@." pp

  let rec evalUnderPmodel pmodel p =
    let evalT t = T.evalUnderPmodel pmodel t in
    let isInvl t u = (evalT t) <= (evalT u) in
    let ( <@= ) t u = (evalT t) <= (evalT u) in
    let ( <@< ) t u = (evalT t) < (evalT u) in
    let ( =@= ) t u = (evalT t) = (evalT u) in
    let ( <@> ) t u = (evalT t) <> (evalT u) in    
    match p with
    | True -> true
    | False -> false
    | Atom (Eq,[t;u]) -> t =@= u
    | Atom (Neq,[t;u]) -> t <@> u
    | Atom (Le,[t;u]) -> t <@= u
    | Atom (Lt,[t;u]) -> t <@< u
    | Atom (In,[t;u1;u2])  when isInvl u1 u2 -> u1 <@= t && t <@= u2
    | Atom (Out,[t;u1;u2]) when isInvl u1 u2 -> t <@< u1 || u2 <@< t
    | Atom (Disj,[t1;u1;t2;u2]) when (isInvl t1 u1) && (isInvl t2 u2) -> u1 <@< t2 || u2 <@< t1
    | Atom (Comm,[t1;u1;t2;u2]) when (isInvl t1 u1) && (isInvl t2 u2) -> t2 <@< u1 && t1 <@< u2
    | Atom (_,_) -> false
    | Or  pp -> List.exists (evalUnderPmodel pmodel) pp
    | And pp -> List.for_all (evalUnderPmodel pmodel) pp
    | Imp (p1,p2) -> (not (evalUnderPmodel pmodel p1)) || (evalUnderPmodel pmodel p2)
    | Neg p0 -> not (evalUnderPmodel pmodel p0)
    | All _ -> failwith "P.evalUnderPmodel: unsupported"
    | Ex _ -> failwith "P.evalUnderPmodel: unsupported"
          
  (* comparison function for pure formulas *)
  let compare p1 p2 = 
    let toAbstract p = 
      match p with
      | True -> (0,"",[],[])
      | False -> (1,"",[],[])
      | Atom(op,tt) ->
         let str_op = 
           match op with
           | Eq -> "Eq"
           | Neq -> "Neq"
           | Le -> "Le"
           | Lt -> "Lt"
           | In -> "In"
           | Out -> "Out"
           | Disj -> "Disj"
           | Comm -> "Comm"
         in
         (2,str_op,tt,[])
      | And pp -> (3,"",[],pp)
      | Or pp -> (4,"",[],pp)
      | Imp(p1,p2) -> (5,"",[],[p1;p2])
      | Neg p0 -> (6,"",[],[p0])
      | All(dom,vvv,p0) ->
         let strDom = if dom = Nat then "Nat" else "Int" in
         (* let str = List.fold_left (fun s0 s -> String.cat s0 s) "" (Strset.add strDom vvv) in *)
         let str = strDom ^ (Strset.fold ( ^ ) vvv "") in
         (7,str,[],[p0])
      | Ex(dom,vvv,p0) ->
         let strDom = if dom = Nat then "Nat" else "Int" in
         let str = strDom ^ (Strset.fold ( ^ ) vvv "") in
         (8,str,[],[p0])
    in
    genCompare toAbstract T.compare p1 p2
          
  (* this checks whether the given p is a presburger formula *)
  (* If it is then do nothing, else raise the NotPresburger exception *)
  let rec checkPresburger p =
    match p with
    | True | False -> ()
    | Atom (_,tt) -> List.iter T.checkPresburger tt 
    | And pp | Or pp -> List.iter checkPresburger pp
    | Imp (p1,p2) -> List.iter checkPresburger [p1;p2]
    | Neg p -> checkPresburger p
    | All (_,_,p) | Ex (_,_,p) -> checkPresburger p

  let rec dual p =
    match p with
    | True -> False
    | False -> True
    | And pp ->
       let pp' = List.map dual pp in
       Or pp'
    | Or pp ->
       let pp' = List.map dual pp in
       And pp'
    | Imp (p1,p2) ->
       let not_p2 = dual p2 in
       And [p1;not_p2]
    | Neg p0 -> p0
    | All (dom,vv,p) -> Ex (dom,vv,dual p)
    | Ex (dom,vv,p) -> All (dom,vv,dual p)
    | Atom (op,tt) ->
       match op with
       | Eq -> Atom (Neq,tt)
       | Neq -> Atom (Eq,tt)
       | Le ->
          let t0 = List.nth tt 0 in
          let t1 = List.nth tt 1 in
          Atom (Lt,[t1;t0])
       | Lt ->
          let t0 = List.nth tt 0 in
          let t1 = List.nth tt 1 in
          Atom (Le,[t1;t0])
       | In -> Atom (Out,tt)
       | Out -> Atom (In,tt)
       | Disj -> Atom (Comm,tt)
       | Comm -> Atom (Disj,tt)
                                
  let rec fv p =
    match p with
    | True -> Strset.empty
    | False -> Strset.empty
    | Atom (_,tt) -> List.fold_left (fun s t -> Strset.union s (T.fv t)) Strset.empty tt
    | And pp -> List.fold_left (fun s p -> Strset.union s (fv p)) Strset.empty pp
    | Or pp -> List.fold_left (fun s p -> Strset.union s (fv p)) Strset.empty pp
    | Imp (p1,p2) -> Strset.union (fv p1) (fv p2)
    | Neg p1 -> fv p1
    | All (_,vvv,p) -> Strset.diff (fv p) vvv
    | Ex (_,vvv,p) -> Strset.diff (fv p) vvv

  let rec terms p : Tset.t =
    match p with
    | Atom (_,tt) -> Tset.of_list tt
    | And pp | Or pp -> Tset.mapUnion terms pp
    | Imp (p1,p2) -> Tset.union (terms p1) (terms p2)
    | Neg p0 -> terms p0
    | All (_,_,p0) | Ex (_,_,p0) -> terms p0
    | _ -> Tset.empty
                    
  (* This function returns free variables as terms *)
  (* It is used to obtain free *signed* variables, which are never quantified *)
  let rec fv_t p =
    match p with
    | True -> Tset.empty
    | False -> Tset.empty
    | Atom (_,tt) -> Tset.mapUnion Tset.fv_t tt
    | And pp -> Tset.mapUnion fv_t pp
    | Or pp -> Tset.mapUnion fv_t pp
    | Imp (p1,p2) -> Tset.mapUnion fv_t [p1;p2]
    | Neg p1 -> fv_t p1
    | All (_,vv,p) -> fv_t p
    | Ex (_,vv,p) -> fv_t p

  let rec getConsts p = 
    match p with
    | True -> Intset.empty
    | False -> Intset.empty
    | Atom (_,tt) -> T.getConstsL tt
    | And pp -> getConstsL pp
    | Or pp -> getConstsL pp
    | Imp (p1,p2) -> getConstsL [p1;p2]
    | Neg p1 -> getConsts p
    | All (_,vvv,p) -> getConsts p
    | Ex (_,vvv,p) -> getConsts p
  and getConstsL pp = Intset.mapUnion getConsts pp
                   
  let mkAnd pp =
    match pp with
    | [] -> True
    | [p] -> p
    | _ -> And pp
    
  let mkOr pp =
    match pp with
    | [] -> False
    | [p] -> p
    | _ -> Or pp
                   
  let hatVars p = Tset.filter T.isHatVar (fv_t p)
                
  let hatVars' p = Tset.filter T.isHatVar' (fv_t p)
                
  let barVars p = Tset.filter T.isBarVar (fv_t p)

  let bcdtVars p = Tset.filter T.isBCDTVar (fv_t p)

  let signVars p = Tset.filter T.isSignVar (fv_t p)

  let rec flattenAndOr p : t =
    match p with
    | True | False | Atom _ -> p
    | And pp ->
       begin
         match flattenAnd pp with
         | [] -> True
         | [q] -> flattenAndOr q
         | qq ->
            match List.filter (fun a -> a<>True) (List.map flattenAndOr qq) with
            | [] -> True
            | [q'] -> q'
            | qq' -> And qq'
       end
    | Or pp ->
       begin
         match flattenOr pp with
         | [] -> False
         | [q] -> q
         | qq ->
            match List.filter (fun a -> a<>False) (List.map flattenAndOr qq) with
            | [] -> False
            | [q'] -> q'
            | qq' -> Or qq'
       end
    | Imp (True,p2) -> flattenAndOr p2
    | Imp (False,p2) -> True
    | Imp (p1,p2) -> Imp(flattenAndOr p1,flattenAndOr p2)
    | Neg True -> False
    | Neg False -> True
    | Neg p1 -> Neg (flattenAndOr p1)
    | All (s,vv,p) -> All(s,vv,flattenAndOr p)
    | Ex (s,vv,p) -> Ex(s,vv,flattenAndOr p)
  and flattenAnd pp = (* produces a list of Atom/Or/forall/exists or [False] *)
    let rec flattenAndAux qq pp = 
      match pp with
      | [] -> List.rev qq
      | (And pp0)::pp1 -> flattenAndAux qq (pp0@pp1)
      | True::pp1 -> flattenAndAux qq pp1
      | False::pp1 -> [False]
      | q::pp1 -> flattenAndAux (q::qq) pp1
    in
    flattenAndAux [] pp
  and flattenOr pp = (* produces a list of Atom/And/forall/exists or [True] *)
    let rec flattenOrAux qq pp = 
      match pp with
      | [] -> List.rev qq
      | (Or pp0)::pp1 -> flattenOrAux qq (pp0@pp1)
      | True::pp1 -> [True]
      | False::pp1 -> flattenOrAux qq pp1
      | q::pp1 -> flattenOrAux (q::qq) pp1
    in
    flattenOrAux [] pp
      
  (* Sanitary checking  *)
  (* x@hat < x@hat+1 is sanitary *)
  (* x@hat = y@hat is not sanitary *)
  let checkSanAtom p =
    match p with
    | True | False -> ()
    | Atom (Disj,tt) ->
       let t0L = List.nth tt 0 in
       let t0R = List.nth tt 1 in
       let t1L = List.nth tt 2 in
       let t1R = List.nth tt 3 in
       Tset.checkSanCompare "LT" t0R t1L;
       Tset.checkSanCompare "LT" t1R t0L;
    | Atom (Neq,tt) -> 
       let t0 = List.nth tt 0 in
       let t1 = List.nth tt 1 in
       Tset.checkSan t0;
       Tset.checkSan t1;
    | Atom (Eq,tt) -> 
       let t0 = List.nth tt 0 in
       let t1 = List.nth tt 1 in
       Tset.checkSanCompare "EQ" t0 t1;
    | Atom (Lt,tt) ->
       let t0 = List.nth tt 0 in
       let t1 = List.nth tt 1 in
       Tset.checkSanCompare "LT" t0 t1
    | Atom (Le,tt) ->
       let t0 = List.nth tt 0 in
       let t1 = List.nth tt 1 in
       Tset.checkSanCompare "LE" t0 t1       
    | Atom (_,_) -> ()
    | And pp -> ()
    | Or pp -> ()
    | Imp (_,_) -> ()
    | Neg _ -> ()
    | All(_,_,p) -> ()
    | Ex(_,_,p) -> ()

  let update_checkSan p =
    let rec aux p0 = 
      match p0 with
      | And pp ->
         let pp' = List.map aux pp in
         And pp'
      | Or pp ->
         let pp' = List.map aux pp in
         Or pp'
      | Imp (p1,p2) ->
         let p1' = aux p1 in
         let p2' = aux p2 in
         Imp (p1',p2')
      | Neg p1 ->
         let p1' = aux p1 in
         Neg p1'
      | All(dom,vv,p) ->
         let p' = aux p in
         All(dom,vv,p')
      | Ex(dom,vv,p) ->
         let p' = aux p in
         Ex(dom,vv,p')
      | _ -> (* Atoms *)
         try
           checkSanAtom p0; p0
         with
           NotSanitary -> False
    in
    aux p
    
  let rec varRepl repl (p : t) : t =
    match p with
    | True  -> p
    | False -> p
    | Atom(op,tt) -> 
       let tt' = List.map (T.varRepl repl) tt in
       Atom (op,tt')
    | And pp ->
       let pp' = List.map (varRepl repl) pp in
       And pp'
    | Or pp ->
       let pp' = List.map (varRepl repl) pp in
       Or pp'
    | Imp (p1,p2) ->
       let p1' = varRepl repl p1 in
       let p2' = varRepl repl p2 in
       Imp (p1',p2')
    | Neg p1 ->
       let p1' = varRepl repl p1 in
       Neg p1'
    | All(dom,vv,p) ->
       let p' = varRepl repl p in
       All(dom,vv,p')
    | Ex(dom,vv,p) ->
       let p' = varRepl repl p in
       Ex(dom,vv,p') 

  let alpha_conv vvvAvoid (p : t) =         
    let genSafeVar (vvvAvoid,repl) v =
      match Strset.mem v vvvAvoid with
      | false -> ((vvvAvoid,repl),v)
      | true -> 
         let v1 = Strset.genFresh v vvvAvoid in
         let vvvAvoid1 = Strset.add v1 vvvAvoid in
         let repl1 = (v,v1) :: repl in
         ((vvvAvoid1,repl1),v1)
    in
    let rec alphaRec vvv_repl p = 
      match p with
      | True | False | Atom(_,_) -> (vvv_repl,p)
      | And pp -> 
         let (vvv_repl',pp') = List_tailrec.map_state alphaRec vvv_repl pp in
         (vvv_repl',And pp')
      | Or pp ->
         let (vvv_repl',pp') = List_tailrec.map_state alphaRec vvv_repl pp in
         (vvv_repl',Or pp')
      | Imp (p0,p1) -> 
         let (vvv_repl1,p0') = alphaRec vvv_repl  p0 in
         let (vvv_repl2,p1') = alphaRec vvv_repl1 p1 in
         (vvv_repl2,Imp(p0',p1'))
      | Neg p0 ->
         let (vvv_repl1,p0') = alphaRec vvv_repl p0 in
         (vvv_repl1,Neg p0')
      | All(dom,vvv0,p0) ->
         let (vvv_repl1,vv1) = List_tailrec.map_state genSafeVar vvv_repl (Strset.elements vvv0) in
         let (vvv_repl2,p1) = alphaRec vvv_repl1 p0 in
         let vvv1 = Strset.of_list vv1 in         
         (vvv_repl2,All(dom,vvv1,p1))
      | Ex(dom,vvv0,p0) ->
         let (vvv_repl1,vv1) = List_tailrec.map_state genSafeVar vvv_repl (Strset.elements vvv0) in
         let (vvv_repl2,p1) = alphaRec vvv_repl1 p0 in
         let vvv1 = Strset.of_list vv1 in
         (vvv_repl2,Ex(dom,vvv1,p1))
    in
    snd (alphaRec (vvvAvoid,[]) p)
    
  let rec subst (sub : Subst.t) p =
    let vvv_fv = fv p in
    let vvv_sub = List.fold_left (fun vvv (v,t) -> Strset.union (Strset.add v vvv) (T.fv t)) Strset.empty sub in
    let vvv_avoid = Strset.union vvv_fv vvv_sub in
    let p1 = alpha_conv vvv_avoid p in
    match p1 with
    | True | False -> p1
    | Atom(op,tt) -> 
       let tt' = List.map (T.subst sub) tt in
       Atom (op,tt')
    | And pp ->
       let pp' = List.map (subst sub) pp in
       And pp'
    | Or pp ->
       let pp' = List.map (subst sub) pp in
       Or pp'
    | Imp (p1,p2) ->
       let p1' = subst sub p1 in
       let p2' = subst sub p2 in
       Imp (p1',p2')
    | Neg p1 ->
       let p1' = subst sub p1 in
       Neg p1'
    | All(dom,vv0,p0) ->
       let p2 = subst sub p0 in
       All(dom,vv0,p2)            
    | Ex(dom,vv0,p0) ->
       let p2 = subst sub p0 in
       Ex(dom,vv0,p2)     
      
  let rec normalizeTerms (p : t) : t =
    match p with
    | True  -> p
    | False -> p
    | Atom(op,tt) -> 
       let tt' = List.map T.nf tt in
       Atom (op,tt')
    | And pp ->
       let pp1 = List.map normalizeTerms pp in
       And pp1
    | Or pp ->
       let pp1 = List.map normalizeTerms pp in
       Or pp1
    | Imp (p1,p2) ->
       let p1' = normalizeTerms p1 in
       let p2' = normalizeTerms p2 in       
       Imp (p1',p2')
    | Neg p1 ->
       let p1' = normalizeTerms p1 in
       Neg p1'
    | All(dom,vv,p) ->
       let p' = normalizeTerms p in
       All(dom,vv,p')
    | Ex(dom,vv,p) ->
       let p' = normalizeTerms p in
       Ex(dom,vv,p')

  (* 
    extract_nonPb _vv _eqlist (x = f(y) + 3 & z = g(x)) 
    returns
    x = ##0 + 3 & z = ##1
    with
    !_vv = [x;y;z;##0;##1]
    !_eqlist = [ (f(y),##0); (g(x),##1) ]
   *)
  let extract_nonPb vvv_eqlist p =
    let rec aux vvv_eqlist p =
      let (vvv,eqlist) = vvv_eqlist in
      match p with
      | True | False -> (vvv_eqlist,p)
      | Atom (op,tt) ->
         let (vvv_eqlist1,tt') = List_tailrec.map_state T.extract_nonPb vvv_eqlist tt in
         (vvv_eqlist1,Atom (op,tt'))
      | And pp ->
         let (vvv_eqlist1,pp') = List_tailrec.map_state aux vvv_eqlist pp in
         (vvv_eqlist1,And pp')
      | Or pp ->
         let (vvv_eqlist1,pp') = List_tailrec.map_state aux vvv_eqlist pp in
         (vvv_eqlist1,Or pp')
      | Imp (p1,p2) ->
         let (vvv_eqlist1,p1') = aux vvv_eqlist  p1 in
         let (vvv_eqlist2,p2') = aux vvv_eqlist1 p2 in
         (vvv_eqlist2, Imp (p1',p2'))
      | Neg p1 ->
         let (vvv_eqlist1,p1') = aux vvv_eqlist p1 in         
         (vvv_eqlist1,Neg p1')
      | All (dom,vvv0,p0) ->
         let vvv1 = Strset.union vvv0 vvv in
         let vvv_eqlist1 = (vvv1,eqlist) in
         let (vvv_eqlist2,p1) = aux vvv_eqlist1 p0 in
         (vvv_eqlist2, All (dom,vvv1,p1))
      | Ex (dom,vvv0,p0) ->
         let vvv1 = Strset.union vvv0 vvv in
         let vvv_eqlist1 = (vvv1,eqlist) in
         let (vvv_eqlist2,p1) = aux vvv_eqlist1 p0 in
         (vvv_eqlist2, Ex (dom,vvv1,p1))
    in
    let (vvv,eqlist) = vvv_eqlist in
    let vvv1 = Strset.union (fv p) vvv in
    aux (vvv1,eqlist) p

  let denominators p : Tset.t =
    let rec aux p' =
      match p' with
      | True | False -> Tset.empty
      | Atom (_,tt) -> Tset.mapUnion Tset.denominators tt
      | And pp | Or pp -> Tset.mapUnion aux pp
      | Imp (p1,p2) -> Tset.mapUnion aux [p1;p2]
      | Neg p1 -> aux p1
      | All (_,_,p) | Ex (_,_,p) -> aux p
    in
    aux p

  (* Assumption: a@hat < b@hat < c@hat *)
  (* Atom (Disj,[a@hat;a@hat+N;b@hat;b@hat+M]) is reduced to Atom(Lt,[a@hat+N; b@hat]) *)
  (* Or [ Atom(Lt,[a@hat+N;b@hat]); Atom(Lt,[b@hat+M;a@hat]) ] is reduced to Atom(Lt,[a@hat+N;b@hat]) *)
  let reduce_disjunctions p =
    let rec aux p' =
      match p' with
      | All (dom,vv,p1) ->
         let p1' = aux p1 in
         All(dom,vv,p1')
      | Ex (dom,vv,p1) ->
         let p1' = aux p1 in         
         Ex(dom,vv,p1')
      | And pp ->
         let pp' = List.map aux pp in
         And pp'
      | Or [ Atom(Lt,[u1;t2]); Atom(Lt,[u2;t1]) ]
      | Atom (Disj,[t1;u1;t2;u2]) ->
         let hatVars1 = Tset.hatVarsL' [t1;u1] in
         let hatVars2 = Tset.hatVarsL' [t2;u2] in
         let hatVarNames1 = Tset.fold (fun u sss -> Strset.union sss (T.getVarName u)) hatVars1 Strset.empty in
         let hatVarNames2 = Tset.fold (fun u sss -> Strset.union sss (T.getVarName u)) hatVars2 Strset.empty in
         let hatVarNameL1 = Strset.elements hatVarNames1 in
         let hatVarNameL2 = Strset.elements hatVarNames2 in
         begin
           match hatVarNameL1,hatVarNameL2 with
           | [v1],[v2] when v1 < v2 -> Atom(Lt,[u1;t2])
           | [v1],[v2] -> Atom(Lt,[u2;t1])
           | _ -> p'
         end
      | Or pp ->
         let pp' = List.map aux pp in
         Or pp'
      | Neg _ -> p'
      | Imp (p1,p2) ->
         let p2' = aux p2 in
         Imp (p1,p2')
      | _ -> p'
    in
    aux p

  let rec applyAtom f p =
    match p with
    | Atom _ -> f p
    | And pp -> And (List.map (applyAtom f) pp)
    | Or  pp -> Or  (List.map (applyAtom f) pp)
    | Imp (p1,p2) -> Imp (applyAtom f p1, applyAtom f p2)
    | Neg p1 -> Neg (applyAtom f p1)
    | All (tp,vv,p1) -> All (tp,vv,applyAtom f p1)
    | Ex  (tp,vv,p1) -> Ex  (tp,vv,applyAtom f p1)
    | _ -> p
         
  (* Naive simplification *)
  (* For M:positive int, N:non-negative int *)
  (* t = t --> true *)
  (* t = t+M --> false *)
  (* t+M = t --> false *)
  (* t = PosInf --> false if t <> PosInf *)
  (* t = NegInf --> false if t <> NegInf *)
  (* t <> PosInf --> true if t <> PosInf *)
  (* t <> NegInf --> true if t <> NegInf *)
  (* t =/ t --> false *)
  (* t =/ t+M --> true *)
  (* t+M =/ t --> true *)
  (* t < t --> false  *)
  (* t < t+M --> true  *)
  (* t+M < t --> false *)
  (* t+m < t+n --> true if m < n *)
  (* t+u1 < t+u2 --> u1 < u2 *)
  (* t <= t --> true  *)    
  (* t <= t+N --> true *)
  (* PosInf < t --> false *)
  (* PosInf <= t & t <> PosInf --> false *)
  (* t <= PosInf --> true *)
  (* t < PosInf & t <> PosInf --> true *)
  (* NegInf <= t --> true *)
  (* NegInf < t & t <> NegInf --> true *)
  (* t < NegInf --> false *)
  (* t <= NegInf & t <> PosInf --> false *)
  (* t+m <= t+n --> true if m <= n *)    
  (* (In,[t;t+M;_]) --> false *)
  (* (In,[t+M;_;t]) --> false *)
  (* (In,[t+m;t+n;_]) --> false (when m < n) *)
  (* (In,[t+m;_;t+n]) --> false (when n < m) *)
  (* (In,[t;t;_]) --> true *)
  (* (In,[t;_;t]) --> true *)    
  (* (Out,[t;t+M;_]) --> true *)
  (* (Out,[t+M;_;t]) --> true *)
  (* (Out,[t+m;t+n;_]) --> true (when m < n) *)
  (* (Out,[t+m;_;t+n]) --> true (when n < m) *)
  (* (Out,[t;t;_]) --> false *)
  (* (Out,[t;_;t]) --> false *)    
  (* (Disj,[_;t;t;_]) --> false *)
  (* (Disj,[t;_;_;t]) --> false *)    
  (* (Disj,[t;t;t+M;t+M]) --> true *)
  (* (Disj,[t+M;t+M;t;t]) --> true *)
  (* (Disj,[t+m;t+m;t+n;t+n]) --> true (when m <> n) *)
  (* (Comm,[_;t;t;_]) --> true *)
  (* (Comm,[t;_;_;t]) --> true *)    
  (* (Comm,[t;t;t+M;t+M]) --> false *)
  (* (Comm,[t+M;t+M;t;t]) --> false *)
  (* (Comm,[t+m;t+m;t+n;t+n]) --> false (when m <> n) *)
  (* HAT VARIABLE HANDLING (special) *)
  (* hat variable handling *)
  (* a@hat+M == 0 --> false *)
  (* a@hat+M != 0 --> true  *)
  (* a@hat+M == b@hat+N --> false *)
  (* a@hat+M != b@hat+N --> true  *)
  (* 0 < a@hat --> true *)
  (* 0 < a@hat+M --> true *)
  (* a@hat <= 0 --> false *)
  (* a@hat+M <= --> false *)
  let syntactical_simpl p =
    let toList t =
      match t with
      | T.Add tt -> tt
      | _ -> [t]
    in
    let fromList tt =
      match tt with
      | [] -> T.Int 0
      | [t] -> t
      | _ -> T.Add tt
    in
    let dropsame t u = (* (a+b+X)#(a+b+Y) --> X#Y, (a+b)#(a+b+Y) --> 0#Y, (a+b+X)#(a+b) --> X#0 *)
      let rec aux tt uu =
        match tt,uu with
        | t0::tt0,u0::uu0 when t0 = u0 -> aux tt0 uu0
        | _,_ -> (fromList tt,fromList uu)
      in
      aux (toList t) (toList u)
    in
    let dropConst t u = (* (X+(m+n))#(Y+n) --> X+m#Y, (X+n)#(Y+(m+n)) --> X#Y+m *)
      let tt = List.rev @@ toList t in
      let uu = List.rev @@ toList u in
      match tt,uu with
      | (T.Int m)::tt1,(T.Int n)::uu1 when m < n ->
         let t1 = fromList @@ List.rev tt1 in
         let u1 = fromList @@ List.rev ((T.Int (n-m))::uu1) in
         (t1,u1)
      | (T.Int m)::tt1,(T.Int n)::uu1 when n < m ->
         let t1 = fromList @@ List.rev ((T.Int (m-n))::tt1) in
         let u1 = fromList @@ List.rev uu1 in
         (t1,u1)
      | (T.Int m)::tt1,(T.Int n)::uu1 when m = n ->
         let t1 = fromList @@ List.rev tt1 in
         let u1 = fromList @@ List.rev uu1 in
         (t1,u1)
      | _,_ -> (t,u)
    in
    let simplAtom0 p =
      match p with
      | Atom (op,[t;u]) when List.mem op [Eq;Neq;Le;Lt] ->
         let t1 = T.syntactical_simpl t in
         let u1 = T.syntactical_simpl u in
         let (t2,u2) = dropsame t1 u1 in
         let (t3,u3) = dropConst t2 u2 in
         Atom (op,[t3;u3])
      | Atom (op,tt) -> Atom (op, List.map T.syntactical_simpl tt)
      | _ -> p
    in
    let simplAtom p =
      let p1 = simplAtom0 p in
      match p1 with
      | Atom (Eq,[t;u]) when t =.= u -> True
      | Atom (Eq,[T.Int m;T.Int n]) when m <> n -> False
      | Atom (Eq,[t; T.Add [u;T.Int m]]) when m > 0 && t =.= u -> False
      | Atom (Eq,[T.Add [t;T.Int m];u]) when m > 0 && t =.= u -> False
      (*--*)
      | Atom (Eq,[t;T.PosInf]) when t <.> T.PosInf -> False
      | Atom (Eq,[T.PosInf;t]) when t <.> T.PosInf -> False
      | Atom (Eq,[t;T.NegInf]) when t <.> T.NegInf -> False
      | Atom (Eq,[T.NegInf;t]) when t <.> T.NegInf -> False
      (*--*)
      | Atom (Neq,[t;u]) when t =.= u -> False
      | Atom (Neq,[T.Int m;T.Int n]) when m <> n -> True
      | Atom (Neq,[t; T.Add [u;T.Int m]]) when m > 0 && t =.= u -> True
      | Atom (Neq,[T.Add [t;T.Int m];u]) when m > 0 && t =.= u -> True
      (*--*)
      | Atom (Neq,[t;T.PosInf]) when t <.> T.PosInf -> True
      | Atom (Neq,[T.PosInf;t]) when t <.> T.PosInf -> True
      | Atom (Neq,[t;T.NegInf]) when t <.> T.NegInf -> True
      | Atom (Neq,[T.NegInf;t]) when t <.> T.NegInf -> True
      (*--*)
      | Atom (Lt,[t;u]) when t =.= u -> False
      | Atom (Lt,[t; T.Add [u;T.Int m]]) when (m > 0 && t =.= u) -> True
      | Atom (Lt,[T.Add[t;T.Int m];u]) when m > 0 && t =.= u -> False
      | Atom (Lt,[T.Add[t;T.Int m];T.Add[u;T.Int n]]) when m < n && t =.= u -> True
      | Atom (Lt,[T.Int m;T.Int n]) when m < n -> True
      | Atom (Lt,[T.Int m;T.Int n]) when m >= n -> False
      (*--*)
      | Atom (Lt,[T.PosInf;_]) -> False
      | Atom (Lt,[T.NegInf;t]) when t <.> T.NegInf -> True
      | Atom (Le,[T.PosInf;t]) when t <.> T.PosInf -> False
      | Atom (Le,[T.NegInf;_]) -> True
      | Atom (Lt,[t;T.PosInf]) when t <.> T.PosInf -> True
      | Atom (Lt,[_;T.NegInf]) -> False
      | Atom (Le,[_;T.PosInf]) -> True
      | Atom (Le,[t;T.NegInf]) when t <.> T.NegInf -> False
      (*--*)
      | Atom (Le,[t;u]) when t =.= u -> True
      | Atom (Le,[t; T.Add [u;T.Int n]]) when n >= 0 && t =.= u -> True
      | Atom (Le,[T.Add[t;T.Int m];T.Add[u;T.Int n]]) when m <= n && t =.= u -> True
      | Atom (Le,[T.Int m;T.Int n]) when m <= n -> True
      | Atom (Le,[T.Int m;T.Int n]) when m > n -> False
      (*--*)
      | Atom (In,[t; T.Add [u;T.Int m]; _]) when m > 0 && t =.= u -> False
      | Atom (In,[T.Add[t;T.Int m];_;u]) when m > 0 && t =.= u -> False
      | Atom (In,[T.Add[t;T.Int m]; T.Add[u;T.Int n];_]) when m < n && t =.= u -> False
      | Atom (In,[T.Add[t;T.Int m]; _; T.Add[u;T.Int n]]) when n < m && t =.= u -> False
      | Atom (In,[t; u; _]) when t =.= u -> True
      | Atom (In,[t; _; u]) when t =.= u -> True
      (*--*)                                                               
      | Atom (Out,[t; T.Add [u;T.Int m]; _]) when m > 0 && t =.= u -> True
      | Atom (Out,[T.Add [t;T.Int m];_;u]) when m > 0 && t =.= u -> True
      | Atom (Out,[T.Add[t;T.Int m]; T.Add[u;T.Int n]; _]) when m < n && t =.= u -> True
      | Atom (Out,[T.Add[t;T.Int m]; _; T.Add[u;T.Int n]]) when n < m && t =.= u -> True
      | Atom (Out,[t; u; _]) when t =.= u -> False
      | Atom (Out,[t; _; u]) when t =.= u -> False
      (*--*)
      | Atom (Disj,[_;t;u;_]) when t =.= u -> False
      | Atom (Disj,[t;_;_;u]) when t =.= u -> False
      | Atom (Disj,[t1;t2; T.Add[u1;T.Int m1];T.Add[u2;T.Int m2]])
           when t1 =.= t2 && u1 =.= u2 && t1 =.= u1 && m1 = m2 && m1 > 0 -> True
      | Atom (Disj,[T.Add[t1;T.Int m1]; T.Add[t2;T.Int m2]; u1;u2])
           when t1 =.= t2 && u1 =.= u2 && t1 =.= u1 && m1 = m2 && m1 > 0 -> True
      | Atom (Disj,[T.Add[t1;T.Int m1];T.Add[t2;T.Int m2]; T.Add[u1;T.Int n1];T.Add[u2;T.Int n2]])
           when t1 =.= t2 && u1 =.= u2 && t1 =.= u1 && m1 = m2 && n1 = n2 && m1 <> n1 -> True
      (*--*)
      | Atom (Comm,[_;t;u;_]) when t =.= u -> True
      | Atom (Comm,[t;_;_;u]) when t =.= u -> True
      | Atom (Comm,[t1;t2; T.Add[u1;T.Int m1];T.Add[u2;T.Int m2]])
           when t1 =.= t2 && u1 =.= u2 && t1 =.= u1 && m1 = m2 && m1 > 0 -> False
      | Atom (Comm,[T.Add[t1;T.Int m1]; T.Add[t2;T.Int m2]; u1;u2])
           when t1 =.= t2 && u1 =.= u2 && t1 =.= u1 && m1 = m2 && m1 > 0 -> False
      | Atom (Comm,[T.Add[t1;T.Int m1];T.Add[t2;T.Int m2]; T.Add[u1;T.Int n1];T.Add[u2;T.Int n2]])
           when t1 =.= t2 && u1 =.= u2 && t1 =.= u1 && m1 = m2 && n1 = n2 && m1 <> n1 -> False
      | _ -> p1
    in
    let simplAtomHat p =       (*- hat vars -*)
      match p with
      | Atom (Eq,[t;u]) when T.isIntConst u && Tset.hasHatVars' t -> False
      | Atom (Eq,[u;t]) when T.isIntConst u && Tset.hasHatVars' t -> False
      | Atom (Eq,[t;u]) when Tset.haveDiffHatVarsL' [t] [u] -> False
      | Atom (Neq,[t;u]) when T.isIntConst u && Tset.hasHatVars' t -> True
      | Atom (Neq,[u;t]) when T.isIntConst u && Tset.hasHatVars' t -> True
      | Atom (Neq,[t;u]) when Tset.haveDiffHatVarsL'  [t] [u] -> True
      | Atom (Lt,[T.Int 0;u]) when Tset.hasHatVars' u -> True
      | Atom (Lt,[T.Int 0;T.Add[u;T.Int n]]) when n >= 0 && Tset.hasHatVars' u -> True
      | Atom (Le,[u;T.Int 0]) when Tset.hasHatVars' u -> False
      | Atom (Le,[T.Add[u;T.Int n];T.Int 0]) when n >= 0 && Tset.hasHatVars' u -> False
      | Atom (op,[t1;t2]) when (op = Lt || op = Le) && Tset.haveDiffHatVarsL'  [t1] [t2] ->
         begin
           match Tset.hatcompare t1 t2 with
           | 1 -> False
           | _ -> True
         end                                                                                
      | Atom (Disj,[t0;t1;t2;t3]) when Tset.haveDiffHatVarsL' [t0;t1] [t2;t3] -> True
      | Atom (Comm,[t0;t1;t2;t3]) when Tset.haveDiffHatVarsL' [t0;t1] [t2;t3] -> False
      | Atom (Out,[t0;t1;t2]) when Tset.haveDiffHatVarsL' [t0] [t1;t2] -> True
      | _ -> p
    in
    let pOutput = 
      match !simplFlag with
      | false -> p        
      | true -> 
         let p0 = normalizeTerms p in
         let p1 = applyAtom simplAtom p0 in
         let p2 = applyAtom simplAtomHat p1 in    
         let p3 = flattenAndOr p2 in
         (*
    print_endline "<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<";    
    print_endline "p ------------";
    println p;
    print_endline "p0------------";
    println p0;
    print_endline "p1------------";
    println p1;
    print_endline "p2------------";
    println p2;
    print_endline "p3------------";
    println p3;
    print_endline ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>";    
          *)
         p3
    in
    pOutput

  let syntactical_simplL pp =
    List.fold_left
      (fun pp p ->
        let p' = syntactical_simpl p in
        match p', List.mem p' pp with
        | True,_  -> pp
        | _,true  -> pp
        | _,false -> p'::pp
      )
      []
      pp

  (* syntactical simplification of a CNF *)
  (* eval is an evaluation function *)
  (* eval p returns either True or False or p *)
  let syntactical_simplL_CNF eval (pp: t list) : t list =
    let simplOrL ppOr : t list =
      List.fold_left
        (fun qq p ->
          match qq,eval p with
          | [True],_ -> [True]
          | _,True -> [True]
          | _,False -> qq
          | _,_ -> p::qq)
        []
        ppOr
    in
    let simplAndL ppAnd : t list =
      List.fold_left
        (fun qq p ->
          match qq,eval p with
          | [False],_ -> [False]
          | _,True -> qq
          | _,False -> [False]
          | _,_ -> p::qq)
        []
        ppAnd
    in
    let simplOr p =
      match simplOrL (flattenOr [p]) with
      | [] -> False
      | [q] -> q
      | qq -> Or qq
    in
    simplAndL (List.map simplOr pp)

  let evalAddr p =
    match p with
    | Atom (Lt,[T.Int 0;_]) -> True
    | Atom (Le,[_;T.Int 0]) -> False
    | Atom (Le,[t; T.Add [u;T.Int n]]) when n >= 0 && t = u -> True
    | Atom (Lt,[t; T.Add [u;T.Int n]]) when n > 0 && t = u -> True
    | Atom (Le,[T.Add [u;T.Int n];t]) when n >= 0 && t = u -> False
    | Atom (Lt,[T.Add [u;T.Int n];t]) when n > 0 && t = u -> False
    | _ -> p
           
  (* [(a@hat+3,b@bar+7);(c@hat,d@bar); P|R] -> [ [a@hat;b@bar]; [c@hat;d@bar] ] *)
  (* For biabduction (list) grouping *)
  let extractEqClassL p =
    let rec extendEqClassL (t,u) result eqclassL =
      match eqclassL with
      | [] -> [t;u] :: result
      | cls::eqclassL1 ->
         begin
           match List.mem t cls, List.mem u cls with
           | true,true -> eqclassL @ result
           | true,false -> (u::cls) :: eqclassL1 @ result
           | false,true -> (t::cls) :: eqclassL1 @ result
           | false,false -> extendEqClassL (t,u) (cls::result) eqclassL1
         end
    in
    let rec ext eqclassL p = 
      match p with
      | Atom(Eq,[t;u]) ->
         begin
           match T.getHeadTerm t, T.getHeadTerm u with
           | [t1],[u1] -> extendEqClassL (t1,u1) [] eqclassL
           | _,_ -> eqclassL
         end
      | And pp -> extL eqclassL pp
      | _ -> []
    and extL eqclassL pp =
      match pp with
      | [] -> eqclassL
      | p::pp1 ->
         let eqclassL1 = ext eqclassL p in
         extL eqclassL1 pp1
    in
    ext [] p

  (* just replacing #IN(u,x) --> a *)
  let rec unfold_indirect (p : t) : t =
    match p with
    | True | False -> p
    | Atom(op,tt) -> 
       let tt' = List.map T.unfold_indirect tt in
       Atom (op,tt')
    | And pp ->
       let pp' = List.map unfold_indirect pp in
       And pp'
    | Or pp ->
       let pp' = List.map unfold_indirect pp in
       Or pp'
    | Imp (p1,p2) ->
       let p1' = unfold_indirect p1 in
       let p2' = unfold_indirect p1 in
       Imp (p1',p2')
    | Neg p1 ->
       let p1' = unfold_indirect p1 in
       Neg p1'
    | All(dom,vv0,p0) ->
       let p2 = unfold_indirect p0 in
       All(dom,vv0,p2)            
    | Ex(dom,vv0,p0) ->
       let p2 = unfold_indirect p0 in
       Ex(dom,vv0,p2)     

  let rec extinguish_phantoms (p:t) : t =
    match p with
    | Atom(op,tt) when L.exists T.isPhantomVar tt -> True
    | And pp -> And (L.filter (fun p -> p<>True) (L.map extinguish_phantoms pp))
    | Or pp -> Or (L.map extinguish_phantoms pp)
    | Imp (p1,p2) -> Imp (extinguish_phantoms p1, extinguish_phantoms p2)
    | Neg p1 -> Neg (extinguish_phantoms p1)
    | All(dom,vv0,p0) -> All(dom,vv0,extinguish_phantoms p0)
    | Ex(dom,vv0,p0) -> Ex(dom,vv0,extinguish_phantoms p0)
    | _ -> p
                      
end
;;

module P = SHpure;;

let ( =.= ) t1 t2 = P.Atom(P.Eq, [t1;t2]);;
let ( <.< ) t1 t2 = P.Atom(P.Lt, [t1;t2]);;
let ( <.> ) t1 t2 = P.Atom(P.Neq, [t1;t2]);;
let ( <.= ) t1 t2 = P.Atom(P.Le, [t1;t2]);;
let _In t t1 t2 = P.Atom(P.In, [t;t1;t2]);;
let _Out t t1 t2 = P.Atom(P.Out, [t;t1;t2]);;
let _Disj t1 u1 t2 u2 = P.Atom(P.Disj, [t1;u1;t2;u2]);;
let _Comm t1 u1 t2 u2 = P.Atom(P.Comm, [t1;u1;t2;u2]);;

let ( &.& ) p q = P.And [p;q];;
let ( |.| ) p q = P.Or [p;q];;
let ( =.> ) p q = P.Imp (p,q);;
let _AllNat vv p = P.All(P.Nat,vv,p);;
let _ExNat vv p = P.Ex(P.Nat,vv,p);;
let _AllInt vv p = P.All(P.Int,vv,p);;
let _ExInt vv p = P.Ex(P.Int,vv,p);;


module SHspatExp = struct
(* Single Spatial expressions *)
(* 's' is used for them	*)

  type t =
    | Pto of T.t * (string * T.t) list
    | Arr of T.t * T.t
    | Str of T.t * T.t (* String Part *)
    | Ind of string * T.t list (* inductive predicates *)

  (* comparison function for spat atoms *)
  let compare s1 s2 = 
    let toAbstract s = 
      match s with
      | Pto(t,qq) ->
         let vvFld = List.map fst qq in
         let tt = List.map snd qq in
         let vFld = List.fold_left (fun s0 s -> s0 ^ s) "" vvFld in
         (0,vFld,tt,[])
      | Arr(t1,t2) -> (1,"",[t1;t2],[])
      | Str(t1,t2) -> (2,"",[t1;t2],[])
      | Ind(pr,tt) -> (3,pr,tt,[])
    in
    genCompare toAbstract T.compare s1 s2

  let terms s : Tset.t =
    match s with
    | Pto(t,qq) -> Tset.of_list (t::(List.map snd qq))
    | Arr(t1,t2) | Str(t1,t2) -> Tset.of_list [t1;t2]
    | Ind(_,tt) -> Tset.of_list tt
    
  (* this checks whether the given s consists of presburger terms *)
  (* If it is then do nothing, else raise the NotPresburger exception *)
  let checkPresburger s =
    match s with
    | Pto (t,cc) ->
       let tt = t :: (List.map snd cc) in
       List.iter T.checkPresburger tt
    | Arr (t1,t2)
      | Str (t1,t2) -> (T.checkPresburger t1; T.checkPresburger t2)
    | Ind (p,tt) -> List.iter T.checkPresburger tt

  let fv s = 
    match s with
    | Pto(t,gg) -> Strset.mapUnion T.fv (t::(List.map snd gg))
    | Arr(t1,t2) -> Strset.mapUnion T.fv [t1;t2]
    | Str(t1,t2) -> Strset.mapUnion T.fv [t1;t2]
    | Ind(_,tt) -> Strset.mapUnion T.fv tt
                  
  let fv_t s =
    match s with
    | Pto(t,gg) -> Tset.mapUnion Tset.fv_t (t::(List.map snd gg))
    | Arr(t1,t2) -> Tset.mapUnion Tset.fv_t [t1;t2]
    | Str(t1,t2) -> Tset.mapUnion Tset.fv_t [t1;t2]
    | Ind(_,tt) -> Tset.mapUnion Tset.fv_t tt

  let addrs (s : t) =
    match s with
    | Pto(t,cc) -> [t]
    | Arr(t,u) -> [t;u]
    | Str(t,u) -> [t;u]
    | Ind(_,tt) -> []

  let addrs_s (s : t) =
    match s with
    | Pto(t,cc) -> Tset.of_list [t]
    | Arr(t,u) -> Tset.of_list [t;u]
    | Str(t,u) -> Tset.of_list [t;u]
    | Ind(_,tt) -> Tset.empty

  let addrs_ls (s : t) =
    match s with
    | Pto(t,cc) -> Tset.of_list (t::(match List.assoc_opt "next" cc with None -> [] | Some u -> [u]))
    | Arr(t,u) -> Tset.of_list [t;u]
    | Str(t,u) -> Tset.of_list [t;u]
    | Ind(_,tt) -> Tset.empty
                 
  let hatVars s = Tset.filter T.isHatVar (fv_t s)

  let hatVars' s = Tset.filter T.isHatVar' (fv_t s)
                
  let barVars s = Tset.filter T.isBarVar (fv_t s)

  let bcdtVars s = Tset.filter T.isBCDTVar (fv_t s)

  let signVars s = Tset.filter T.isSignVar (fv_t s)

  let indirectVars s = Tset.filter T.isIndirectVar (fv_t s)
                 
  let hatVarsAddr s = Tset.hatVarsL (addrs s)
      
  let barVarsAddr s = Tset.barVarsL (addrs s)

  let bcdtVarsAddr s = Tset.bcdtVarsL (addrs s)
                     
  let signVarsAddr s = Tset.signVarsL (addrs s)

  let rec pp fmt (s: t) =
    match s with    
    | Pto(t,cc) ->
       Format.fprintf fmt "%a->(%a)" T.pp t pp_cc cc
    | Arr(t1,t2) ->
       Format.fprintf fmt "Arr(%a,%a)" T.pp t1 T.pp t2
    | Str(t1,t2) ->
       Format.fprintf fmt "Str(%a,%a)" T.pp t1 T.pp t2
    | Ind(p,[]) ->
       Format.fprintf fmt "%s" p
    | Ind(p,tt) ->
       Format.fprintf fmt "%s(%a)" p (pp_list_comma T.pp) tt
  and pp_cc fmt cc =
    let pp_f_t fmt (f,t) = Format.fprintf fmt "%s:%a" f T.pp t in
    Format.fprintf fmt "%a" (pp_list_comma pp_f_t) cc
      
  let print = Format.printf "@[%a@]" pp
    
  let println = Format.printf "@[%a@." pp

  let cells (s : t) =
    match s with
    | Pto(t,_) -> [t]
    | Arr(t,_) -> [t]
    | Str(t,_) -> [t]
    | Ind(_,_) -> []
                
  let getPtoContent (s : t) =
    match s with
    | Pto(_,cc) -> cc
    | _ -> []

  let rec getConsts (s:t) =
    match s with    
    | Pto(t,cc) -> Intset.unionL [T.getConsts t; Intset.mapUnion (fun (_,t) -> T.getConsts t) cc]
    | Arr(t1,t2) -> T.getConstsL [t1;t2]
    | Str(t1,t2) -> T.getConstsL [t1;t2]
    | Ind(_,tt) -> T.getConstsL tt
  and getConstsL ss = Intset.mapUnion getConsts ss
         
  let getPtoContentTms (s:t) = List.map snd (getPtoContent s)

  let getPtoContentTms_s (s:t) = List.fold_left (fun s (_,t) -> Tset.add t s) Tset.empty (getPtoContent s)
                               
  (* mkContentPairs [(f1:x1; f2:y1; f3:z1)] [(g2:a;f1:b;f2:c)] returns *)
  (* - [(f1,x1,b);(f2,y1,c)] *)
  let mkContentPairs cc1 cc2 =
    let compare_f c1 c2 = String.compare (fst c1) (fst c2) in
    let cc1' = List.sort compare_f cc1 in
    let cc2' = List.sort compare_f cc2 in
    let rec mkPairs res cc1a cc2a =
      match cc1a,cc2a with
      | _,[] -> res
      | [],_ -> res               
      | (f1,_)::cc1a',(f2,_)::_ when f1 < f2 -> mkPairs res cc1a' cc2a
      | (f1,_)::_,(f2,_)::cc2a' when f1 > f2 -> mkPairs res cc1a cc2a'
      | (f1,u1)::cc1a',(f2,u2)::cc2a' -> mkPairs ((u1,u2)::res) cc1a' cc2a'
    in
    mkPairs [] cc1' cc2'

  let getArraySeg (s : t) = match s with
    | Arr(t1,t2) -> [(t1,t2)]
    | _ -> []      

  let getStringSeg (s : t) = match s with
    | Str(t1,t2) -> [(t1,t2)]
    | _ -> []      

  let mkInterval (s : t) = match s with
    | Pto(t,_) -> (t,t)
    | Arr(t1,t2) -> (t1,t2)
    | Str(t1,t2) -> (t1,t2)
    | _ -> failwith "mkInterval: inductive predicate"

  let mkIntervalLs (s : t) = match s with
    | Ind(_,tt) when List.length tt = 2 ->
       let t0 = List.nth tt 0 in
       let t1 = List.nth tt 1 in
       (t0,t1)
    | Ind(_,_) -> failwith "mkIntervalLs: not binary inductive pred."
    | _ -> failwith "mkIntervalLs: not inductive pred."
         
  let getArrayLen (s : t) = match s with
    | Arr(t1,t2) -> [T.Sub[t2;t1]]
    | _ -> []

  let getStringLen (s : t) = match s with
    | Str(t1,t2) -> [T.Sub[t2;t1]]
    | _ -> []

  let rec cellSize (s : t) = match s with
    | Pto(t,_) -> one
    | Arr(t1,t2) -> (t2 -.- t1) +.+ one
    | Str(t1,t2) -> (t2 -.- t1) +.+ one
    | _ -> failwith "cellSize: inductive predicate"
       
  let varRepl repl (s : t) : t = match s with
    | Pto(t,uu) ->
      let t' = T.varRepl repl t in
      let uu' = List.map (fun (f,t) -> (f, T.varRepl repl t)) uu in
      Pto(t',uu')
    | Arr(t1,t2) ->
      let t1' = T.varRepl repl t1 in
      let t2' = T.varRepl repl t2 in
      Arr(t1',t2')
    | Str(t1,t2) ->
      let t1' = T.varRepl repl t1 in
      let t2' = T.varRepl repl t2 in
      Str(t1',t2')
    | Ind(p,tt) ->
       let tt' = List.map (T.varRepl repl) tt in
       Ind(p,tt')

  let subst sub s = match s with
    | Pto(t,uu) ->
      let t' = T.subst sub t in
      let uu' = List.map (fun (f,t) -> (f,T.subst sub t)) uu in
      Pto(t',uu')
    | Arr(t1,t2) ->
      let t1' = T.subst sub t1 in
      let t2' = T.subst sub t2 in
      Arr(t1',t2')
    | Str(t1,t2) ->
      let t1' = T.subst sub t1 in
      let t2' = T.subst sub t2 in
      Str(t1',t2')
    | Ind(p,tt) ->
       let tt' = List.map (T.subst sub) tt in
       Ind(p,tt')
       
  let nf (s : t) : t = match s with
    | Pto(t,uu) ->
      let t' = T.nf t in
      let uu' = List.map (fun (f,t) -> (f,T.nf t)) uu in
      Pto(t',uu')
    | Arr(t1,t2) ->
      let t1' = T.nf t1 in
      let t2' = T.nf t2 in
      Arr(t1',t2')
    | Str(t1,t2) ->
      let t1' = T.nf t1 in
      let t2' = T.nf t2 in
      Str(t1',t2')
    | Ind(p,tt) ->
       let tt' = List.map T.nf tt in
       Ind(p,tt')
       
  let eq s1 s2 = (nf s1) = (nf s2)
      
  let checkSan s =
    match s with
    | Pto(t,cc) -> List.iter Tset.checkSan (t :: (List.map snd cc))
    | Arr(t1,t2) | Str(t1,t2) ->
       Tset.checkSan t1;
       Tset.checkSan t2
    | Ind (_,tt) ->
       List.iter Tset.checkSan tt
  (* 
    extract_fcall _vv _eqlist Arr(f(x),z)
    returns
    Arr(##0,z)
    with
    !_vv = [x;z;##0]
    !_eqlist = [ (f(x),##0) ]
   *)
  let extract_nonPb vvv_eqlist s =
    let rec aux vvv_eqlist s =
      match s with
      | Pto (t,cc) ->
         let (vvv_eqlist1,t') = T.extract_nonPb vvv_eqlist t in
         let ff = List.map fst cc in         
         let tt = List.map snd cc in
         let (vvv_eqlist2,tt') = List_tailrec.map_state T.extract_nonPb vvv_eqlist1 tt in
         let cc' = zipLst ff tt in
         (vvv_eqlist2, Pto(t',cc'))
      | Arr (t1,t2) ->
         let (vvv_eqlist1,t1') = T.extract_nonPb vvv_eqlist  t1 in
         let (vvv_eqlist2,t2') = T.extract_nonPb vvv_eqlist1 t2 in
         (vvv_eqlist2, Arr(t1',t2'))
      | Str (t1,t2) ->
         let (vvv_eqlist1,t1') = T.extract_nonPb vvv_eqlist  t1 in
         let (vvv_eqlist2,t2') = T.extract_nonPb vvv_eqlist1 t2 in
         (vvv_eqlist2, Str(t1',t2'))
      | Ind (p,tt) ->
         let (vvv_eqlist1,tt') = List_tailrec.map_state T.extract_nonPb vvv_eqlist tt in
         (vvv_eqlist1, Ind (p,tt'))
    in
    let (vvv,eqlist) = vvv_eqlist in
    let vvv1 = Strset.union (fv s) vvv in
    aux (vvv1,eqlist) s

  let denominators s : Tset.t =
    match s with
    | Pto (t,cc) -> Tset.mapUnion Tset.denominators (t::(List.map snd cc))
    | Arr (t1,t2) | Str (t1,t2) -> Tset.mapUnion Tset.denominators [t1;t2]
    | Ind (_,tt) -> Tset.mapUnion Tset.denominators tt

  let getLsEndpoints s =
    match s with
    | Ind (ls,tt) when ls = "Ls" -> tt
    | _ -> []

  let getLsEndpoints_s s =
    match s with
    | Ind (ls,tt) when ls = "Ls" -> Tset.of_list tt
    | _ -> Tset.empty
         
  (* Just checking "next"-field *)
  let getListPtoHead s =
    match s with
    | Pto (t,cc) when List.mem "next" (List.map fst cc) -> [t]
    | _ -> []

  let isListPto s = (getListPtoHead s) <> []
                  
  let syntactical_simpl s =
    match s with
    | Pto (t,cc) ->
       let t1 = T.syntactical_simpl t in
       let cc1 = List.map (fun (f,u) -> (f,T.syntactical_simpl u)) cc in
       Pto (t1,cc1)
    | Arr (t,u) ->
       let t1 = T.syntactical_simpl t in
       let u1 = T.syntactical_simpl u in
       Arr (t1,u1)
    | Str (t,u) ->
       let t1 = T.syntactical_simpl t in
       let u1 = T.syntactical_simpl u in
       Str (t1,u1)
    | Ind (name,tt) ->
       let tt1 = List.map T.syntactical_simpl tt in
       Ind (name,tt1)
       
end
;;

(* Short cuts for SHspatExps *)
module S = SHspatExp;;
let arr(t1,t2) = S.Arr(t1,t2);;
let str(t1,t2) = S.Str(t1,t2);;
let ( -.> ) t cc = S.Pto(t,cc);;
  


module SHspat = struct
  (* 'ss' is used for them		*)
  type t = SHspatExp.t list

  let checkPresburger ss = List.iter S.checkPresburger ss

  let terms (ss: t) : Tset.t = Tset.mapUnion S.terms ss
                         
  let fv (ss : t) = Strset.mapUnion S.fv ss

  let fv_t (ss : t) = Tset.mapUnion S.fv_t ss

  let pp = pp_list "Emp" " * " S.pp

  let print = Format.printf "@[%a@]" pp
            
  let println = Format.printf "@[%a@." pp
              
  let cells (ss : t) = unionL (List.map S.cells ss)

  let addrs (ss : t) = unionL (List.map S.addrs ss)
	  
  let split (ss : t) =
    let rec splitRec ptos arys strs inds ss1 =
      match ss1 with
      | [] -> (List.rev ptos,List.rev arys,List.rev strs,List.rev inds)
      | s'::ss' ->
	     match s' with
	     | S.Pto(_,_) -> splitRec (s'::ptos) arys strs inds ss'
	     | S.Arr(_,_) -> splitRec ptos (s'::arys) strs inds ss'
	     | S.Str(_,_) -> splitRec ptos arys (s'::strs) inds ss'
         | S.Ind(_,_) -> splitRec ptos arys strs (s'::inds) ss'
    in splitRec [] [] [] [] ss

  let getArraySeg (ss : t) = 
    List.concat (List.map SHspatExp.getArraySeg ss)

  let getStringSeg (ss : t) = 
    List.concat (List.map SHspatExp.getStringSeg ss)

  let mkSegment (ss : t) = List.map S.mkInterval ss
    
  let cellSize (ss : t) =
    T.Add (List.map SHspatExp.cellSize ss)
      
  let getArrayLen (ss : t) =
    List.concat (List.map SHspatExp.getArrayLen ss)

  let getStringLen (ss : t) =
    List.concat (List.map SHspatExp.getStringLen ss)
    
  let varRepl repl (ss : t) : t =
    List.map (SHspatExp.varRepl repl) ss

  let spat_length ss = List.length ss 
      
  let subst (sub : Subst.t) (ss : t) : t =
    List.map (SHspatExp.subst sub) ss

  let nf (ss : t) : t =
    List.map SHspatExp.nf ss

  let checkSan (ss : t) = List.iter S.checkSan ss

  let hatVars = Tset.mapUnion S.hatVars

  let hatVars' = Tset.mapUnion S.hatVars'

  let barVars = Tset.mapUnion S.barVars

  let bcdtVars = Tset.mapUnion S.bcdtVars
    
  let signVars = Tset.mapUnion S.signVars
                        
  let hatVarsAddr = Tset.mapUnion S.hatVarsAddr

  let barVarsAddr = Tset.mapUnion S.barVarsAddr

  let bcdtVarsAddr = Tset.mapUnion S.bcdtVarsAddr

  let signVarsAddr = Tset.mapUnion S.signVarsAddr

  (* checkTypeConsistency ss *)
  (* It checks that ss has a consistent typeinfo as one memory block *)
  (* That is, ss should have the same type *)
  let checkTypeConsistency (ss : t) =
    let tt = mapAppend_rev S.addrs ss in
    T.checkTypeInfo (Attrs.mapUnion T.getAttrs tt) 

  let extract_nonPb vvv_eqlist ss = List_tailrec.map_state S.extract_nonPb vvv_eqlist ss

  let denominators ss : Tset.t = Tset.mapUnion S.denominators ss
    
  (* Splitting of spatial part *)
  (* (ssArr,ssLs) *)
  (* Ex. Arr(x,y)*Ls(a,b) becomes (Arr(x,y),Ls(x,y))  *)
  let splitArrayList (ss : t) : t * t = 
    let (ssPto,ssArr,ssStr,ssLs) = split ss in
    let (ssLsPto,ssArrPto) = List_tailrec.splitLst S.isListPto ssPto in
    let ssArr1 = ssArrPto @ ssArr @ ssStr in
    let ssLs1 = ssLsPto @ ssLs in
    (ssArr1,ssLs1)

  let splitPtoArrayList (ss : t) : t * t * t =
    let (ssPto,ssArr,ssStr,ssLs) = split ss in
    (ssPto,ssArr@ssStr,ssLs)
    
  let syntactical_simpl ss = List.map S.syntactical_simpl ss
    
end
;;

module SS = SHspat
;;


(* Hat variable conditions *)
(* (1) hat variables are positive *)
(* (2) different hat variable terms are incompatible *)
(* Idea: order of hat variables [x@hat;y@hat;z@hat] *)
(* Create a condition accoring to this order, for example, 0< x@hat < x@hat+3 < y@hat < y@hat+10 < z@hat *)
let mkHatCond pp ss1 ss2 =
  let hatVars = Tset.union (Tset.mapUnion S.hatVars' (List.rev_append ss1 ss2)) (Tset.mapUnion P.hatVars' pp) in
  let orderHatVars = Tset.elements hatVars in
  let tttPP = Tset.mapUnion P.terms pp in
  let tttSS = Tset.mapUnion S.terms (List.rev_append ss1 ss2) in
  let ttt = Tset.union tttPP tttSS in  
  let consts = Intset.unionL [P.getConstsL pp; S.getConstsL ss1; S.getConstsL ss2; Intset.singleton 0] in
  let consts' = Intset.filter (fun n -> n < 10000000000) consts in (* remove the limit constant *)
  let maxNum = Intset.max_elt consts' in (* get the largest constant *)
  let rec mkHatCond pp order ttt =
    match order with
    | a::b::order1 ->
       let aaa' = Tset.filter (fun t -> List.mem a (T.getHeadTerm t)) ttt in
       let ttt' = Tset.diff ttt aaa' in
       let pp' = Tset.fold (fun a' pp -> (a' <.< b)::pp) aaa' pp in
       mkHatCond pp' (b::order1) ttt'
    | _ -> pp
  in
  match orderHatVars with
  | [] -> []
  | _ -> (T.Int maxNum <.< List.hd orderHatVars)::(mkHatCond [] orderHatVars ttt)
;;

(*------------------------------*)
(* Symbolic Heaps				*)
(*------------------------------*)
module SH = struct
(* 'h' is used for them			*)

  (* (vv,ppp,ss) means (Ex vvv.(pb & ss) *)
  type t = Strset.t * SHpure.t * SHspat.t 

  let vars (h: t) = fst3 h
  let pure (h: t) = snd3 h
  let spat (h: t) = thd3 h
                         
  let terms h : Tset.t = Tset.union (P.terms (pure h)) (SS.terms (spat h))
         
  let checkPresburger (h: t) = P.checkPresburger (pure h); SS.checkPresburger (spat h)

  let pp fmt (h : t) =
    let (vvv,p,ss) = h in
    let ex_vv =
      if Strset.is_empty vvv then ""
      else Fmt.asprintf "Ex %a. " (pp_list_comma pp_string) (Strset.elements vvv)
    in
    Format.fprintf fmt "%s%a && %a" ex_vv SS.pp ss P.pp p

  let print = Format.printf "@[%a@]" pp 
    
  let println = Format.printf "@[%a@." pp 

  let av (h : t) =
    let (vvv,p,ss) = h in
    let vvv1 = Strset.union (P.fv p) (SS.fv ss) in
    Strset.union vvv vvv1

  let bv (h : t) = let (vvv,_,_) = h in vvv

  let fv (h : t) = Strset.diff (av h) (bv h)

  let of_spat (h : t)  = thd3 h

  let of_pure (h : t)  = snd3 h

  let cells (h : t) = SS.cells (of_spat h)

  let varRepl repl (h : t) : t =
    let (vvv,p,ss) = h in
    let p1 = SHpure.varRepl repl p in
    let ss1 = SHspat.varRepl repl ss in
    (vvv,p1,ss1)

  let spat_length (h : t) =
    let (_,_,ss) = h in
    SS.spat_length ss
      
  (* alpha_conv vvvAvoid ({x,y},Pi,Sg)			*)
  (* it produces fresh variables x' and y'		*)
  (* where x' and y' are fresh for vvvAvoid		*)
  (* Then returns ({x',y'},Pi[x'/x,y'/y],Sg[x'/x,y'/y])	*)
  let alpha_conv vvvAvoid (h : t) : t = 
    let (vvvEx,p,ss) = h in
    let rec alp_conv1 vvRes vv p1 ss1 = 
      match vv with
      | [] -> (Strset.of_list vvRes,p1,ss1)
      | v::vv1 ->
	     match Strset.mem v vvvAvoid with
         | false -> alp_conv1 (v::vvRes) vv1 p1 ss1
         | true  -> 
	        let v' = Strset.genFresh v vvvAvoid in
	        let p2 = P.varRepl [(v,v')] p1 in
	        let ss2 = SS.varRepl [(v,v')] ss1 in
	        alp_conv1 (v'::vvRes) vv1 p2 ss2
    in alp_conv1 [] (Strset.elements vvvEx) p ss
     
  let subst (sub : Subst.t) (h : t) =
    let vvvFV = fv h in
    let sub' = List.filter (fun (v,_) -> Strset.mem v vvvFV) sub in
    let tt = List.map snd sub' in
    let vvvAvoid = Strset.mapUnion T.fv tt in
    let (vvv1,p1,ss1) = alpha_conv vvvAvoid h in
    let p2 = P.subst sub' p1 in
    let ss2 = SS.subst sub' ss1 in
    (vvv1,p2,ss2)

  let nf (h : t) : t =
    let (vvv,p,ss) = h in
    let p' = P.normalizeTerms p in
    let ss' = SS.nf ss in
    (vvv,p',ss')

  let extract_fcall vvv_eqlist (h : t) =
    let (vvv,p,ss) = h in
    let (vvv0,eqlist0) = vvv_eqlist in
    let vvv_eqlist1 = (Strset.union vvv vvv0, eqlist0) in
    let (vvv_eqlist2,p') = P.extract_nonPb vvv_eqlist1 p in
    let (vvv_eqlist3,ss') = SS.extract_nonPb vvv_eqlist2 ss in
    let h' = (vvv,p',ss') in
    (vvv_eqlist3,h')

end
;;

(*--------------------------------------*)
(* Quantifier-Free Symbolic Heaps		*)
(*--------------------------------------*)
module QFSH = struct
  (* 'k' is used for them	*)
  (* (p,ss) means (p & ss) *)
  type t = SHpure.t * SHspat.t 

  let up (k : t) : SH.t = let (p,ss) = k in (Strset.empty,p,ss)

  let down (h : SH.t) : t = let (_,p,ss) = h in (p,ss)    

  let upfunc f = fun k -> f (up k)

  let terms = upfunc SH.terms
  let pp fmt = upfunc (SH.pp fmt)
  let print = Format.printf "@[%a@]" pp
  let println = Format.printf "@[%a@." pp            
  let av = upfunc SH.av
  let bv = upfunc SH.bv
  let fv = upfunc SH.fv
  let of_spat = upfunc SH.of_spat
  let of_pure = upfunc SH.of_pure
  let spat_length = upfunc SH.spat_length
  let cells = upfunc SH.cells
  let subst sub k = down (SH.subst sub (up k))
  let nf k = down (SH.nf (up k))

  let checkPresburger k =
    let (p,ss) = k in
    P.checkPresburger p;
    SS.checkPresburger ss
           
  let getArrayLen (k : t) =
    let (_,ss) = k in
    SHspat.getArrayLen ss

  let isPtoHeadForm (k : t) =
    let (_,s) = k in
    match s with
    | S.Pto(_,_)::_ -> true
    | _ -> false

  let isArrHeadForm (p,s) =
    match s with
    | S.Arr(_,_)::_ -> true
    | _ -> false

  let extract_nonPb vvv_eqlist (k : t) =
    let (p,ss) = k in
    let (vvv_eqlist1,p') = P.extract_nonPb vvv_eqlist p in
    let (vvv_eqlist2,ss') = SS.extract_nonPb vvv_eqlist1 ss in
    let k' = (p',ss') in
    (vvv_eqlist2,k')

  let update_checkSan (k : t) =
    let (p,ss) = k in
    let p' = P.update_checkSan p in
    try
      SS.checkSan ss;
      (p',ss)
    with
      NotSanitary -> (P.False,[])
                   
end
;;

(* Module of Multi-conclusion Entailments *)  
module Entl = struct

(* Entailment has the form sh1 |- sh21 | sh22 | ... | sh2m *)
(* Basically, the quantifier-part of lhs is assumed to be empty *)
(* ([],P,S) |- (v1,P1,S1),...,(vn,Pn,Sn)	*)
(* 'e' is used for them *)

  type t = SH.t * SH.t list

  let pp fmt (e : t) = Format.fprintf fmt "%a |- %a" SH.pp (fst e) (pp_list "" " | " SH.pp) (snd e)
                     
  let print = Format.printf "@[%a@]" pp

  let println = Format.printf "@[%a@." pp

  let alpha_conv (e : t) : t =
    let (h,hh) = e in
    let rec alpha_convL rest hh1 =
      match hh1,rest with
      | [],h2::hh2 -> (h2,hh2)
      | [],_ -> failwith "alpha_conv"
      | h3::hh3,_ ->
	     let vvvAV = Strset.mapUnion SH.av (List.rev_append rest hh3) in
	     let vvvAvoid = Strset.union vvvAV (SH.fv h3) in
	     let h4 = SH.alpha_conv vvvAvoid h3 in
	     alpha_convL (h4::rest) hh3
    in alpha_convL [] (List.rev_append hh [h])

  let size (e : t) =
    let (h,hh) = e in
    let n = SH.spat_length h in
    let nn = List.map SH.spat_length hh in
    (n,nn)

  let string_of_size (e : t) =
    let (n,nn) = size e in
    let v = string_of_int n in
    let vv = string_of_list string_of_int "," nn in
    "("^v^", ["^vv^"])"
    
  let nf (e : t) : t =
    let (h,hh) = e in
    let h1 = SH.nf h in
    let hh1 = List.map SH.nf hh in
    alpha_conv (h1,hh1)
    
end
;;

(* Module of QF Multi-conclusion Entailments *)  
module QFEntl = struct
    
  type t = QFSH.t * QFSH.t list
    
  let up (e : t) =
    let (k,kk) = e in
    let h = QFSH.up k in
    let hh = List.map QFSH.up kk in
    (h,hh)

  let down (e : Entl.t) : t =
    let (h,hh) = e in
    let k = QFSH.down h in
    let kk = List.map QFSH.down hh in
    (k,kk)    

  let upfunc f = fun k -> f (up k)

  let size = upfunc Entl.size
  let pp fmt = upfunc (Entl.pp fmt)
  let print = Format.printf "@[%a@]" pp
  let println = Format.printf "@[%a@." pp
  let nf = upfunc Entl.nf

end
;;

module SHinterval = struct
  (* 'j' is used *)
  type t = SHterm.t * SHterm.t

  let checkPresburger j =
    let (t1,t2) = j in
    T.checkPresburger t1;
    T.checkPresburger t2

  let create t0 t1 = (t0,t1)
  let left (j : t) = fst j
  let right (j : t) = snd j

  let pp fmt (j : t) = Format.fprintf fmt "(%a,%a)" T.pp (fst j) T.pp (snd j)
                     
  let print = Format.printf "@[%a@]" pp
              
  let println = Format.printf "@[%a@." pp
                   
end
;;
module Invl = SHinterval
;;
module Segments = struct
  (* 'jj' is used *)
  type t = Invl.t list

  let checkPresburger jj = List.iter Invl.checkPresburger jj

  let pp fmt = Format.fprintf fmt "[%a]" (pp_list_comma Invl.pp)
             
  let print = Format.printf "@[%a@]" pp
               
  let println = Format.printf "@[%a@." pp
                 
end
;;                
module Seg = Segments
;;


(*------------------------------*)
(* Manual Input         		*)
(*------------------------------*)
module MIfunctionIO = struct

  (* s = [(x,x@bar);(y,14);(z,a@hat+1)] *)
  type store = (string * SHterm.t) list

  (* tp is Attrs.t *)
  (* {} is int, void, etc *)
  (* {STRUCT "foo"} is struct foo *)
  (* {STRUCT "foo";PTR} is struct foo* *)
  (* (return-type,funcname,[(x1,types)]) *)
  type tp = Attrs.t
  type fproto = tp * string * (string * tp) list
             
  (* ret = (r,s,d,A,B) *)
  (* r:return value, s:store, d:branch, A:post, B:missing *)
  type return = T.t * store * P.t * QFSH.t * QFSH.t 
    
  type t =
    {
      mutable rawfunc : string;
      mutable func: fproto list; (* [] or [func-prototype]. This is filled after parsing rawfunc *)
      mutable s : store;
      mutable d : SHpure.t;
      mutable sh : QFSH.t;
      mutable ret : return list
    }

  let pp_funproto fmt (func: fproto list) =
    match func with
    | [] -> ()
    | (rettypes,fname,params)::_ ->
       let pp_param1 fmt (x,tp) = Format.fprintf fmt "%s<%a>" x Attrs.pp tp in
       Format.fprintf fmt "%a %s (%a)" Attrs.pp rettypes fname (pp_list_comma pp_param1) params
    
  let pp_store fmt (s : store) =
    let pp1 fmt (v,t) = Format.fprintf fmt "%s=%a" v T.pp t in
    Format.fprintf fmt "[%a]" (pp_list_comma pp1) s

  let pp_return fmt (ret : return) =
    let (r,s,d,sh1,sh2) = ret in    
    Format.fprintf fmt "(%a,%a,%a,%a,%a)" T.pp r pp_store s P.pp d QFSH.pp sh1 QFSH.pp sh2

  let pp fmt f =
    Format.fprintf fmt "FuncName: %a\n" pp_funproto f.func;
    Format.fprintf fmt "Input: \n";
    Format.fprintf fmt "s: %a\n" pp_store f.s;
    Format.fprintf fmt "d: %a\n" P.pp f.d;
    Format.fprintf fmt "A: %a\n" QFSH.pp f.sh;
    Format.fprintf fmt "Output: \n";
    Format.fprintf fmt "%a" (pp_list_newline pp_return) f.ret

  let print = Format.printf "@[%a@]" pp
               
  let println = Format.printf "@[%a@." pp
    
end
;;

module MIfile = struct

  type t = MIfunctionIO.t list
         
  module FunIO = MIfunctionIO
           
  let pp = pp_list_newline FunIO.pp
    
  let print = Format.printf "@[%a@]" pp
               
  let println = Format.printf "@[%a@." pp
                 
end
;;


(*------------------------------*)
(* Some other short-cuts		*)
(*------------------------------*)
let trueSH : SH.t = (Strset.empty,P.True,[]);;

(* list_bfilter [1;2;3] [t;f;t] returns [1;3] *)
let list_bfilter xx bfilter =
  let bx = List.filter (fun (b,_) -> b) (zipLst bfilter xx) in
  List.map (fun (_,y) -> y) bx
;;

(* mapFilter f [2;3;4] [t;f;t] makes [f2;f4]	*)
let mapFilter f xx bfilter =
  let xx1 = list_bfilter xx bfilter in
  List.map f xx1
;;

(* mapEqFilter x [y;z;w] [t;f;t] makes [x=y;x=w]	*)
let mapEqFilter t = mapFilter (fun x -> t =.= x);;

(* mapLtFilter x [y;z;w] [t;f;t] makes [x<y;x<w]	*)
let mapLtFilter t = mapFilter (fun x -> t <.< x);;







