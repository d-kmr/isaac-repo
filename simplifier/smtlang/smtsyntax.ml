open Notations
open PrintTools   
open Tools

module Logic = struct
  (* Logic is not used actually because Z3 tries to detect appropreate logic automatically *)
  (* See https://github.com/Z3Prover/z3/blob/master/src/tactic/portfolio/default_tactic.cpp *)
  (*     https://github.com/Z3Prover/z3/issues/1035#issuecomment-303160975 *)
  type t =
  | AUFLIA | AUFLIRA | AUFNIRA
  | LIA | LRA
  | QF_ABV | QF_AUFBV | QF_AUFLIA | QF_AX | QF_BV | QF_IDL
  | QF_LIA | QF_LRA | QF_NIA | QF_NRA | QF_RDL
  | QF_UF | QF_UFBV| QF_UFIDL | QF_UFLIA | QF_UFLRA | QF_UFNRA
  | UFLRA | UFNIA
    
  let pp fmt logic =
    match logic with
    | AUFLIA -> Fmt.fprintf fmt "AUFLIA"
    | AUFLIRA -> Fmt.fprintf fmt "AUFLIRA"
    | AUFNIRA -> Fmt.fprintf fmt "AUFNIRA"
    | LIA -> Fmt.fprintf fmt "LIA"
    | LRA -> Fmt.fprintf fmt "LRA"
    | QF_ABV -> Fmt.fprintf fmt "QF_ABV"
    | QF_AUFBV -> Fmt.fprintf fmt "QF_AUFBV"
    | QF_AUFLIA -> Fmt.fprintf fmt "QF_AUFLIA"
    | QF_AX -> Fmt.fprintf fmt "QF_AX"
    | QF_BV -> Fmt.fprintf fmt "QF_BV"
    | QF_IDL -> Fmt.fprintf fmt "QF_IDL"
    | QF_LIA -> Fmt.fprintf fmt "QF_LIA"
    | QF_LRA -> Fmt.fprintf fmt "QF_LRA"
    | QF_NIA -> Fmt.fprintf fmt "QF_NIA"
    | QF_NRA -> Fmt.fprintf fmt "QF_NRA"
    | QF_RDL -> Fmt.fprintf fmt "QF_RDL"
    | QF_UF -> Fmt.fprintf fmt "QF_UF"
    | QF_UFBV -> Fmt.fprintf fmt "QF_UFBV"
    | QF_UFIDL -> Fmt.fprintf fmt "QF_UFIDL"
    | QF_UFLIA -> Fmt.fprintf fmt "QF_UFLIA"
    | QF_UFLRA -> Fmt.fprintf fmt "QF_UFLRA"
    | QF_UFNRA -> Fmt.fprintf fmt "QF_UFNRA"
    | UFLRA -> Fmt.fprintf fmt "UFLRA"
    | UFNIA -> Fmt.fprintf fmt "UFNIA"
             
end
;;

module Sort = struct
  
  type t = Name of string | App of string * t list
  type sub = (string * t) list

  let rec pp fmt s =
    match s with
    | Name s -> Fmt.fprintf fmt "%s" s
    | App(hd,sorts) -> Fmt.fprintf fmt "(%s %a)" hd (pp_list_space pp) sorts

  let print = Fmt.printf "@[%a@]" pp
            
  let println = Fmt.printf "@[%a@." pp
                     
  let rec subst (sb : sub) s = match s with
    | Name v as q ->
       begin
         try
	       List.assoc v sb 
         with Not_found -> q
       end
    (* | BV n -> BV n *)
    | App(hd,sorts) ->
       let sorts' = List.map (subst sb) sorts in
       App(hd,sorts')

  let rec ctxSortSub (p,vars,s) sort =
    match sort with
    | Name _ as q -> q
    (* | BV _ as q -> q *)
    | App(q,sorts) when q = p ->
      let sorts' = List.map (ctxSortSub (p,vars,s)) sorts in
      let sub = zipLst vars sorts' in
      subst sub s
    | App(q,sorts) ->		(* when q <> p *)
      let sorts' = List.map (ctxSortSub (p,vars,s)) sorts in
      App(q,sorts')
	
end
;;

module Keyword = struct

  type t = K0 of string | K1 of string
  (* K0 "abc" comes from ":abc" *)
  (* K1 "abc" comes from  "abc" *)

  let pp fmt kw =
    match kw with
    | K0 kwd -> Fmt.fprintf fmt ":%s" kwd
    | K1 kwd -> Fmt.fprintf fmt "%s" kwd
end
;;

module Exp = struct

(* About App
   Usage: App(op,[t1;t2]) 
   Supported op (ZA=Z3.Arithmetic, ZB=Z3.Boolean, ZV=Z3.BitVector)

   BitVector-mode
   "+" --> ZV.mk_add
   "-" --> ZV.mk_sub
   "*" --> ZV.mk_mul
   "/" --> ZV.mk_sdiv (signed division)
   "mod" --> ZV.mk_smod (signed mod)
   "<"   --> ZV.mk_slt  (signed less than)
   "<="  --> ZV.mk_sle  (signed less than or equal)
   ">"   --> ZV.mk_sgt  (signed greater than)
   ">="  --> ZV.mk_sge  (signed greater than or equal)
   "<<" --> ZV.mk_shl
   ">>" --> ZV.mk_shr
   "band" --> ZV.mk_and (bitwise and)
   "bor"  --> ZV.mk_or  (bitwise or)
   "bxor"  --> ZV.mk_xor  (bitwise xor)
   "bnot" --> ZV.mk_not (bitwise not)

   Arithmetic-mode
   "+"    --> ZA.mk_add
   "-"    --> ZA.mk_sub/ZA.mk_unary_minus
   "*"    --> ZA.mk_mul
   "mod"  --> ZA.mk_mod
   "="    --> ZA.mk_eq
   "distinct" --> ZA.mk_distinct
   "<"    --> ZA.mk_lt
   ">"    --> ZA.mk_gt
   "<="   --> ZA.mk_le
   ">="   --> ZA.mk_ge

   Common
   "imp"  --> ZB.mk_implies
   "and"  --> ZB.mk_and
   "or"   --> ZB.mk_or
   "not"  --> ZB.mk_not
 *)

  type domain = Nat | Int
                    
  type t =
    | Int of int
    | PosInf
    | NegInf
    | Var of string
    | App of string * t list
    | All of domain * Strset.t * t
    | Ex  of domain * Strset.t * t
    | Let of (string * t) list * t
    | Att of t * attriv list
  and attriv = Keyword.t * t list

  type sub = (string * t) list

  let pp_domain fmt dom =
    match dom with
    | Nat -> Fmt.fprintf fmt "nat"
    | Int -> Fmt.fprintf fmt "int"
           
  (* Pretty-printing in smt2-format *)           
  let rec pp_smt2 fmt exp =
    match exp with
    | Var v -> Fmt.fprintf fmt "%s" v
    | Int n -> Fmt.fprintf fmt "%d" n
    | PosInf -> Fmt.fprintf fmt "PosInf"
    | NegInf -> Fmt.fprintf fmt "NegInf"
    | App(func,args) -> Fmt.fprintf fmt "(%s %a)" func (pp_list_space pp_smt2) args
    | All(dom,vvv,e) -> Fmt.fprintf fmt "(forall-%a(%a) %a)" pp_domain dom (Strset.pp ",") vvv pp_smt2 e
    | Ex(dom,vvv,e) -> Fmt.fprintf fmt "(exists-%a(%a) %a)" pp_domain dom (Strset.pp ",") vvv pp_smt2 e
    | Let(binds,e) ->
       let pp_bind fmt (v,e) = Fmt.fprintf fmt "(%s,%a)" v pp_smt2 e in
       Fmt.fprintf fmt "(let %a %a)" (pp_list_space pp_bind) binds pp_smt2 e
    | Att(e,attrs) -> Fmt.fprintf fmt "(Attr %a %a)" pp_smt2 e (pp_list_space pp_attr) attrs
  and pp_attr fmt (kw,exps) = Fmt.fprintf fmt "%a %a" Keyword.pp kw (pp_list_space pp_smt2) exps
                            
  (* Pretty-printing in a user-friendly format *)           
  let rec pp fmt exp =
    match exp with
    | Var v -> Fmt.fprintf fmt "%s" v
    | Int n -> Fmt.fprintf fmt "%d" n
    | PosInf -> Fmt.fprintf fmt "+INF"
    | NegInf -> Fmt.fprintf fmt "-INF"
    | App(func,args) -> Fmt.fprintf fmt "(%s %a)" func (pp_list_space pp) args
    | All(dom,vvv,e) -> Fmt.fprintf fmt "∀%a:%a(%a)" (Strset.pp ",") vvv pp_domain dom pp e
    | Ex(dom,vvv,e) -> Fmt.fprintf fmt "∃%a:%a(%a)" (Strset.pp ",") vvv pp_domain dom pp e
    | Let(binds,e) ->
       let pp_bind fmt (v,e) = Fmt.fprintf fmt "(%s,%a)" v pp e in
       Fmt.fprintf fmt "Let\n%a\nin\n%a" (pp_list_space pp_bind) binds pp e
    | Att(e,attrs) -> Fmt.fprintf fmt "Attr(%a,%a)" pp e (pp_list_space pp_attr) attrs
  and pp_attr fmt (kw,exps) = Fmt.fprintf fmt "%a %a" Keyword.pp kw (pp_list_space pp) exps
                            
  let print = Fmt.printf "@[%a@]" pp

  let println = Fmt.printf "@[%a@." pp
                                   
  let rec fv e =
    match e with
    | Int _ | PosInf | NegInf -> Strset.empty
    | Var v -> Strset.singleton v
    | App(_,exps) -> Strset.mapUnion fv exps
    | All(_,vvv,exp) -> Strset.filter (fun x -> not(Strset.mem x vvv)) (fv exp)
    | Ex (_,vvv,exp) -> Strset.filter (fun x -> not(Strset.mem x vvv)) (fv exp)
    | Let(binds,exp) ->
       let vars = List.map fst binds in       
       let vvv0 = Strset.filter (fun x -> not(List.mem x vars)) (fv exp) in
       let vvv1 = Strset.mapUnion (fun (_,e) -> fv e) binds in
       Strset.union vvv0 vvv1
    | Att(exp,atts) ->
       let vvvAtts = Strset.mapUnion (fun (_,ee) -> Strset.mapUnion fv ee) atts in
       Strset.union vvvAtts (fv exp)

  let fv' e = Strset.elements (fv e)
     
  let rec fbv e =
    match e with
    | Int _ | PosInf | NegInf -> Strset.empty
    | Var v -> Strset.singleton v
    | App(_,exps) -> Strset.mapUnion fbv exps
    | All(_,vvv,exp) -> Strset.union vvv (fbv exp)
    | Ex (_,vvv,exp) -> Strset.union vvv (fbv exp)
    | Let(binds,exp) ->
       let vvv1 = Strset.mapUnion (fun (x,e) -> Strset.add x (fbv e)) binds in
       Strset.union (fbv exp) vvv1
    | Att(exp,atts) ->
       let vvvAtts = Strset.mapUnion (fun (_,ee) -> Strset.mapUnion fbv ee) atts in
       Strset.union  vvvAtts (fbv exp)

  (* hasInf checks whether exp contains PosInf/NegInf *)
  let rec hasInf e = 
    match e with
    | PosInf -> (true,false)
    | NegInf -> (false,true)
    | Int _ -> (false,true)
    | Var _ -> (false,true)
    | App(_,ee) -> hasInfL ee
    | All(_,_,exp) -> hasInf exp
    | Ex (_,_,exp) -> hasInf exp
    | Att(exp,_) -> hasInf exp
    | Let(binds,exp) -> hasInfL (e::(List.map snd binds))
    and hasInfL ee = 
      List.fold_left
        (fun (b1,b2) e -> let (b1',b2')=hasInf e in (b1||b1',b2||b2'))
        (false,false)
        ee
       
  let rec subst0 repl exp =
    let subst0_att rp (kw,exps) = (kw,List.map (subst0 rp) exps) in
    match exp with
    | Int _ | PosInf | NegInf -> exp
    | Var v ->
       begin
	     try
	       Var (List.assoc v repl)
	     with Not_found -> exp
       end
    | App(f,args) ->
       let args' = List.map (subst0 repl) args in
       App(f,args')
    | All(dom,vvv,exp) ->
       let repl' = List.filter (fun (x,_) -> not(Strset.mem x vvv)) repl in
       let exp' = subst0 repl' exp in
       All(dom,vvv,exp')
    | Ex(dom,vvv,exp) ->
       let repl' = List.filter (fun (x,_) -> not(Strset.mem x vvv)) repl in
       let exp' = subst0 repl' exp in
       Ex(dom,vvv,exp')
    | Let(binds,exp) ->
       let binds' = List.map (fun (v,e)-> (v,(subst0 repl e))) binds in
       let vs = List.map (fun (v,_)->v) binds in
       let repl' = List.filter (fun (x,_) -> not(List.mem x vs)) repl in
       let exp' = subst0 repl' exp in
       Let(binds',exp')
    | Att(exp,atts) ->
       let exp' = subst0 repl exp in
       let atts' = List.map (subst0_att repl) atts in
       Att(exp',atts')

  let rec subst1 sub vvvUsed exp =
    let rec mk_vlist vvvAvoid vvvUsed vvv =
      match Strset.elements vvv with
      | [] -> (Strset.empty,[])
      | v::vv1 ->
	     if Strset.mem v vvvAvoid then
	       let v' = Strset.genFresh "v" vvvUsed in
	       let vvvUsed' = Strset.add v' vvvUsed in
	       let (vvv2,sub) = mk_vlist vvvAvoid vvvUsed' (Strset.of_list vv1) in
	       (Strset.add v' vvv2, (v,v')::sub)
	     else
	       let (vvv2,sub) = mk_vlist vvvAvoid vvvUsed (Strset.of_list vv1) in
	       (Strset.add v vvv2, sub)
    in
    let subst1_att sb vvvUsd (kw,ee) = (kw,List.map (subst1 sb vvvUsd) ee) in
    match exp with
    | Int _ | PosInf | NegInf -> exp
    | Var v  -> (try List.assoc v sub with Not_found -> exp)
    | App(f,args) ->
       let args' = List.map (subst1 sub vvvUsed) args in
       App(f,args')
    | All(dom,vvv,e) ->
       let vvvAvoid = Strset.mapUnion (fun (_,e)-> fv e) sub in
       let vvvUsed' = Strset.unionL [fbv e; vvv; vvvUsed] in
       let (vvv',repl) = mk_vlist vvvAvoid vvvUsed' vvv in
       let e' = subst0 repl e in
       let sub' = List.filter (fun (x,_)-> not(Strset.mem x vvv)) sub in
       let e'' = subst1 sub' vvvUsed' e' in
       All(dom,vvv',e'')
    | Ex(dom,vvv,e) ->
       let vvvE = fbv e in
       let vvvAvoid = Strset.mapUnion (fun (_,e)-> fv e) sub in
       let vvvUsed' = Strset.unionL [vvvE;vvv;vvvUsed] in
       let (vvv',repl) = mk_vlist vvvAvoid vvvUsed' vvv in
       let e' = subst0 repl e in
       let sub' = List.filter (fun (x,_)-> not(Strset.mem x vvv)) sub in       
       let e'' = subst1 sub' vvvUsed' e' in       
       Ex(dom,vvv',e'')
    | Let(binds,e) ->
       let vv = List.map fst binds in
       let vvv = Strset.of_list vv in       
       let ee = List.map snd binds in
       let vvvAvoid = Strset.mapUnion (fun (_,e)->fv e) sub in
       let vvvUsed' = Strset.unionL [fbv e; vvv; vvvUsed] in
       let (vvv',repl) = mk_vlist vvvAvoid vvvUsed' vvv in      
       let e' = subst0 repl e in
       let sub' = List.filter (fun (x,_)-> not(Strset.mem x vvv)) sub in 
       let e'' = subst1 sub' vvvUsed' e' in
       let vv' = List.map (fun v -> List.assoc v repl) vv in
       let binds' = zipLst vv' ee in
       Let(binds',e'')
    | Att(e,atts) ->
       let e' = subst1 sub vvvUsed e in
       let atts' = List.map (subst1_att sub vvvUsed) atts in
       Att(e',atts')

  let subst (sb : sub) e =
    let vvv = Strset.mapUnion (fun (_,e) -> fbv e) sb in
    subst1 sb vvv e

  let rec ctxSortSub csub exp = 
    match exp with
    | Int _ | PosInf | NegInf | Var _ -> exp
    | App(f,args) ->
      let args' = List.map (ctxSortSub csub) args in
      App(f,args')
    | All(dom,vv,exp) ->
      let exp' = ctxSortSub csub exp in
      All(dom,vv,exp')
    | Ex(dom,vv,exp) ->
      let exp' = ctxSortSub csub exp in
      Ex(dom,vv,exp')
    | Let(binds,exp) ->
      let binds' = List.map (fun (v,e)-> (v,ctxSortSub csub e)) binds in
      let exp' = ctxSortSub csub exp in
      Let(binds',exp')
    | Att(exp,atts) ->
      let exp' = ctxSortSub csub exp in
      let atts' = List.map (ctxSortSub_att csub) atts in
      Att(exp',atts')
  and ctxSortSub_att csub (kw,exps) =
    let exps' = List.map (ctxSortSub csub) exps in
    (kw,exps')

end
;;

module Command = struct

  type t =
  | DecVar of string * Sort.t
  (* (declare-var <sym> <sort>) *)
  | DecCons of string * Sort.t
  (* (declare-const <sym> <sort>) *)
  | DecFn of string * Sort.t list * Sort.t	
  (* (declare-fun <sym> <sort>* <sort>) *)
  | DecFns of (string * Sort.t list) list
  (* (declare-funs ( <sym> <sort>* )* *)
  | DefFn of string * (string * Sort.t) list * Sort.t * Exp.t
  (* (define-fun <sym> (<sym> <sort>)* <sort> <exp>) *)
  | DecSt of string * int
  (* (declare-sort <sym> <num>?) *)
  (* (declare-sort <sym>) is (declare-sort <sym> 0)*)
  | DefSt of string * string list * Sort.t
  (* (define-sort <sym> (<sym>* ) <sort>) *)
  | DecPreds of (string * Sort.t list) list
  (* (declare-preds ( ( <sym> <sort>* )* )) *)
  | Ass of Exp.t
  (* (assert <exp>) *)
  | GetAss
  (* (get-assertions) *)
  | CheckSat
  (* (check-sat) *)
  | GetPrf
  (* (get-proof) *)
  | GetUnsat
  (* (get-unsat-core) *)
  | GetVal of Exp.t list
  (* (get-value <exp>* ) *)
  | GetAsgn
  (* (get-assignment) *)
  | GetOpt of Keyword.t
  (* (get-option <keyword>) *)
  | SetOpt of Keyword.t * Exp.t
  (* (set-option <keyword> <exp>) *)
  | GetInfo of Keyword.t
  (* (get-info <keyword>) *)
  | SetInfo of Keyword.t * Exp.t
  (* (set-info <keyword> <attval>) *)
  | Exit
  (* (exit) *)      
  | Push of int option
  (* (push) *)
  | Pop of int option
  (* (pop) *)
  | Echo of string
  (* (echo <string>) *)
  | GetModel
  (* (get-model) *)
  | Reset
  (* (reset) *)
  | Display of Exp.t
  (* (display <exp>) *)
  | Simpfy of Exp.t * Exp.attriv list
  (* (simplify <exp> <attriv>* ) *)
  | Eval of Exp.t * (Keyword.t * Exp.t) list
  (* (eval <exp> (<keyword> <exp>)* ) *)
  | Model
  (* (model) *)
  | DecDT of (string list * datatype list)
  (* (declare-datatypes (<sym>* ) (<datatype>)* )	*)
  (* <datatype> = (<sym> (<cons_decl>)* )		*)
  (* <cons_decl> = (<sym> (<acc_decl>)* )		*)
  (* <acc_decl> = (<sym> <sort>)			*)
  and datatype = string * cons_decl list
  and cons_decl = string * acc_decl list
  and acc_decl = string * Sort.t
  (* Example of datatypes				*)
  (* (declare-datatypes () ((pair (mk_pair (fst Int) (snd Int)))) *)
  (* This means  pair ::= mk_pair of (fst:Int) * (snd:Int) *)
    
  exception Sort_found
    
  let rec getSort_of_symbol coms sym =
    if coms = [] then (raise Not_found) else
      let hdcoms = List.hd coms in
      let tlcoms = List.tl coms in
      let res = ref (Sort.Name "") in
      try
	match hdcoms with
	| DecVar(sym1,sort1) 
	| DecCons(sym1,sort1) 
	| DecFn(sym1,_,sort1) ->
	  if sym = sym1
	  then
	    (res := sort1; raise Sort_found)
	  else getSort_of_symbol tlcoms sym
	| DecFns funinfo ->
	  begin
	    try
	      (res := List.hd(List.rev(List.assoc sym funinfo));
	       raise Sort_found)
	    with Not_found -> getSort_of_symbol tlcoms sym
	  end
	| DecPreds predinfo ->
	  begin
	    try
	      if List.length (List.assoc sym predinfo) >= 0 then
		(res := Sort.Name "Bool";
		 raise Sort_found)
	      else Sort.Name "dummy";
	    with Not_found -> getSort_of_symbol tlcoms sym
	  end
	| DefFn(sym1,_,sort1,_) ->
	  if sym = sym1
	  then
	    (res := sort1; raise Sort_found)
	  else getSort_of_symbol tlcoms sym	  
	| _ -> getSort_of_symbol tlcoms sym
      with Sort_found -> !res

  let getSort_of_exp coms exp =
    let module E = Exp in
    let rec getSort e = 
    match e with
    | E.Var v -> getSort_of_symbol coms v
    | E.Int _ | E.PosInf | E.NegInf -> Sort.Name "Int"
    | E.App(f,_) -> getSort_of_symbol coms f
    | E.All _ -> Sort.Name "Bool"
    | E.Ex _ -> Sort.Name "Bool"
    | E.Let(_,e') -> getSort e'
    | E.Att(e',_) -> getSort e'
    in
    getSort exp

  let rec ctxSortSub csub com = match com with
    | DecVar(sym,sort) -> 
      let sort' = Sort.ctxSortSub csub sort in
      DecVar(sym,sort')
    | DecCons(sym,sort) ->
      let sort' = Sort.ctxSortSub csub sort in
      DecCons(sym,sort')
    | DecFn(sym,sorts,sort) -> 
      let sorts' = List.map (Sort.ctxSortSub csub) sorts in
      let sort' = Sort.ctxSortSub csub sort in
      DecFn(sym,sorts',sort')	
    | DecFns fdecs ->
      let ctxSub (f,sorts) =
	let sorts' = List.map (Sort.ctxSortSub csub) sorts in
	(f,sorts')
      in
      let fdecs' = List.map ctxSub fdecs in
      DecFns fdecs'
   | DefFn(sym,args,sort,exp) -> 
     let sort' = Sort.ctxSortSub csub sort in
     let exp' = Exp.ctxSortSub csub exp in
     let args' =
       List.map (fun (x,s) -> (x, Sort.ctxSortSub csub s)) args
     in
     DefFn(sym,args',sort',exp')
   | DecSt(_,_) as q -> q
   | DefSt(sym,syms,sort) ->
     let sort' = Sort.ctxSortSub csub sort in
     DefSt(sym,syms,sort')
   | DecPreds pdecs ->
     let ctxSub (p,sorts) = (p,List.map (Sort.ctxSortSub csub) sorts)
     in 
     let pdecs' = List.map ctxSub pdecs in
     DecPreds pdecs'
   | Ass exp ->
     let exp' = Exp.ctxSortSub csub exp in
     Ass exp'
  | GetAss as q -> q
  | CheckSat as q -> q
  | GetPrf as q -> q
  | GetUnsat as q -> q
  | GetVal exps ->
    let exps' = List.map (Exp.ctxSortSub csub) exps in
    GetVal exps'
  | GetAsgn as q -> q
  | GetOpt _ as q -> q
  | SetOpt(kw,exp) -> 
    let exp' = Exp.ctxSortSub csub exp in
    SetOpt(kw,exp')
  | GetInfo _ as q -> q
  | SetInfo(kw,exp) ->
    let exp' = Exp.ctxSortSub csub exp in
    SetInfo(kw,exp')
  | Exit as q -> q
  | Push _ as q -> q
  | Pop _ as q -> q
  | Echo _ as q -> q
  | GetModel as q -> q
  | Reset as q -> q
  | Display exp -> 
    let exp' = Exp.ctxSortSub csub exp in
    Display exp'
  | Simpfy(exp,attrs) -> 
    let exp' = Exp.ctxSortSub csub exp in
    let attrs' = List.map (Exp.ctxSortSub_att csub) attrs in
    Simpfy(exp',attrs')
  | Eval(exp,kwexps) ->
    let exp' = Exp.ctxSortSub csub exp in
    let ctxSub_kwex (kw,e) =
      let e' = Exp.ctxSortSub csub e in
      (kw,e')
    in
    let kwexps' = List.map ctxSub_kwex kwexps in
    Eval(exp',kwexps')
  | Model as q -> q
  | DecDT(syms, dtypes) ->
    let dtypes' = List.map (ctxSub_dtype csub) dtypes in
    DecDT(syms, dtypes')
  and ctxSub_dtype csub (sym,cdecls) =
    let cdecls' = List.map (ctxSub_consdecl csub) cdecls in
    (sym,cdecls')
  and ctxSub_consdecl csub (sym,adecls) = 
    let adecls' = List.map (ctxSub_accdecl csub) adecls in
    (sym,adecls')
  and ctxSub_accdecl csub (sym,sort) = 
    let sort' = Sort.ctxSortSub csub sort in
    (sym,sort')

  let rec pp fmt com =
    match com with
    | DecVar(sym,sort)  -> Fmt.fprintf fmt "(declare-var %s %a)" sym Sort.pp sort
    | DecCons(sym,sort) -> Fmt.fprintf fmt "(declare-const %s %a)" sym Sort.pp sort
    | DecFn(sym,sorts,sort) -> Fmt.fprintf fmt "(declare-fun %s (%a) %a)" sym (pp_list_space Sort.pp) sorts Sort.pp sort
    | DecFns fdecs ->
       let pp_fdec fmt (f,sorts) = Fmt.fprintf fmt "(%s %a)" f (pp_list_space Sort.pp) sorts in
       Fmt.fprintf fmt "(declare-funs (%a))" (pp_list_space pp_fdec) fdecs
    | DecSt(sym,n) -> Fmt.fprintf fmt "(declare-sort %s %d)" sym n
    | DefSt(sym,syms,sort) -> Fmt.fprintf fmt "(define-sort %s (%a) %a)" sym (pp_list_space Fmt.pp_print_string) syms Sort.pp sort
    | DefFn(sym,args,sort,exp) ->
       let pp_arg fmt (x,s) = Fmt.fprintf fmt "(%s %a)" x Sort.pp s in
       Fmt.fprintf fmt "(define-fun %s (%a) %a %a)" sym (pp_list_space pp_arg) args Sort.pp sort Exp.pp exp
    | DecPreds pdecs ->
       let pp_pdec fmt (p,sorts) =
         if sorts = [] then Fmt.fprintf fmt "(%s)" p
         else Fmt.fprintf fmt "(%s %a)" p (pp_list_space Sort.pp) sorts
       in
       Fmt.fprintf fmt "(declare-preds (%a))" (pp_list_space pp_pdec) pdecs
    | Ass exp -> Fmt.fprintf fmt "(assert %a)" Exp.pp exp
    | GetAss -> Fmt.fprintf fmt "(get-assertions)"
    | CheckSat -> Fmt.fprintf fmt "(check-sat)"
    | GetPrf -> Fmt.fprintf fmt "(get-proof)"
    | GetUnsat -> Fmt.fprintf fmt "(get-unsat-core)"
    | GetVal exps -> Fmt.fprintf fmt "(get-value %a)" (pp_list_space Exp.pp) exps
    | GetAsgn -> Fmt.fprintf fmt "(get-assignment)"
    | GetOpt kw -> Fmt.fprintf fmt "(get-option %a)" Keyword.pp kw
    | SetOpt(kw,exp) -> Fmt.fprintf fmt "(set-option %a %a)" Keyword.pp kw Exp.pp exp
    | GetInfo kw -> Fmt.fprintf fmt "(get-info %a)" Keyword.pp kw
    | SetInfo(kw,exp) -> Fmt.fprintf fmt "(set-info %a %a)" Keyword.pp kw Exp.pp exp
    | Exit -> Fmt.fprintf fmt "(exit)"
    | Push None -> Fmt.fprintf fmt "(push)"
    | Push (Some n) -> Fmt.fprintf fmt "(push %d)" n
    | Pop None -> Fmt.fprintf fmt "(pop)"
    | Pop (Some n) -> Fmt.fprintf fmt "(pop %d)" n
    | Echo str -> Fmt.fprintf fmt "(echo %s)" str
    | GetModel -> Fmt.fprintf fmt "(get-model)"
    | Reset -> Fmt.fprintf fmt "(reset)"
    | Display exp -> Fmt.fprintf fmt "(display %a)" Exp.pp exp
    | Eval(exp,[]) -> Fmt.fprintf fmt "(eval %a)" Exp.pp exp
    | Eval(exp,kwexps) ->
       let pp_kwexp fmt (kw,e) = Fmt.fprintf fmt "(%a %a)" Keyword.pp kw Exp.pp e in
       Fmt.fprintf fmt "(eval %a %a)" Exp.pp exp (pp_list_space pp_kwexp) kwexps
    | Model -> Fmt.fprintf fmt "(model)"
    | Simpfy(exp,[]) -> Fmt.fprintf fmt "(simplify %a)" Exp.pp exp
    | Simpfy(exp,attrs) -> Fmt.fprintf fmt "(simplify %a %a)" Exp.pp exp (pp_list_space Exp.pp_attr) attrs
    | DecDT(syms, dtypes) ->
       Fmt.fprintf fmt "(declare-datatypes (%a) (%a))" (pp_list_space Fmt.pp_print_string) syms (pp_list_space pp_datatype) dtypes
  and pp_datatype fmt (sym,cdecls) =
    match cdecls with
    | [] -> Fmt.fprintf fmt "%s" sym
    | _  -> Fmt.fprintf fmt "(%s %a)" sym (pp_list_space pp_consdecl) cdecls
  and pp_consdecl fmt (sym,adecls) =
    match adecls with
    | [] -> Fmt.fprintf fmt "%s" sym
    | _  -> Fmt.fprintf fmt "(%s %a)" sym (pp_list_space pp_accdecl) adecls
  and pp_accdecl fmt (sym,sort) = Fmt.fprintf fmt "(%s %a)" sym Sort.pp sort
                            
  let print = Fmt.printf "@[%a@]" pp
    
  let println = Fmt.printf "@[%a@." pp
    
  (* hasInf checks whether com contains PosInf/NegInf *) 
  let hasInf com : bool * bool = 
    match com with
    | Ass exp
      | DefFn(_,_,_,exp)
      | SetOpt(_,exp)
      | SetInfo(_,exp)
      | Display exp 
      | Simpfy(exp,_)
      | Eval(exp,_) -> Exp.hasInf exp
    | GetVal exps -> Exp.hasInfL exps
    | _ -> (false,false)               

  let hasInfL coms =
    List.fold_left
      (fun (b1,b2) c -> let (b1',b2')=hasInf c in (b1||b1',b2||b2'))
      (false,false)
      coms         
                    
end
;;

module SMTprog = struct

  type t = Logic.t * Command.t list

  let pp fmt (prog : t) =
    let (logic,commands) = prog in
    Fmt.fprintf fmt "(set-logic %a)\n\n" Logic.pp logic;
    Fmt.fprintf fmt "%a" (pp_list_newline Command.pp) commands

  let print = Fmt.printf "@[%a@." pp

end
;;

(*--------------------------------------*)
(* Short-cuts for SMT-expressions	    *)
(*--------------------------------------*)
let ( =^= ) t1 t2 = Exp.App("=",[t1;t2])   (* eq *)
;;
let ( <^> ) t1 t2 = Exp.App("distinct",[t1;t2])   (* neq *)
;;
let ( >^= ) t1 t2 = Exp.App(">=",[t1;t2])  (* geq*)
;;
let ( <^= ) t1 t2 = Exp.App("<=",[t1;t2])  (* leq *)
;;
let ( <^< ) t1 t2 = Exp.App("<",[t1;t2])   (* lt *)
;;
let ( %^% ) t1 t2 = Exp.App("mod",[t1;t2])  (* t1 mod t2 *)
;;
let zero' = Exp.Int 0
;;
let bot' = Exp.App("distinct",[zero';zero']) (* false *)
;;
let top' = Exp.App("=",[zero';zero'])  (* true *)
;;
let not' e = Exp.App("not",[e])  (* negation *)
;;
let ( -^> ) e1 e2 = Exp.App("imp",[e1;e2]) (* imply *)
;;
let ( &^& ) e1 e2 = Exp.App("and",[e1;e2])  (* e1 and e2 *)
;;
let ( |^| ) e1 e2 = Exp.App("or",[e1;e2])  (* e1 and e2 *)
;;
let bigOr' ee =
  match List.length ee with
  | 0 -> bot'
  | 1 -> List.hd ee
  | _ -> Exp.App("or",ee)
;;
let bigAnd' ee =
  match List.length ee with
  | 0 -> top'
  | 1 -> List.hd ee
  | _ -> Exp.App("and",ee)
;;
let imp' e1 e2 = Exp.App("imp",[e1;e2])
;;
(*
let int' = Sort.Name "Int"
;;
let bv32' = Sort.BV 32
;;
 *)
let allnatS' vvv e =
  match Strset.is_empty vvv with
  | true  -> e
  | false -> Exp.All(Exp.Nat,vvv,e)
;;
let allintS' vvv e =
  match Strset.is_empty vvv with
  | true  -> e
  | false -> Exp.All(Exp.Int,vvv,e)
;;
let exnatS' vvv e =
  match Strset.is_empty vvv with
  | true  -> e
  | false -> Exp.Ex(Exp.Nat,vvv, e)
;;
let exintS' vvv e =
  match Strset.is_empty vvv with
  | true  -> e
  | false -> Exp.Ex(Exp.Int,vvv,e)
;;
let allnat' vv e = allnatS' (Strset.of_list vv) e
;;
let allint' vv e = allintS' (Strset.of_list vv) e
;;
let exnat' vv e = exnatS' (Strset.of_list vv) e
;;
let exint' vv e = exintS' (Strset.of_list vv) e
;;
