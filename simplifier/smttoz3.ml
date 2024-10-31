open Notations
open PrintTools
open Tools
open Smtsyntax
open Z3

module Cmd = Command
module ZA = Z3.Arithmetic
module ZI = Z3.Arithmetic.Integer
module ZB = Z3.Boolean
module ZE = Z3.Expr
module ZQ = Z3.Quantifier
module ZV = Z3.BitVector
module ZSym = Z3.Symbol
module ParamDescrs = Z3.Params.ParamDescrs

let myInt  = Smtsyntax.Sort.Name "Int"
           
let myBool = Smtsyntax.Sort.Name "Bool"
           
let myBV32 = Smtsyntax.Sort.Name "BitVec[32]"
(* let myBV32 = Smtsyntax.Sort.BV 32;; *)

let _PosInf,_NegInf = "PosInf","NegInf"
                    
let posInf,negInf = Exp.Var _PosInf, Exp.Var _NegInf

module Mode = struct
  type t = Arithmetic of string | BitVector

  let pp ppf mode =
    match mode with
    | Arithmetic str -> Fmt.fprintf ppf "@[Arithmetic:%s@]" str
    | BitVector -> Fmt.fprintf ppf "@[BitVector@]"

  let println mode = Fmt.fprintf stdout "@[%a@." pp mode    

end
;;
exception UNKNOWN
;;

let println_ze e = print_endline (ZE.to_string e)
;;

module EnrichedContext = struct 
  type t =
    context *
      (Smtsyntax.Sort.t * Sort.sort) list * 
      (string * Symbol.symbol * FuncDecl.func_decl * int option) list
  (* an enriched context has the form (ctx,sort_info,func_info) *)
  (* sort_info is an assoc list of smt-sort and z3-sort		*)
  (* e.g., [(Int,<int>) ; (Bool,<bool>) ; ..]			*)
  (* func_info is an assoc list of (name,symbol,fdecl,db_id)	*)
  (* 'db_id' is the de-bruijn index of the variable 		*)
  (* 'x' is replaced by 'n' if ('x',..,Some 'n') is in ectx	*)
      
  let init ctx : t =
    let ints = ZA.Integer.mk_sort ctx in
    let bools = Boolean.mk_sort ctx in
    let bv32 = ZV.mk_sort ctx 32 in
    (ctx,[(myInt,ints);(myBool,bools);(myBV32,bv32)],[])

  let lookupFun (ectx : t) name = 
    let (_,_,fdata) = ectx in
    let fdata' = List.map (fun (a,b,c,d) -> (a,(b,c,d))) fdata in
    List.assoc name fdata'

  let rec lookupSort (ectx : t) sort =
    let module SS = Smtsyntax.Sort in
    let (cxt,sdata,_) = ectx in
    let sortmatch sort1 sort2 =
      match sort1,sort2 with
      | SS.Name p1,SS.Name p2 -> 
	     if p1 = p2 then true else false
      (* | SS.BV _,SS.BV _ -> true *)
      | SS.App(p1,_),SS.App(p2,_) ->
	     if p1 = p2 then true else false        
      | _,_ -> false
    in
    let msorts = List.filter (fun (s,_)-> sortmatch s sort) sdata in
    if msorts = [] then (Smtsyntax.Sort.println sort; failwith "Error: smttoz3.lookupSort")
    else
      (fun (_,z)->z) (List.hd msorts)

  let get_range (ectx : t) name =
    let (_,fdecl,_) = lookupFun ectx name in
    FuncDecl.get_range fdecl
    
  let isDeclaredFun (ectx : t) name =
    try
      let _ = lookupFun ectx name in true
    with Not_found -> false

  let get_int (ectx : t) = 
    lookupSort ectx myInt

  let get_bv32 (ectx : t) = 
    lookupSort ectx myBV32
    
  let get_bool (ectx : t) =
    lookupSort ectx myBool

  (* add constants of given sort *)
  let add_consts (ectx : t) sort names : t = 
    let (ctx,sdata,fdata) = ectx in
    let syms = List.map (Z3.Symbol.mk_string ctx) names in
    let fdecls = List.map 
      (fun s -> Z3.FuncDecl.mk_const_decl ctx s sort)
      syms
    in
    let itemLst = zipLst names (zipLst syms fdecls) in
    let fdata1 = List.map (fun (x,(y,z)) -> (x,y,z,None)) itemLst in
    (ctx,sdata,fdata1@fdata)

  (* add int constants *)
  let add_iconsts (ectx : t) names =
    let ints = get_int ectx in 
    add_consts ectx ints names

  (* add bool constants *)
  let add_bconsts (ectx : t) names = 
    let bools = get_bool ectx in 
    add_consts ectx bools names

  (* add bit-vector constants *)
  let add_bvconsts (ectx : t) names = 
    let bv32s = get_bv32 ectx in 
    add_consts ectx bv32s names
    
  let add_fun (ectx : t) f sorts sort : t = 
    let (ctx,sdata,fdata) = ectx in
    let sym = Z3.Symbol.mk_string ctx f in
    let fdecl = Z3.FuncDecl.mk_func_decl ctx sym sorts sort in
    let fdat = (f,sym,fdecl,None) in
    (ctx,sdata,fdat::fdata)

  let shift_index (ectx : t) : t =
    let (ctx,sdata,fdata) = ectx in
    let shift_id opt = match opt with
      | None -> None
      | Some n -> Some (n+1)
    in
    let shift_finfo (f,s,d,o) = (f,s,d,shift_id o) in
    (ctx, sdata, List.map shift_finfo fdata)
      
  let add_bvar (ectx : t) v sort : t =
    let (ctx,sdata,fdata) = shift_index ectx in
    let sym = Z3.Symbol.mk_string ctx v in
    let fdecl = Z3.FuncDecl.mk_func_decl ctx sym [] sort in
    let fdat = (v,sym,fdecl,Some 0) in
    (ctx,sdata,fdat::fdata)    

  let get_consts (ectx : t) =
    let module ZF = Z3.FuncDecl in
    let (_,_,fdata) = ectx in
    let isConst fdecl =
      if ZF.get_domain fdecl = [] then true else false
    in
    let xl = List.filter (fun (_,_,fdecl,_) -> isConst fdecl) fdata in
    let xdl = List.rev (List.map (fun (x,_,fdecl,_) -> (x,fdecl)) xl) in
    List.map (fun (x,fd) -> (x,ZF.get_range fd)) xdl
      
end
;;

module EC = EnrichedContext;;

(* transformation for bitvector mode *)
let make_app_bitvector (ectx : EC.t) f exps =
  let (ctx,_,_) = ectx in
  match f with
  | "+" -> ZV.mk_add ctx (List.nth exps 0) (List.nth exps 1)
  | "*" -> ZV.mk_mul ctx (List.nth exps 0) (List.nth exps 1)
  | "-" ->
    if List.length exps = 1 then
      ZV.mk_neg ctx (List.hd exps)
    else ZV.mk_sub ctx (List.nth exps 0) (List.nth exps 1)
  | "div" -> ZV.mk_sdiv ctx (List.nth exps 0) (List.nth exps 1)
  | "/" -> ZV.mk_sdiv ctx (List.nth exps 0) (List.nth exps 1)  (* it also receives "/" *)
  | "mod" -> ZV.mk_smod ctx (List.nth exps 0) (List.nth exps 1)
  | "<" -> ZV.mk_slt ctx (List.nth exps 0) (List.nth exps 1)
  | ">" -> ZV.mk_sgt ctx (List.nth exps 0) (List.nth exps 1)
  | "<=" -> ZV.mk_sle ctx (List.nth exps 0) (List.nth exps 1)
  | ">=" -> ZV.mk_sge ctx (List.nth exps 0) (List.nth exps 1)
  | "=" -> ZB.mk_eq ctx (List.nth exps 0) (List.nth exps 1)
  | "distinct" -> ZB.mk_distinct ctx exps
  | "not" -> ZB.mk_not ctx (List.hd exps)
  | "and" -> ZB.mk_and ctx exps
  | "or" -> ZB.mk_or ctx exps
  | "xor" -> ZB.mk_xor ctx (List.nth exps 0) (List.nth exps 1)
  | "ite" -> ZB.mk_ite ctx (List.nth exps 0) (List.nth exps 1) (List.nth exps 2)
  | "iff" -> ZB.mk_iff ctx (List.nth exps 0) (List.nth exps 1)
  | "imp" -> ZB.mk_implies ctx (List.nth exps 0) (List.nth exps 1)
  | "<<" -> ZV.mk_shl ctx (List.nth exps 0) (List.nth exps 1)
  | ">>" -> ZV.mk_lshr ctx (List.nth exps 0) (List.nth exps 1)
  | "band" -> ZV.mk_and ctx (List.nth exps 0) (List.nth exps 1)
  | "bor"  -> ZV.mk_or ctx (List.nth exps 0) (List.nth exps 1)
  | "bxor" -> ZV.mk_xor ctx (List.nth exps 0) (List.nth exps 1)
  | "bnot" -> ZV.mk_not ctx (List.nth exps 0)
  | _ -> raiseMes ("make_app_bitvector: unknown function: " ^ f) UNKNOWN
;;

(* transformation for arithmetic mode *)
let make_app_arithmetic (ectx : EC.t) f exps =
  let (ctx,_,_) = ectx in
  match f with
  | "+" -> ZA.mk_add ctx exps
  | "*" -> ZA.mk_mul ctx exps
  | "-" ->
    if List.length exps = 1 then
      ZA.mk_unary_minus ctx (List.hd exps)
    else ZA.mk_sub ctx exps
  | "div" -> ZA.mk_div ctx (List.nth exps 0) (List.nth exps 1)
  | "/" -> ZA.mk_div ctx (List.nth exps 0) (List.nth exps 1)  (* it also receives "/" *)
  | "mod" -> ZI.mk_mod ctx (List.nth exps 0) (List.nth exps 1)
  | "<" -> ZA.mk_lt ctx (List.nth exps 0) (List.nth exps 1)
  | ">" -> ZA.mk_gt ctx (List.nth exps 0) (List.nth exps 1)
  | "<=" -> ZA.mk_le ctx (List.nth exps 0) (List.nth exps 1)
  | ">=" -> ZA.mk_ge ctx (List.nth exps 0) (List.nth exps 1)
  | "=" -> ZB.mk_eq ctx (List.nth exps 0) (List.nth exps 1)
  | "distinct" -> ZB.mk_distinct ctx exps
  | "not" -> ZB.mk_not ctx (List.hd exps)
  | "and" -> ZB.mk_and ctx exps
  | "or" -> ZB.mk_or ctx exps
  | "xor" -> ZB.mk_xor ctx (List.nth exps 0) (List.nth exps 1)
  | "ite" -> ZB.mk_ite ctx (List.nth exps 0) (List.nth exps 1) (List.nth exps 2)
  | "iff" -> ZB.mk_iff ctx (List.nth exps 0) (List.nth exps 1)
  | "imp" -> ZB.mk_implies ctx (List.nth exps 0) (List.nth exps 1)
  | _ -> raiseMes ("make_app_arithmetic: unknown function: " ^ f) UNKNOWN
;;

(* translation of expressions *) (** Error here *)
let rec transExpr mode (ectx : EC.t) exp =  
  let module SE = Exp in  
  let (ctx,_,_) = ectx in
  let ints = EC.get_int ectx in  
  let make_app =
    match mode with
    | Mode.Arithmetic _ -> make_app_arithmetic
    | Mode.BitVector  -> make_app_bitvector
  in
  let expZero =
    match mode with
    | Mode.Arithmetic _ -> ZE.mk_numeral_int ctx 0 ints
    | Mode.BitVector    -> ZV.mk_numeral ctx "0" 32
  in
  let sort =
    match mode with
    | Arithmetic _ -> ZA.Integer.mk_sort ctx
    | BitVector -> ZV.mk_sort ctx 32
  in
  match exp,mode with
  | SE.Int n,Mode.BitVector     -> ZV.mk_numeral ctx (string_of_int n) 32
  | SE.Int n,Mode.Arithmetic _  -> ZE.mk_numeral_int ctx n ints
  | SE.PosInf,_ -> ZE.mk_const_s ctx _PosInf sort
  | SE.NegInf,_ -> ZE.mk_const_s ctx _NegInf sort
  (*
  | SE.PosInf,Mode.BitVector    -> ZV.mk_numeral ctx (string_of_int max_int) 32
  | SE.PosInf,Mode.Arithmetic _ -> ZE.mk_numeral_int ctx max_int ints
  | SE.NegInf,Mode.BitVector    -> ZV.mk_numeral ctx (string_of_int min_int) 32
  | SE.NegInf,Mode.Arithmetic _ -> ZE.mk_numeral_int ctx min_int ints
                                  *)
  | SE.Var v,_ ->
     let (_,vdecl,opt) = EC.lookupFun ectx v in
     begin
       match opt with
       | None    -> ZE.mk_const_f ctx vdecl
       | Some id -> ZQ.mk_bound ctx id (EC.get_range ectx v)
     end
  | SE.App(f,args),_ ->
     let args' = List.map (transExpr mode ectx) args in
     make_app ectx f args'
  | SE.Let(_,_),_ -> ZE.mk_const_s ctx "Let" ints		(* dummy *)
  | SE.Att(exp,_),_ -> transExpr mode ectx exp			(* dummy *)
  | SE.All (dom,vvv,body),_ ->
     let vv = Strset.elements vvv in
     let varsorts = List.map (fun v -> ZE.mk_const ctx (ZSym.mk_string ctx v) sort) vv in
     let ectx' = List.fold_left (fun ectx0 v -> EC.add_bvar ectx0 v sort) ectx vv in
     let (ctx',_,_) = ectx' in     
     let body1 = transExpr mode ectx' body in
     let body2 =
       match dom with
       | SE.Int -> body1
       | SE.Nat ->
          let condExpL = 
            List.map
              (fun v ->
                let (_,vdecl,_) = EC.lookupFun ectx' v in
                let var = ZE.mk_const_f ctx' vdecl in (* Z3.Exp *)
                make_app ectx' ">=" [var;expZero]
              )
              vv
          in
          let expAndCond = if List.length condExpL = 1 then List.hd condExpL else ZB.mk_and ctx' condExpL in
          ZB.mk_implies ctx' expAndCond body1
     in
     let qexp =
       ZQ.mk_forall_const ctx
	     varsorts   (* expr list *)
	     body2		(* main part *)
	     None [] [] None None		(* auxiliary part *)
     in ZQ.expr_of_quantifier qexp
  | SE.Ex (dom,vvv,body),_ ->
     let vv = Strset.elements vvv in     
     let varsorts = List.map (fun v -> ZE.mk_const ctx (ZSym.mk_string ctx v) sort) vv in
     let ectx' = List.fold_left (fun ectx0 v -> EC.add_bvar ectx0 v sort) ectx vv in
     let (ctx',_,_) = ectx' in     
     let body1 = transExpr mode ectx' body in
     let body2 =
       match dom with
       | SE.Int -> body1
       | SE.Nat ->
          let condExpL = 
            List.map
              (fun v ->
                let (_,vdecl,_) = EC.lookupFun ectx' v in
                let var = ZE.mk_const_f ctx' vdecl in (* Z3.Exp *)
                make_app ectx' ">=" [var;expZero]
              )
              vv
          in
          ZB.mk_and ctx' (condExpL @ [body1])
     in
     let qexp =
       ZQ.mk_exists_const ctx
	     varsorts   (* expr list *)
	     body2		(* main part *)
	     None [] [] None None		(* auxiliary part *)
     in ZQ.expr_of_quantifier qexp
;;


(* Translation of datatypes				*)
(* mk_z3constructor ctx dtps i j 			*)
(* It makes Z3-constructor of the j-th constructor of	*)
(* the i-th type of the datatype dtps			*)
let mk_z3constructor
    (ectx : EC.t)
    (dtps : Cmd.datatype list) i j =
  let module EC = EnrichedContext in
  let (ctx,_,_) = ectx in
  let get_body_nthtype i = (fun (_,y)->y) (List.nth dtps i) in
  let get_nthbody_nthtype i j =
    List.nth (get_body_nthtype i) j in
  let get_cons_nthbody_nthtype i j =
    (fun (x,_) -> x) (get_nthbody_nthtype i j) in
  let get_adecs_nthbody_nthtype i j =
    (fun (_,y) -> y) (get_nthbody_nthtype i j) in
  let adecslen_nthbody_nthtype i j =
    List.length (get_adecs_nthbody_nthtype i j) in
  let get_nthadec_nthbody_nthtype i j k =
    List.nth (get_adecs_nthbody_nthtype i j) k in
  let get_acc_nthadec_nthabody_nthtype i j k =
    (fun (x,_) -> x) (get_nthadec_nthbody_nthtype i j k) in
  let get_accsort_nthadec_nthabody_nthtype i j k = 
    (fun (_,y) -> y) (get_nthadec_nthbody_nthtype i j k) in
  let cons = get_cons_nthbody_nthtype i j in
  let iscons = "is_"^cons in
  let sym_iscons = Z3.Symbol.mk_string ctx iscons in
  let alst = genLst (adecslen_nthbody_nthtype i j) in
  let accs = List.map (get_acc_nthadec_nthabody_nthtype i j) alst in
  let sym_accs = List.map (Z3.Symbol.mk_string ctx) accs in
  let asorts = List.map (get_accsort_nthadec_nthabody_nthtype i j) alst in
  let asorts' = List.map (EC.lookupSort ectx) asorts in
  let asorts_opt = List.map (fun x -> Some x) asorts' in
  let ilst = List.map (fun _ -> 1) alst in	
  Z3.Datatype.mk_constructor_s
    ctx
    cons		(* Name of the constructor <cons> *)
    sym_iscons		(* Symbol of the recognizer "is_<cons>" *)
    sym_accs		(* Symbols of the accessors *)
    asorts_opt		(* Sorts of the accessors *)
    ilst		(* I'm not sure the role of this list *)
;;

let mk_z3constructors ectx dtps i =
  let get_body_nthtype i = (fun (_,y)->y) (List.nth dtps i) in
  let bodylen_nthtype i = List.length (get_body_nthtype i) in
  let blst = genLst (bodylen_nthtype i) in
  List.map (mk_z3constructor ectx dtps i) blst
;;

(* mk_econtext coms					*)
(* It creates an ectx from given commands		*)
(* It checks DecFn, DecSt, 				*)
(* DefFn (if it's not decl'd), and DecDT		*)
(* Other commands are skipped				*)
(* DecVar,DecCons,DecFns,DecPreds,DefSt,DefFn are skipped *)
(* since they are already eliminated			*)
let mk_econtext modelflag ucflag commands : EC.t =
  let module SS = Smtsyntax.Sort in
  let module ZS = Z3.Sort in
  let module ZD = Z3.Datatype in  
  let _ctxSeed = ref [] in
  if modelflag then _ctxSeed := ("model","true")::!_ctxSeed else ();
  if ucflag then _ctxSeed := ("unsat_core","true")::!_ctxSeed else ();
  let ctx = Z3.mk_context !_ctxSeed in
  let ectx = ref (EC.init ctx) in
  let rec mk_ectx coms =
    if coms = [] then () else
    let hdcom = List.hd coms in
    let tlcom = List.tl coms in
    match hdcom with
    | Cmd.DecFn(f,sorts,sort) ->
      let sorts' = List.map (EC.lookupSort !ectx) sorts in
      let sort' = EC.lookupSort !ectx sort in
      ectx := EC.add_fun !ectx f sorts' sort';
     mk_ectx tlcom
    | Cmd.DecSt(name,_) ->
      let (ctx,sdata,fdata) = !ectx in
      let sort = SS.Name name in
      let sort' = ZS.mk_uninterpreted_s ctx name in
      ectx := (ctx,(sort,sort')::sdata,fdata);
      mk_ectx tlcom
    | Cmd.DecDT(vars,dtps) ->
      let (ctx,sdata,fdata) = !ectx in
      let prmsort_smt = List.map (fun v -> SS.Name v) vars in
      let prmsort_z3 = List.map (ZS.mk_uninterpreted_s ctx) vars in
      let ectx1 = (ctx,(zipLst prmsort_smt prmsort_z3)@sdata,fdata) in
      let n = List.length dtps in
      let nlst = genLst n in
      let get_name_nthtype i = (fun (x,_)->x) (List.nth dtps i) in
      let typenames = List.map get_name_nthtype nlst in
      let typename0 = List.nth typenames 0 in
      let nthConstructors i = mk_z3constructors ectx1 dtps i in
      let constructors0 = nthConstructors 0 in
      let z3Sort = ZD.mk_sort_s ctx typename0 constructors0 in
      let smtSort =
	    if vars = [] then SS.Name typename0
	    else
	      let argsorts = List.map (fun v -> SS.Name v) vars in
	      SS.App(typename0,argsorts)
      in
      ectx := (ctx,(smtSort, z3Sort)::sdata,fdata);
      mk_ectx tlcom
    | _ -> mk_ectx tlcom
  in
  mk_ectx commands;
  !ectx
;;

module SimpleExp = struct
  type t = Cons of string | Int of int | OTHER

  let pp fmt (se : t) =
    match se with
    | Cons str -> Fmt.fprintf fmt "%s" str
    | Int n -> Fmt.fprintf fmt "%d" n
    | OTHER -> Fmt.fprintf fmt "OTHER"

  let pps fmt (se : t) =
    match se with
    | Cons str -> Fmt.sprintf "%s" str
    | Int n -> Fmt.sprintf "%d" n
    | OTHER -> Fmt.sprintf "OTHER"

  let exp2int e =
    let eStr = ZE.to_string e in
    try
      int_of_string eStr
    with
      _ -> (* fail case may be (- 2000) or real fail *)
      let eStr' = String.sub eStr 3 (String.length eStr - 4) in (* remove "(- " and ")" *)
      try
        (-1) * (int_of_string eStr')
      with
        _ -> (* real fail *)
        Fmt.printf "@[SimpleExp: Non-numeral %s@." eStr';
        failwith ""
      
  let of_exp ctx e : t =
    match ZV.is_bv e, ZE.is_numeral e, ZE.is_const e with
    | true,_,_ -> Int (exp2int (ZV.mk_bv2int ctx e true))
    | _,true,_ -> Int (exp2int e)
    | _,_,true -> Cons (ZE.to_string e)
    | _,_,false -> OTHER

  let to_int ctx e =
    match ZV.is_bv e, ZE.is_numeral e with
    | true,_ -> exp2int (ZV.mk_bv2int ctx e true)
    | _,true -> exp2int e
    | _,_ -> Fmt.printf "@[SimpleExp.to_int: Non-numeral %s@." (ZE.to_string e); failwith ""
                 
  let optexp2int ctx oe =
	match oe with
	| Some e -> to_int ctx e
	| None -> print_endline "SimpleExp.optexp2int: None"; failwith ""
                 
  let of_optexp ctx oe =
    match oe with
    | None -> OTHER
    | Some e -> of_exp ctx e

end
;;

module SatcheckResult = struct
  
  type model = (string * int) list
             
  type t = 
    | Model of model (* model [(x,1);(y,2)] when sat *)
    | UnsatCore of Z3.Expr.expr list (* unsat-core [e1;e2] when unsat *)
    | Unknown

  let pp_model fmt model =
    let pp1 fmt (x,n) = Fmt.fprintf fmt "(%s,%d)" x n in
    Fmt.fprintf fmt "%a" (pp_list_space pp1) model

  let pp_unsatcore fmt uc =
    Fmt.fprintf fmt "%s" (List.fold_left (fun s e -> s ^ (Z3.Expr.to_string e)) "" uc)
    
  let println res =
    match res with
    | Model mods -> Fmt.printf "@[%a\n@." pp_model mods
    | UnsatCore expL -> print_endline "UnsatCore"
    | Unknown -> print_endline "Unknown"
                 
end
;;
open SatcheckResult
;;

let set_timeout timeoutOpt =
  match timeoutOpt with
  | None -> ()
  | Some time -> Z3.set_global_param "timeout" (string_of_int time)
;;     

(* 
This may raise exception UNKNOWN if
- Z3 answers unknown or
- input is a bitvetor expression in Arithmetic mode
- Assumption: (modelflag && ucflag) != true
*)
let checkCommands mode modelflag ucflag vvInt vvNat commands : SatcheckResult.t =
  set_timeout (Some 60); (* timeout 60sec *)
  let ectx =
    let ectx0 = mk_econtext modelflag ucflag commands in
    match mode with
    | Mode.Arithmetic _ -> EC.add_iconsts ectx0 (_PosInf::_NegInf::vvInt @ vvNat)
    | Mode.BitVector    -> EC.add_bvconsts ectx0 (_PosInf::_NegInf::vvInt @ vvNat)
  in
  dbgf "SATdebug" "@[------------------------------@.";  
  dbgf "SATdebug" "@[Input for checkCommands@.";
  dbgf "SATdebug" "@[%a@." (pp_list_newline Cmd.pp) commands;
  dbgf "SATdebug" "@[------------------------------@.";    
  let (ctx,sdata,fdata) = ectx in
  let t_ufnia = Tactic.mk_tactic ctx "ufnia" in
  let t_bv = Tactic.mk_tactic ctx "bv" in      
  (* let t_smt = Tactic.mk_tactic ctx "smt" in *)
  let t_lia = Tactic.mk_tactic ctx "lia" in    
  let tactic =
    match mode with
    | Mode.Arithmetic "lia" -> t_lia
    | Mode.Arithmetic _ -> t_ufnia
    | Mode.BitVector  -> t_bv
  in
  let solver = Solver.mk_solver_t ctx tactic in  
  
  (* List.iter print_endline (Tactic.get_tactic_names ctx); *)
  let _expL = ref [] in
  let rec mk_mysolver solver' com =
    if com = [] then ()
    else
      let hdcom = List.hd com in
      let tlcom = List.tl com in
      match hdcom with
      | Cmd.DecVar(_,_)
      | Cmd.DecCons(_,_)
      | Cmd.DecFns _
      | Cmd.DecSt(_,_)
      | Cmd.DecPreds _
      | Cmd.DefSt(_,_,_)
      | Cmd.DefFn(_,_,_,_)
	(* skipped since already eliminated in preproccessing *)
      | Cmd.DecFn(_,_,_)
      |	Cmd.DecDT(_,_)
	(* skipped since already treated in mk_econtext *)
      | Cmd.Push _
      | Cmd.Pop _
      | Cmd.GetAss
      | Cmd.GetPrf
      | Cmd.GetUnsat
      | Cmd.GetAsgn
      | Cmd.SetOpt(_,_)
      | Cmd.GetInfo _
      | Cmd.SetInfo(_,_)
      | Cmd.Exit
      | Cmd.Echo _
      | Cmd.GetModel
      | Cmd.Reset
      | Cmd.Display _
      | Cmd.Simpfy(_,_)
      | Cmd.Eval(_,_)
      | Cmd.Model
      | Cmd.GetOpt _ -> 
	(* ignored since they are out of scope *)
	       mk_mysolver solver' tlcom
      | Cmd.Ass exp ->
         let exp' = try transExpr mode ectx exp  with x -> raiseMes "checkCommands: tranExpr error" x in
         Solver.assert_and_track solver' exp' exp';
	     mk_mysolver solver' tlcom
      | Cmd.CheckSat -> ()	(* finishes if check-sat comes *)
      | Cmd.GetVal exp -> mk_mysolver solver' tlcom (* dummy *)
  in
  mk_mysolver solver commands;

  let timeoutOpt = Z3.get_global_param "timeout" in
  let timeoutStr = match timeoutOpt with None -> "None" | Some ss -> ss in
  dbgf "Z3" "@[[Z3 Solver Status]@.";
  dbgf "Z3" "@[Timeout: %s@." timeoutStr;
  dbgf "Z3" "@[Commands:\n%s@." (Solver.to_string solver);

  match Solver.check solver [],modelflag,ucflag with
  | Z3.Solver.SATISFIABLE,true,_ ->
     dbgf "Z3" "@[Result: SAT\n@.";
     begin
       match Solver.get_model solver with
       | None -> Model []		(* Dummy *)
       | Some model ->
	      let evalexp e = Z3.Model.evaluate model e true in (* true: use model completion (put constant if e cannot be calculated in the model) *)
	      let evalcons (v,s) = evalexp (ZE.mk_const_s ctx v s) in
	      let varsorts = EC.get_consts ectx in
	      let vars = List.map fst varsorts in
	      let optvals = List.map evalcons varsorts in
	      let valL = List.map (SimpleExp.optexp2int ctx) optvals in
	      let varvalL = zipLst vars valL in
	      Model varvalL
     end
  | Z3.Solver.SATISFIABLE,false,_ ->
     dbgf "Z3" "@[Result: SAT\n@.";
     Model []
  | Z3.Solver.UNSATISFIABLE,_,true ->
     dbgf "Z3" "@[Result: UNSAT\n@.";
     let uc = Solver.get_unsat_core solver in
     UnsatCore uc
  | Z3.Solver.UNSATISFIABLE,_,false ->
     dbgf "Z3" "@[Result: UNSAT\n@.";
     UnsatCore []
  | Z3.Solver.UNKNOWN,_,_ ->
     dbgf "Z3" "@[Result: UNKNOWN\n@.";
     Fmt.printf "@[checkCommands: solver returns UNKNOWN@.";
     raise UNKNOWN
;;

let checkCommandsSwitch mode modelflag ucflag vvInt vvNat commands =
  match checkCommands mode modelflag false vvInt vvNat commands with
  | UnsatCore _ when ucflag ->
     dbgf "Z3" "@[Second Execution of Z3 for making UNSAT-CORE@.";
     checkCommands mode false true vvInt vvNat commands (* ~modelflag:false ~ucflag:true *)
  | _ as res -> res
;;  

let checkCommandsAuto modelflag ucflag vvInt vvNat commands : SatcheckResult.t =
  let posInf_eq_maxInt = posInf =^= (Exp.Int  200000000) in
  let negInf_eq_minInt = negInf =^= (Exp.Int (-200000000)) in
(*  let posInf_eq_maxInt = posInf =^= (Exp.Int max_int) in
  let negInf_eq_minInt = negInf =^= (Exp.Int min_int) in *)
  (* Upperbound + Lowerbound (to avoid bitVector bug? (see satcheck_eg/bitvectorbug.sat) *)
  let cUbIntVars = List.map (fun v -> Cmd.Ass (Exp.App("<",[Exp.Var v;posInf]))) vvInt in
  let cLbIntVars = List.map (fun v -> Cmd.Ass (Exp.App("<",[negInf;Exp.Var v]))) vvInt in
  let cUbNatVars = List.map (fun v -> Cmd.Ass (Exp.App("<",[Exp.Var v;posInf]))) vvNat in  
  let cLbNatVars = List.map (fun v -> Cmd.Ass (Exp.App("<=",[Exp.Int 0;Exp.Var v]))) vvNat in
  let commandsArith = 
    let cPosInf = [Cmd.DecVar(_PosInf,myInt);Cmd.Ass posInf_eq_maxInt] in
    let cNegInf = [Cmd.DecVar(_NegInf,myInt);Cmd.Ass negInf_eq_minInt] in
    let cDeclVars = List.map (fun v -> Cmd.DecVar (v,myInt)) (vvInt@vvNat) in
    cPosInf @ cNegInf @ cDeclVars @ cUbIntVars @ cLbIntVars @ cUbNatVars @ cLbNatVars @ commands
  in
  let commandsBV = 
    let cPosInf = [Cmd.DecVar(_PosInf,myBV32);Cmd.Ass posInf_eq_maxInt] in
    let cNegInf = [Cmd.DecVar(_NegInf,myBV32);Cmd.Ass negInf_eq_minInt] in
    let cDeclVars = List.map (fun v -> Cmd.DecVar (v,myBV32)) (vvInt@vvNat) in
    cPosInf @ cNegInf @ cDeclVars @ cUbIntVars @ cLbIntVars @ cUbNatVars @ cLbNatVars @ commands
  in
  try
    checkCommandsSwitch (Mode.Arithmetic "ufnia") modelflag ucflag vvInt vvNat commandsArith
  with
  | UNKNOWN ->
     begin
       dbgf "Z3" "@[UNKNOWN --> switch to BitVector BV[32]@.";
       try
         checkCommandsSwitch BitVector modelflag ucflag vvInt vvNat commandsBV
       with
       | UNKNOWN ->
          begin
            dbgf "Z3" "@[UNKNOWN --> switch to Arithmetic LIA@.";
            try
              checkCommandsSwitch (Mode.Arithmetic "lia") modelflag ucflag vvInt vvNat commandsArith
            with
            | UNKNOWN -> SatcheckResult.Unknown
          end
     end
;;    

let checkExpIntNat modelflag ucflag ee : SatcheckResult.t =
  let spvarNat = ["lambda"] in (* special variable names of nat type *)
  let vv = Strset.elements (Strset.mapUnion Exp.fv ee) in
  let vvInt = List.filter (fun v -> not (List.mem v spvarNat)) vv in
  let vvNat = List.filter (fun v -> List.mem v spvarNat) vv in  
  let cAssExpL = List.map (fun e -> Cmd.Ass e) ee in  
  let commands = cAssExpL @ [Cmd.CheckSat] in
  try
    checkCommandsAuto modelflag ucflag vvInt vvNat commands
  with
  | e -> print_endline "Exception from checkSatIntNat"; raise e
;;  

(* checkSatExp exp *)
let checkSatExp modelflag ucflag exp =
  dbgf "SATdebug" "@[------------------------------@.";  
  dbgf "SATdebug" "@[Input for checkSatExp@.";
  dbgf "SATdebug" "@[%a@." Exp.pp exp;
  dbgf "SATdebug" "@[------------------------------@.";
  let res =
    try
      checkExpIntNat modelflag ucflag [exp]
    with
    | e -> print_endline "Exception from checkSatExp"; raise e
  in
  res
;;

let checkSatExpBool exp =
  match checkExpIntNat false false [exp] with (* ~modelflag:false ~ucflag:false *)
  | Model _ -> true
  | UnsatCore _ -> false
  | _ -> false
;;

let checkSatExpBoolUnknown exp =
  match checkExpIntNat false false [exp] with (* ~modelflag:false ~ucflag:false *)
  | Model _ -> true
  | UnsatCore _ -> false
  | _ -> raiseMes "checkSatExpBoolUnknown" UNKNOWN
;;

let checkSatExpL modelflag ucflag ee =
  dbgf "SATdebug" "@[------------------------------@.";  
  dbgf "SATdebug" "@[Input for checkSatExpL@.";
  dbgf "SATdebug" "@[%a@." (pp_list_newline Exp.pp) ee;
  dbgf "SATdebug" "@[------------------------------@.";
  let res =
    try
      checkExpIntNat modelflag ucflag ee
    with
    | e -> print_endline "Exception from checkSatExpL"; raise e
  in
  res
;;


(* checkValidExp exp
checkValidExp E returns true
<-> checkSatExp (-E) returns an unsat_core
<-> (-E) has no model, i.e., (All M. M |/= -E)
<-> (All M. M |= E)
<-> E is valid
 *)
let checkValidExp timeout countermodel exp =
  match checkSatExp countermodel false (not' exp) with (* ~modelflag:countermodel ~ucflag:false *)
  (* (not exp) is sat <-> A counter-model for exp exists <-> exp is invalid *)
  | Model md -> (`INVALID,Some md)
  (* (not exp) is unsat <-> No counter-model for exp exists <-> exp is valid *)
  | UnsatCore _ -> (`VALID,None)
  | Unknown -> (`UNKNOWN,None)
;;


(* checkInconsExp exp
checkInconsExp E returns true
<-> checkSatExp E returns an unsat-core, i.e., (All M. M |/= E)
<-> E is inconsistent
*)
let checkInconsExp exp =
  match checkSatExp false false exp with (* ~modelflag:false ~ucflag:false *)
  | Model _ -> false
  | UnsatCore _ -> true
  | Unknown -> false
;;




