// Parser for Satcheck 2019/10/03

%{
open Slsyntax
open Tools                     
%}

%token <string> IDENT  // x, y, P, ...
%token <int> NUM

%token NIL      // "nil"                                    
%token AST      // '*'
%token PLUS     // '+'
%token MINUS	// '-'
%token MOD      // '%'
%token SLASH    // '/'
%token UMINUS
                                    
%token EQA       // '='
%token EQB       // "=="                                    
%token NEQA      // "<>"
%token NEQB      // "!="
%token NEQC      // "<>"
%token SHL      // "<<"
%token SHR      // ">>"
%token LE       // "<="
%token IMP      // "=>"                                    
%token GE       // ">="                                    
%token LT       // "<"                                    
%token GT       // ">" 
%token TRUE     // "True"
%token FALSE    // "False"
            
%token LPAREN   // '('
%token RPAREN   // ')'
%token LSQBRACKET // '['
%token RSQBRACKET // ']'
%token COMMA    // ','
%token COLON    // ':'
%token ATMARK   // '@'
%token DOLLAR   // '$'
%token SHARP    // '#'
%token QUESTION // '?'
%token HAT      // '^'
%token TILDE    // "~"/"BNOT"
                                    
%token EXint    // "Ex"
%token ALLint   // "All"
%token EXnat    // "Ex+"
%token ALLnat   // "All+"                                    
%token ARR  	// "Arr"
%token ARRAY  	// "Array"
%token STR  	// "Str"
%token STRINGPART 	// "Stringpart"
%token LS   	// "Ls"            
%token EMP  	// "Emp"
%token AND      // '&'
%token ANDAND   // "&&"
%token OR       // '|'
%token NOT      // "NOT" 
%token PTO      // "->"
%token VDASH    // "|-"
%token BAND     // "band"
%token BOR      // "bor"
%token BXOR     // "bxor"
%token DISJ     // "disj"
%token COMM     // "comm"
%token OUT      // "out"
                                    
%token EOF 

// Assoc priority
%nonassoc VDASH
%nonassoc ANDAND                                    
%nonassoc EXint EXnat ALLint ALLnat
%nonassoc COLON
%right IMP
%left OR            
%left AND
%nonassoc NOT
%left BAND
%left BXOR
%left BOR
%left AST                                    
%nonassoc EQA EQB NEQA NEQB NEQC
%nonassoc LE LT GT GE DISJ COMM OUT
%nonassoc PTO 
%left SHR SHL
%left PLUS MINUS 
%left MOD SLASH UAST
%left TILDE LSQBRACKET UMINUS 
%left VAR NIL EMP LPAREN ATMARK DOLLAR

%start main
%type <Slsyntax.QFSH.t> main
%type <string list> ident_seq
%type <SHterm.t> term
%type <SHspat.t> spat
%type <SHpure.t> pure
%type <QFSH.t> qfsh
%%

// 
main:
  | qfsh EOF
     { $1 }
;

ident_seq:
  | IDENT
      { [$1] }
  | ident_seq COMMA IDENT
      { $1 @ [$3] }
  | LPAREN ident_seq RPAREN
	  { $2 }
;

var_attriv_one:
  | IDENT
      {
        match $1 with
        | "PTR" | "ptr" -> Attr.PTR
        | "EXQ" | "exq" -> Attr.EXQ
        | "PARAM" | "param" -> Attr.PARAM
        | "PTRPTR" | "ptrptr" -> Attr.PTRPTR
        | "GLOBAL" | "global" -> Attr.GLOBAL
        | "HAT" | "hat" -> Attr.HAT
        | "BAR" | "bar" -> Attr.BAR
        | "EXTERN" | "extern" -> Attr.EXTERN
        | "TILDE" | "tilde" -> Attr.TILDE
        | "CHECK" | "check" -> Attr.CHECK
        | "DOT" | "dot" -> Attr.DOT
        | "QUESTION" | "question" -> Attr.QUESTION
        | "AQUTE" | "acute" -> Attr.ACUTE
        | "INDIRECT" | "indirect" -> Attr.INDIRECT
        | "PROTO" | "proto" -> Attr.PROTO
        | "ARRAY" | "array" -> Attr.ARRAY [1] 
        | _ -> Attr.STRUCT $1
      }
;
  
var_attriv:
  | ATMARK var_attriv_one
      { Attrs.singleton $2 }
  | var_attriv ATMARK var_attriv_one
      { Attrs.add $3 $1 }
;

variable:
  | SHARP IDENT var_attriv
      { SHterm.Var ("#"^$2,$3) }
  | IDENT var_attriv
      { SHterm.Var ($1,$2) }
  | IDENT 
      { SHterm.Var ($1,Attrs.empty) }
;

bvariable:  // used for quantifiers
  | SHARP IDENT var_attriv
      { "#"^$2 }
  | IDENT var_attriv
      { $1 }
  | IDENT 
      { $1 }
;

bvariable_seq:
  | bvariable
      { Strset.singleton $1 }
  | bvariable_seq COMMA bvariable
      { Strset.add $3 $1 }
  | LPAREN bvariable_seq RPAREN
	  { $2 }
;
  
term:
  | IDENT LPAREN term_seq RPAREN
      { SHterm.Fcall ($1,$3) }
  | variable
      { $1 }
  | NUM
      { SHterm.Int $1 }
  | NIL
      { SHterm.Int 0 }
  | term PLUS term
      { SHterm.Add [$1;$3] }
  | term PLUS MINUS term
      { SHterm.Sub [$1;$4] }
  | term MINUS term
      { SHterm.Sub [$1;$3] }
  | term MOD term
      { SHterm.Mod ($1,$3) }
  | term AST term %prec UAST
      { SHterm.Mul ($1,$3) }
  | term SLASH term
      { SHterm.Div ($1,$3) }
  | term SHR term
      { SHterm.Shr ($1,$3) }
  | term SHL term
      { SHterm.Shl ($1,$3) }
  | term BAND term
      { SHterm.Band ($1,$3) }
  | term BOR term
      { SHterm.Bor ($1,$3) }
  | term BXOR term
      { SHterm.Bxor ($1,$3) }
  | TILDE term
      { SHterm.Bnot $2 }
  | MINUS term %prec UMINUS
      { SHterm.Sub [SHterm.Int 0;$2] }
  | LPAREN term RPAREN
      { $2 }
  | error
    { 
      let message =
        Printf.sprintf 
          "parse error at line %d:%d-%d"
          ((Parsing.symbol_start_pos ()).Lexing.pos_lnum)
		  (Parsing.symbol_start ())
		  (Parsing.symbol_end ())
	    in
	    failwith message
    }	  
;

term_seq:
  | term
      { [$1] }
	  
  | term_seq COMMA term
      { $1 @ [$3] }

  | LPAREN term_seq RPAREN
	  { $2 }
	  
  | error
    { 
      let message =
        Printf.sprintf 
          "parse error (term_seq) near characters %d-%d"
          (Parsing.symbol_start ())
	      (Parsing.symbol_end ())
	    in
	    failwith message
    }	  	  
;
  
termpf:
  | IDENT LPAREN termpf_seq RPAREN
      { SHterm.Fcall ($1,$3) }
  | variable
      { $1 }
  | NUM
    { SHterm.Int $1 }
  | LPAREN PLUS termpf_seq RPAREN
      { SHterm.Add $3 }
  | LPAREN MINUS termpf_seq RPAREN
      { SHterm.Sub $3 }
  | LPAREN MOD termpf termpf RPAREN
      { SHterm.Mod ($3,$4) }
  | LPAREN AST termpf termpf RPAREN
      { SHterm.Mul ($3,$4) }
  | LPAREN SLASH termpf termpf RPAREN
      { SHterm.Div ($3,$4) }
  | LPAREN SHR termpf termpf RPAREN
      { SHterm.Shr ($3,$4) }
  | LPAREN SHL termpf termpf RPAREN
      { SHterm.Shl ($3,$4) }
  | LPAREN BAND termpf termpf RPAREN
      { SHterm.Band ($3,$4) }
  | LPAREN BAND termpf termpf RPAREN
      { SHterm.Bor ($3,$4) }
  | LPAREN BXOR termpf termpf RPAREN
      { SHterm.Bxor ($3,$4) }
  | LPAREN TILDE termpf RPAREN
      { SHterm.Bnot $3 }
  | MINUS termpf %prec UMINUS
      { SHterm.Sub [SHterm.Int 0;$2] }
  | LPAREN termpf RPAREN
      { $2 }
  | error
    { 
      let message =
        Printf.sprintf 
          "parse error at line %d:%d-%d"
          ((Parsing.symbol_start_pos ()).Lexing.pos_lnum)
		  (Parsing.symbol_start ())
		  (Parsing.symbol_end ())
	    in
	    failwith message
    }	  
;

termpf_seq:
  | termpf
      { [$1] }
  | termpf_seq termpf
      { $1 @ [$2] }
  | error
    { 
      let message =
        Printf.sprintf 
          "parse error (term_seq) near characters %d-%d"
          (Parsing.symbol_start ())
	      (Parsing.symbol_end ())
	    in
	    failwith message
    }	  	  
;
  
fieldterm:
  | term
      { ("",$1) }
  | AST COLON term
      { ("*",$3) }
  | IDENT COLON term
      { ($1,$3) }
;

fieldterm_seq:
  | fieldterm
      { [$1] }
  | fieldterm COMMA fieldterm_seq
      { $1 :: $3 }
;
  
term_interval:
  | LSQBRACKET term COMMA term RSQBRACKET
      { ($2,$4) }
;

pure_atom:
  | TRUE
      { P.True }
  | FALSE
      { P.False }
  | term EQA term
      { P.Atom(P.Eq,[$1;$3]) }
  | term EQB term
      { P.Atom(P.Eq,[$1;$3]) }
  | term NEQA term
      { P.Atom(P.Neq,[$1;$3]) }
  | term NEQB term
      { P.Atom(P.Neq,[$1;$3]) }
  | term NEQC term
      { P.Atom(P.Neq,[$1;$3]) }
  | term LT term
      { P.Atom(P.Lt,[$1;$3]) }
  | term LE term
      { P.Atom(P.Le,[$1;$3]) }
  | term GT term
      { P.Atom(P.Lt,[$3;$1]) }
  | term GE term
      { P.Atom(P.Le,[$3;$1]) }
  | term_interval DISJ term_interval
      {
        let (t0,t1) = $1 in
        let (t2,t3) = $3 in
        P.Atom(Disj,[t0;t1;t2;t3])
      }
  | term_interval COMM term_interval
      {
        let (t0,t1) = $1 in
        let (t2,t3) = $3 in
        P.Atom(Comm,[t0;t1;t2;t3])
      }
  | term OUT term_interval
      {
        let (t1,t2) = $3 in
        P.Atom(Out,[$1;t1;t2])
      }
  | LPAREN pure RPAREN
      { $2 }
;
  
pure:
  | pure_atom
      { $1 }
  | pure AND pure
      { P.And [$1;$3] }
  | pure OR pure
      { P.Or [$1;$3] }
  | pure IMP pure
      { P.Imp ($1,$3) }
  | NOT pure 
      { P.Neg $2}
  | ALLint bvariable_seq pure
      { P.All(P.Int,$2,$3) }
  | EXint bvariable_seq pure
      { P.Ex(P.Int,$2,$3) }
  | ALLnat bvariable_seq pure
      { P.All(P.Nat,$2,$3) }
  | EXnat bvariable_seq pure
      { P.Ex(P.Nat,$2,$3) }
;      

pure_and:
  | pure AND
      { $1 }
;

purepf_atom:
  | TRUE
      { P.True }
  | FALSE
      { P.False }
  | LPAREN EQA termpf termpf RPAREN
      { P.Atom(P.Eq,[$3;$4]) }
  | LPAREN EQB termpf termpf RPAREN
      { P.Atom(P.Eq,[$3;$4]) }
  | LPAREN NEQA termpf termpf RPAREN
      { P.Atom(P.Neq,[$3;$4]) }
  | LPAREN NEQB termpf termpf RPAREN
      { P.Atom(P.Neq,[$3;$4]) }
  | LPAREN NEQC termpf termpf RPAREN
      { P.Atom(P.Neq,[$3;$4]) }
  | LPAREN LT termpf termpf RPAREN      
      { P.Atom(P.Lt,[$3;$4]) }
  | LPAREN LE termpf termpf RPAREN      
      { P.Atom(P.Le,[$3;$4]) }
  | LPAREN GT termpf termpf RPAREN      
      { P.Atom(P.Lt,[$4;$3]) }
  | LPAREN GE termpf termpf RPAREN      
      { P.Atom(P.Le,[$4;$3]) }
  | LPAREN term_interval DISJ term_interval RPAREN
      {
        let (t0,t1) = $2 in
        let (t2,t3) = $4 in
        P.Atom(Disj,[t0;t1;t2;t3])
      }
  | LPAREN term_interval COMM term_interval RPAREN
      {
        let (t0,t1) = $2 in
        let (t2,t3) = $4 in
        P.Atom(Comm,[t0;t1;t2;t3])
      }
  | LPAREN purepf RPAREN
      { $2 }

;

purepf:
  | purepf_atom
      { $1 }
  | LPAREN AND purepf_seq RPAREN
      { P.And $3 }
  | LPAREN OR purepf_seq RPAREN      
      { P.Or $3 }
  | LPAREN IMP purepf purepf RPAREN      
      { P.Imp ($3,$4) }
  | LPAREN NOT purepf RPAREN      
      { P.Neg $3}
  | LPAREN ALLint bvariable_seq purepf RPAREN
      { P.All(P.Int,$3,$4) }
  | LPAREN EXint bvariable_seq purepf RPAREN
      { P.Ex(P.Int,$3,$4) }
  | LPAREN ALLnat bvariable_seq purepf RPAREN
      { P.All(P.Nat,$3,$4) }
  | LPAREN EXnat bvariable_seq purepf RPAREN
      { P.Ex(P.Nat,$3,$4) }
;      

purepf_and:
  | purepf AND
      { $1 }
;

purepf_seq:
  | purepf
      { [$1] }
  | purepf_seq purepf
      { $1 @ [$2] }
  | error
    { 
      let message =
        Printf.sprintf 
          "parse error (term_seq) near characters %d-%d"
          (Parsing.symbol_start ())
	      (Parsing.symbol_end ())
	    in
	    failwith message
    }	  	  
;
  
spat_atom:
  | term PTO LPAREN RPAREN	// t -> ()
     { S.Pto($1,[]) }    
  | term PTO LPAREN fieldterm_seq RPAREN	// t -> (f1:t1,f2:t2)
     { S.Pto($1,$4) }
  | ARR LPAREN term COMMA term RPAREN	// Arr ( t,t )
     { S.Arr($3,$5) }
  | ARRAY LPAREN term COMMA term RPAREN	// Array ( t,t )
     { S.Arr($3,$5) }  
  | STR LPAREN term COMMA term RPAREN	// Str ( t,t )
     { S.Str($3,$5) }
  | STRINGPART LPAREN term COMMA term RPAREN	// Stringpart ( t,t )
     { S.Str($3,$5) }  
  | LS LPAREN term COMMA term RPAREN // Ls(t,t)
     { S.Ind("Ls",[$3;$5]) }
;

spat:
  | EMP
      { [] }
  | spat_atom
      { [$1] }
  | spat_atom AST spat
      { $1 :: $3 }
;

qfsh:
  | spat
      { (P.True,$1) }
  | pure ANDAND spat
      { ($1,$3) }
  | pure AND spat
      { ($1,$3) }
  | purepf ANDAND spat
      { ($1,$3) }
;
