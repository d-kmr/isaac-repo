(* Lexer for slsyntax 2019/05/11 *)
(* Modified 2019/08/05 for biabduction extention *)
(* Modified 2021/05/30 to add binary operations *)

{
  open Satcheck_parser
}

let space = [' ' '\t']
let eol = ['\n' '\r']
let digit = ['0'-'9']
let alpha = ['A'-'Z' 'a'-'z' '_']
let alnum = digit | alpha | '\'' | '?'
let comment = "//"
  
rule token = parse
  | "<<"      { SHL }
  | ">>"      { SHR }
  | '<'       { LT }
  | "<="      { LE }
  | '>'       { GT }  
  | ">="      { GE }
  | "=>"      { IMP }
  | '+'       { PLUS }
  | '-'       { MINUS }
  | '%'       { MOD }
  | '/'       { SLASH }
  | '*'       { AST }
  | '='       { EQA }
  | "=="      { EQB }  
  | "!="      { NEQA }
  | "=/"      { NEQB }  
  | "<>"      { NEQC }
  | "True"    { TRUE }
  | "False"   { FALSE }  
  | '('       { LPAREN }
  | ')'       { RPAREN }
  | '['       { LSQBRACKET }
  | ']'       { RSQBRACKET }
  | ':'       { COLON }
  | ','       { COMMA }
  | '@'       { ATMARK }
  | "$"       { DOLLAR }
  | "#"       { SHARP }
  | "?"       { QUESTION }
  | "~"       { TILDE }
  | "disj"    { DISJ }
  | "comm"    { COMM }
  | "out"     { OUT }
  | "nil"     { NIL }
    
  | "EXint"   { EXint }
  | "ALLint"  { ALLint }
  | "EXnat"   { EXnat }
  | "ALLnat"  { ALLnat }
  | "exists-int"  { EXint }
  | "forall-int"  { ALLint }
  | "exists-int"  { EXnat }
  | "forall-nat"  { ALLnat }
  | "AND"     { AND }
  | "and"     { AND }  
  | "IMP"     { IMP }
  | "imp"     { IMP }    
  | "OR"      { OR }
  | "or"      { OR }  
  | "NOT"     { NOT }
  | "not"     { NOT }  
  | "Arr"     { ARR }
  | "Array"   { ARRAY }
  | "Ls"      { LS }
  | "List"    { LS }    
  | "Str"     { STR }
  | "Stringpart" { STRINGPART }
  | "Emp"     { EMP }
  | "band"    { BAND }
  | "bor"     { BOR }
  | "bxor"    { BXOR }
  | '&'       { AND }
  | "&&"      { ANDAND }
  | "||"      { OR }  
  | '|'       { OR }
  | "->"      { PTO }
  | "|-"      { VDASH }
  | alpha alnum*
    { IDENT (Lexing.lexeme lexbuf) }
  | '\n'
      {
        Lexing.new_line lexbuf;
        token lexbuf
      }
  | digit*      { NUM (int_of_string (Lexing.lexeme lexbuf)) }
  | eof         { EOF }
  | space+      { token lexbuf }
  | comment [^ '\n' '\r']* eol { token lexbuf }
  | _
      {
        Format.printf "@[Parse Error (line %d), Unexpected Input: %s@."
          (lexbuf.lex_start_p.pos_lnum)
          (Lexing.lexeme lexbuf);
        exit 0        
      }

and comment = parse
  | eol     { token lexbuf }
  | eof     { EOF }            
  | _       { comment lexbuf }    
