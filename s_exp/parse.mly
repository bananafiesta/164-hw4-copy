%{ open Exp %}

%token <int> NUMBER
%token <string> SYMBOL
%token <char> CHARACTER
%token <string> STRING
%token LPAREN RPAREN
%token EOF

%start <Exp.t> main

%%

main:
| e = expr EOF
        { e }

expr:
| n = NUMBER
  { Num n }
| c = CHARACTER
  { Chr c }
| s = STRING
  { Str s }
| s = SYMBOL
  { Sym s }
| LPAREN l=lst RPAREN
  { Lst l }

lst:
|   { [] }
| e = expr l = lst
    { e ::l }
