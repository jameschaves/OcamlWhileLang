%{
open Ast
%}

%token <Ast.aExp> AEXP
%token <Ast.label> LABEL

%token <int> NUM
%token <string> VAR
%token ASSIGN
%token SKIP
%token PLUS
%token MINUS
%token TIMES
%token EQUAL
%token TRUE
%token FALSE
%token NOT
%token AND
%token OR
%token GT
%token LT
%token LPAREN
%token RPAREN
%token LBRACKET
%token RBRACKET
%token LCURLYBRACKET
%token RCURLYBRACKET
%token EOF

%left PLUS
%left MINUS
%left TIMES

%start  prog

%type <Ast.expr> prog

%%

prog:
    | e = expr; EOF { e }
    ;

expr:
    | SKIP; l = expr { Skip(l) }
    | n = NUM { Num n }
    | a = VAR { Var a }
    | e1 = expr; TIMES; e2 = expr { AExp (Mult, e1, e2) }
    | e1 = expr; PLUS; e2 = expr { AExp (Add, e1, e2) }
    | e1 = expr; MINUS; e2 = expr { AExp (Sub, e1, e2) }
    | e1 = expr; AND; e2 = expr { BExp (And, e1, e2) }
    | e1 = expr; OR; e2 = expr { BExp (Or, e1, e2) }
    | e1 = expr; EQUAL; e2 = expr { BExp (Eq, e1, e2) }
    | e1 = expr; GT; e2 = expr { BExp (Gt, e1, e2) }
    | e1 = expr; LT; e2 = expr { BExp (Lt, e1, e2) }
    | TRUE { True }
    | FALSE { False } 
    | NOT; b = expr { Not (b) }
    | x = VAR; ASSIGN; e1 = AEXP; l = LABEL { Stmt(Assignment (x, e1, l)) }
    | LPAREN; e = expr; RPAREN { e }
    | LBRACKET; e = expr; RBRACKET { e }
    | LCURLYBRACKET; e = expr; RCURLYBRACKET { e }
 
    // | x = expr; ASSIGN; e1 = expr; e2 = expr { Assignment(Str x, AExp e1, Label e2) }
    ;