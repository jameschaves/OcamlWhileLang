%{
open Ast

(*)
   let next_id = ref 0;;
   let id () = let res = !next_id in
                 next_id := !next_id + 1;
                 res;; 

   let reset () = next_id := 0;;
   *)
%}

/* Token definitions */

%token <int> INT
%token <string> IDENT
%token ASSIGN
%token IF
%token SEMICOLON
%token ELSE THEN
%token WHILE DO
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
%token EOF

/* 
 Menhir allows you to specify how to resolve shift-reduce conflicts when it sees a .
 There are three options:
  %left  we reduce
  %right we shift
  %nonassoc raise a syntax error 
 We list the operators in order of precedence - from low to high.
 e.g. * has higher precedence than +  so 1 + 2 * 3  = 1 + (2 * 3)
*/

%right EQUAL
%left PLUS MINUS
%left TIMES
%left AND OR  

/* Specify starting production */

%start <Ast.stmt> prog

/* Definition types */

%type <stmt> stmt
%type <label> label
%type <bExp> bExp
%type <aExp> aExp

%type <binOp> binOp
%type <boolOp> boolOp
%type <relOp> relOp


%% /* Start grammar productions */


prog: 
    | main= stmt;  EOF { main }

/* Types */

condition_expr:
    | LBRACKET; b = bExp;  label = label; RBRACKET { Condition (e, label)} 

label:
    | LBRACKET; label = INT; RBRACKET { Label label }

stmt:
    | IF LBRACKET; b = bExp;  label = label; RBRACKET THEN LPAREN; then_expr = stmt; RPAREN ELSE LPAREN; else_expr = stmt; RPAREN { IfThenElse (b, then_expr, else_expr, label) }
    | WHILE LBRACKET; b = bExp;  label = label; RBRACKET DO LPAREN; loop_expr = stmt; RPAREN { While (b, loop_expr, label) }
    | SKIP; label = label { Skip (label) }
    | LBRACKET; id = IDENT; ASSIGN; assigned_expr = aExp; label = label; RBRACKET { Assignment (id, assigned_expr, label)}
    | LPAREN; s1 = stmt; SEMICOLON; s2 = stmt; RPAREN { Seq(s1, s2) }

aExp_with_paren:
    | LPAREN a = aExp RPAREN { a }

aExp:
    | i = INT { Int i }
    | id = IDENT { Ident id }
    | MINUS { Neg }
    | a1 = aExp; op = binOp; a2 = aExp { BinOp (op, a1, a2)}


bExp_with_paren:
    | LPAREN b = bExp RPAREN { b }

bExp:
    | TRUE { Bool (true) }
    | FALSE { Bool (false) }
    | NOT; b = bExp { Not (b) }
    | a1 = aExp; op = relOp; a2 = aExp { RelOp (op, a1, a2)}
    | b1 = bExp; op = boolOp; b2 = bExp { BoolOp (op, b1, b2)}

/* Operator expressions */

/* %inline expands occurrences of these 
    so rather than 
    unop e 
    we get two productions
     EXCLAMATION_MARK e 
     MINUS e 

*/


%inline binOp:
    | PLUS { Add }
    | MINUS { Sub }
    | TIMES { Mult }

%inline boolOp:
    | AND { And }
    | OR { Or }

%inline relOp:
    | EQUAL EQUAL { Eq }
    | NOT EQUAL { NotEq }
    | LT { Lt }
    | GT { Gt }
