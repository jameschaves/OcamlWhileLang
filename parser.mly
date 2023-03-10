%{
open Ast

(**
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
%token ELSE THEN END WHILE DO
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


%left PLUS MINUS
%left TIMES
%left AND OR  
%right SEMICOLON

/* Specify starting production */

%start <Ast.expr> prog

/* Definition types */


%type <label> label

%% /* Start grammar productions */


prog: 
    | main= stmt; option(SEMICOLON);  EOF { main }
    | opAExp = aExpWithCompl; EOF { opAExp } 
    | opBExp = bExpWithCompl; EOF { opBExp } 

/* Types */

condition_expr:
    | LBRACKET; b = bExp; RBRACKET; label = label { Condition (b, label)} 

label:
    | LBRACKET; label = INT; RBRACKET; { Label label }

stmt:
    | IF; cond_expr = condition_expr; THEN; then_expr = stmt; ELSE ; else_expr = stmt; END { IfThenElse (cond_expr, then_expr, else_expr) }
    | WHILE; cond_expr = condition_expr; DO; loop_expr = stmt; END { While ( cond_expr, loop_expr) }
    | SKIP; label = label; { Skip (label) }
    | LBRACKET; id = IDENT; ASSIGN; assigned_expr = aExp; RBRACKET; label = label { Assignment (id, assigned_expr, label)}
    | s1 = stmt; SEMICOLON; s2 = stmt { Seq(s1, s2) }

aExpWithCompl:
    | option(LBRACKET); option(LPAREN); a = aExp; option(RPAREN); option(RBRACKET) { a }

aExp:
    | i = INT { Int i }
    | id = IDENT { Ident id }
    | MINUS { Neg }
    | a1 = aExp; op = binOp; a2 = aExp { BinOp (op, a1, a2)}

bExpWithCompl:
    | option(LBRACKET); option(LPAREN); b = bExp; option(RPAREN); option(RBRACKET) { b }

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
