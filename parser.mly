%{
open Ast
%}

/* Token definitions */

%token <int> INT
%token <string> VAR
%token ASSIGN
%token IF
%token SEMICOLON
%token ELSE
%token WHILE
%token DO
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

%start <Ast.program> program

//%start prog
//%type <Ast.program> prog

/* Definition types */

%type <block_expr> main_expr
%type <block_expr> block_expr
%type <expr> expr

%type <condition_expr> condition_expr
%type <label_expr> label_expr

%type <unop> unop
%type <binop> binop
%% /* Start grammar productions */


program: 
| main= main_expr;  EOF { Prog (main) }

/* Types */

main_expr:
| exprs = block_expr { exprs }

block_expr:
// | s1 = expr; SEMICOLON; exprs = separated_list(SEMICOLON, expr) {Seq (exprs)}  
// | LBRACKET; exprs = separated_list(SEMICOLON, expr); LBRACKET {Seq (exprs)}  
// | s1 = expr; SEMICOLON; s2 = expr { Seq (s1, s2) }  
    | stmtExprs = separated_list(SEMICOLON, stmt) {Stmt (stmtExprs)}  

identifier:
// | variable = VAR { Variable (Var_name.of_string variable) }
| variable = VAR { Variable (variable) }

condition_expr:
    | LBRACKET; e = expr;  label = label_expr; RBRACKET { Condition (e, label)} 

label_expr:
    | LBRACKET; label = expr; RBRACKET { Label label }

stmt:
    // | LBRACKET; e = expr ; RBRACKET { e }
    | LBRACKET; id = identifier; ASSIGN; assigned_expr = expr; label = label_expr; RBRACKET { Assignment (id, assigned_expr, label)}
    | WHILE; cond_expr = condition_expr; DO LPAREN; loop_expr = block_expr; RPAREN { While ( cond_expr, loop_expr) }
    | SKIP; label = label_expr { Skip (label) }
    | IF; cond_expr = expr; then_expr = block_expr; ELSE; else_expr = block_expr { IfThenElse (cond_expr, then_expr, else_expr) }

expr:
    | LPAREN e = expr RPAREN { e }
    // | LBRACKET; e = expr; RBRACKET { e }
    | i = INT { Int i }
    | var = VAR { Var var }
    | TRUE { Bool true }
    | FALSE { Bool false }
    | op = unop e = expr { Unop (op, e)}
    | e1 = expr; op = binop; e2 = expr { Binop (op, e1, e2)}
    // | id = identifier; ASSIGN; assigned_expr = expr; LBRACKET; label = expr; RBRACKET { Assignment (id, assigned_expr, label)}
    // | SKIP; label = expr { Skip (label) }
    // | s1 = expr; SEMICOLON; s2 = expr { Seq (s1, s2) }  
    // | IF; cond_expr = expr; then_expr = block_expr; ELSE; else_expr = block_expr { IfThenElse (cond_expr, then_expr, else_expr) }
    // | WHILE cond_expr = expr; loop_expr = block_expr { While ( cond_expr, loop_expr) }


/* Operator expressions */

/* %inline expands occurrences of these 
    so rather than 
    unop e 
    we get two productions
     EXCLAMATION_MARK e 
     MINUS e 

*/

%inline unop:
    | NOT { Not }
    | MINUS { Neg }

%inline binop:
    | PLUS { Add }
    | MINUS { Sub }
    | TIMES { Mult }
    | AND { And }
    | OR { Or }
    | EQUAL EQUAL { Eq }
    | NOT EQUAL { NotEq }
    | LT { Lt }
    | GT { Gt }
