{
    open Lexing

    open Parser

    exception SyntaxError of string

    let next_line lexbuf =
        let pos = lexbuf.lex_curr_p in
            lexbuf.lex_curr_p <-
            { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
            }
}

(* This defines the reserved keywords used in the definition of Identifier *)
let myKeywords = "if" | "then" | "else" | "while" | "skip" | "end" | "return" | "call" | "proc" | "is"

(* Define helper regexes *)
let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']

let int = '-'? digit+  (* regex for integers *)
let identifier = (alpha) (alpha|digit|'_')* (* regex for identifier *)
let whitespace = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

let natural = digit+

rule read_token = 
    parse 
    | "true" { TRUE }
    | "false" { FALSE }  
    | ":=" { ASSIGN }
    | "if" { IF }
    | ";" { SEMICOLON }
    | "else" { ELSE }
    | "then" { THEN }
    | "while" { WHILE }
    | "do" { DO }
    | "skip" { SKIP }
    | "!" { NOT }
    | "=" { EQUAL }
    | "&&" { AND }
    | "||" { OR }
    | ">" { GT}
    | "<" { LT }
    (* | identifier ":=*[" natural "]" { ASSIGN } *)
    | "*" { TIMES }
    | "+" { PLUS }
    | "-" { MINUS }
    | "(" { LPAREN }
    | ")" { RPAREN }
    | "[" { LBRACKET }
    | "]" { RBRACKET }
    | int { INT (int_of_string (Lexing.lexeme lexbuf)) }
    | identifier { VAR (Lexing.lexeme lexbuf)}
    | whitespace { read_token lexbuf }
    | "//" { read_single_line_comment lexbuf (* use our comment rule for rest of line *) }
    | "/*" { read_multi_line_comment lexbuf }    
    (* | '"'      { read_string (Buffer.create 17) lexbuf } *)
    | newline { next_line lexbuf; read_token lexbuf }
    | eof { EOF }
    | _ {raise (SyntaxError ("Lexer - Illegal character: " ^ Lexing.lexeme lexbuf)) }

and read_single_line_comment = parse
  | newline { next_line lexbuf; read_token lexbuf }
  | eof { EOF }
  | _ { read_single_line_comment lexbuf }

and read_multi_line_comment = parse
  | "*/" { read_token lexbuf }
  | newline { next_line lexbuf; read_multi_line_comment lexbuf }
  | eof { raise (SyntaxError ("Lexer - Unexpected EOF - please terminate your comment.")) }
  | _ { read_multi_line_comment lexbuf }

(* and read_string buf = parse
  | '"'       { STRING (Buffer.contents buf) }
  | '\\' 'n'  { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | [^ '"' '\\']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string buf lexbuf
    }
  | _ { raise (SyntaxError ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof { raise (SyntaxError ("String is not terminated")) } *)

