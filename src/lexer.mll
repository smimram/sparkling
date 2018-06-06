{
    open Lexing

    let on_newline lexbuf =
      let pos = lexbuf.lex_curr_p in
        lexbuf.lex_curr_p <-
          {
            pos with
            pos_lnum = pos.pos_lnum + 1;
            pos_bol = pos.pos_cnum;
          }

    open Parser
}

let space = ' ' | '\t' | '\r'

rule token = parse
  | "//"[^'\n']* { token lexbuf }
  | "(" { LPAR }
  | ")" { RPAR }
  | "{" { LACC }
  | "}" { RACC }
  | "|" { PAR }
  | "+" { PLUS }
  | "-" { MINUS }
  | "*" { MULT }
  | "!" { NOT }
  | "&&" { AND }
  | "||" { OR }
  | "=" { EQ }
  | "==" { ISEQ }
  | "<=" { LE }
  | "<" { LT }
  | "," { COMMA }
  | ";" { SEMICOLON }
  | "++" { INCR }
  | "--" { DECR }
  | "lock" { P }
  | "unlock" { V }
  | "void" { T_VOID }
  | "bool" { T_BOOL }
  | "int" { T_INT }
  | "mutex" { T_MUTEX }
  | "if" { IF }
  | "then" { THEN }
  | "else" { ELSE }
  | "true" { V_BOOL true }
  | "false" { V_BOOL false }
  | "return" { RETURN }
  | "while" { WHILE }
  | "atomic" { ATOMIC }
  | "assert" { ASSERT }
  | ('-'?['0'-'9']+ as n) { V_INT (int_of_string n) }
  | (['a'-'z''A'-'Z''0'-'9''_']+ as str) { IDENT str }
  | space+ { token lexbuf }
  | '\n' { on_newline lexbuf; token lexbuf }
  | eof { EOF }
