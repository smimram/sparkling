%{
    open Prog
    open Lang
%}

%token LPAR RPAR PAR LACC RACC SEMICOLON COMMA
%token IF THEN ELSE RETURN NOT WHILE
%token T_VOID T_BOOL T_INT T_MUTEX
%token ISEQ LE LT EQ PLUS MINUS MULT AND OR
%token INCR DECR
%token ASSERT
%token EOF
%token P V ATOMIC
%token <string> IDENT
%token <int> V_INT
%token <bool> V_BOOL

%left PAR
%nonassoc ELSE
%nonassoc WHILE
%left OR
%left AND
%nonassoc LE LT
%left ISEQ
%left PLUS MINUS
%left MULT
%nonassoc NOT
%left DOT SEMICOLON

%start main
%type <Lang.declaration list> main
%%

main:
    | declarations EOF { $1 }

declarations:
    | { [] }
    | declaration declarations { $1::$2 }

declaration:
    | typ IDENT LPAR declaration_arguments RPAR instr { ($1, $2, Some $4, $6) }
    | typ IDENT SEMICOLON { ($1, $2, None, Seq []) }

declaration_arguments:
    | { [] }
    | typ IDENT declaration_arguments { ($1,$2)::$3 }

instrs:
    | instr SEMICOLON instrs { $1::$3 }
    | { [] }

instr:
    | LACC instrs RACC { Seq $2 }
    | action { Action $1 }
    | IF expr instr ELSE instr { If ($2,$3,$5) }
//    | IF expr instr { If ($2,$3,Seq []) }
    | WHILE expr instr { While ($2,$3) }
    | instr PAR instr { Par [$1; $3] }
    | IDENT LPAR expr_list RPAR { Call ($1,$3,None) }
    | IDENT EQ IDENT LPAR expr_list RPAR { Call ($3,$5,Some $1) }

action:
    | P LPAR IDENT RPAR { P $3 }
    | V LPAR IDENT RPAR { V $3 }
    | command { Cmd $1 }

command:
    | ASSERT expr { EAssert $2 }
    | RETURN expr { EReturn $2 }
    | IDENT EQ expr { EAssign ($1, $3) }
    | IDENT INCR { EAssign ($1, EAdd (EVar $1, EInt 1)) }
    | IDENT DECR { EAssign ($1, ESub (EVar $1, EInt 1)) }
    | typ IDENT { ENew_var ($1, $2) }

typ:
    | T_VOID { TVoid }
    | T_BOOL { TBool }
    | T_INT { TInt }
    | T_MUTEX { TMutex }

expr:
    | IDENT { EVar $1 }
    | V_INT { EInt $1 }
    | V_BOOL { EBool $1 }
    | NOT expr { ENot $2 }
    | expr PLUS expr { EAdd ($1,$3) }
    | expr MINUS expr { ESub ($1,$3) }
    | expr MULT expr { EMult ($1,$3) }
    | expr ISEQ expr { EIs_eq ($1,$3) }
    | expr AND expr { EAnd ($1,$3) }
    | expr OR expr { EOr ($1,$3) }
    | expr LE expr { ELe ($1,$3) }
    | expr LT expr { ELt ($1,$3) }
    | LPAR expr RPAR { $2 }

expr_list:
    | { [] }
    | expr { [$1] }
    | expr COMMA expr_list { $1::$3 }
