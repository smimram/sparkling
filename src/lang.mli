(** Description and manipulation of a toy programming language. *)

(** A type. *)
type type_expr =
  | TVoid  (** void *)
  | TBool  (** boolean *)
  | TInt   (** integer *)
  | TMutex (** mutex *)

val string_of_type_expr : type_expr -> string

(** An expression. *)
type expr =
  | EAssign of string * expr
  | ENew_var of type_expr * string
  | EAssert of expr
  | EReturn of expr
  | EVar of string
  | EInt of int
  | EBool of bool
  | EAdd of expr * expr
  | ESub of expr * expr
  | ENot of expr
  | EMult of expr * expr
  | EDiv of expr * expr
  | EIs_eq of expr * expr
  | ELe of expr * expr
  | ELt of expr * expr
  | EAnd of expr * expr
  | EOr of expr * expr

val string_of_expr : expr -> string

val disjunctive_normal_form : expr -> expr list list

val string_of_constr : expr -> string

val string_of_action : expr Prog.action -> string

(** A program. *)
type t = expr Prog.t

val to_string : t -> string

(** A program consists of a list of declarations of functions and variables. *)
type declaration =
  type_expr (** type *)
  * string (** name *)
  * ((type_expr * string) list) option (** arguments, [None] means variable *)
  * t (** the program *)

val inline : declaration list -> t -> t

(** Intervals where a mutex is taken. *)
val brackets : t -> (string * Prog.Int.t) list

(** Forbidden area. *)
val forbidden : t -> Prog.Area.t

(** Allowed area. *)
val allowed : t -> Prog.Area.t

(*
(** Components. *)
val components : t -> Prog.Area.t * Prog.CArea.t
*)
