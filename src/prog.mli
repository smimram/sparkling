(** Abstract representation of a program. *)
type 'a t =
  | Action of 'a action
  | Seq of 'a t list
  | Par of 'a t list
  | If of 'a * 'a t * 'a t
  | While of 'a * 'a t
  | Call of string * 'a list * (string option)
and 'a action =
  | P of string
  | V of string
  | Cmd of 'a

type 'a prog = 'a t

val to_string : 'a t -> string

(** Operation on positions in a program. *)
module Pos :
sig
  (** A position. *)
  type t =
    | PBot            (** Maximal position. *)
    | PTop            (** Minimal position. *)
    | PSeq of int * t
    | PPar of t list
    | PIf of bool * t
    | PWhile of t

  val to_string : 'a prog -> t -> string
  val to_string_simple : t -> string

  (** The minimal position. *)
  val bot : 'a prog -> t

  (** The maximal position. *)
  val top : 'a prog -> t

  (** Less or equal. *)
  val le : t -> t -> bool

  (** Greater or equal. *)
  val ge : t -> t -> bool

  (** Construct a subprogram of the program whose terminal position is the
    * specified position. *)
  (* val realize : 'a prog -> t -> 'a prog *)
end

(** Operations on intervals of a progam. *)
module Int :
sig
  (** An interval. *)
  type t

  (** The maximal interval. *)
  val everything : 'a prog -> t

  (** Ensure that an interval is valid (for debugging purposes since this should
    * always be [true]). *)
  val valid : t -> bool

  val make : Pos.t * Pos.t -> t

  val bounds : t -> Pos.t * Pos.t

  val to_string : 'a prog -> t -> string
  val to_string_simple : t -> string

  (** [included i j] tests whether [i] is included in [j]. *)
  val included : 'a prog -> t -> t -> bool

  (** Is a position within an interval? *)
  val belongs : 'a prog -> Pos.t -> t -> bool

  (** Intersection of two intervals. *)
  val meet : 'a prog -> t -> t -> t list

  val realize : 'a prog -> t -> 'a prog
end

(** Operations on regions, which are lists of intervals of a program. For
  * efficiency we mostly manipulated normalized regions in which the intervals are
  * all maximal. *)
module Region :
sig
  (** An region. *)
  type t = Int.t list

  val create : unit -> t

  val add : 'a prog -> Int.t -> t -> t

  val meet : 'a prog -> t -> t -> t

  val join : 'a prog -> t -> t -> t

  val to_string : 'a prog -> t -> string

  (** Ouput region in dot graph format. *)
  val to_dot : 'a prog -> t -> string

  (** Complement of an region. *)
  val compl : 'a prog -> t -> t

  (** [difference a b] computes [a] where the "complement" of [b] has been
    * removed. Notice that this might generate degenerated intervals which can
    * be removed with [nondegenerated]. *)
  val difference : 'a prog -> t -> t -> t

  (** Remove degenerated intervals. *)
  val nondegenerated : t -> t

  val normalize : 'a prog -> t -> t

  val deadlocks : 'a prog -> t -> Pos.t list

  val ginsu : t -> t

  (* val components : t -> t *)
end

module Flow_graph :
sig
  type 'a t

  val of_region : 'a prog -> ?no_squares:bool -> ?diagonals:bool -> Region.t -> 'a t

  val to_dot : 'a prog -> 'a t -> string

  val iter_breadth : (Pos.t -> 'a prog -> Pos.t -> unit) -> 'a t -> unit
end
