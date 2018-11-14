
(* This file is free software. See file "license" for more details. *)

(** {1 Bindings to Batsat} *)

type t
(** An instance of batsat (stateful) *)

type 'a printer = Format.formatter -> 'a -> unit

module Lit : sig
  type t = private int
  (** Some representation of literals that will be accepted by the SAT solver. *)

  val equal : t -> t -> bool
  val hash : t -> int
  val compare : t -> t -> int

  val make : int -> t
  (** [make n] creates the literal whose index is [n].
      {b NOTE} [n] must be strictly positive. Use {!neg} to obtain
      the negation of a literal. *)

  val neg : t -> t
  (** Negation of a literal.
      Invariant: [neg (neg x) = x] *)

  val abs : t -> t
  (** Absolute value (removes negation if any). *)

  val sign : t -> bool
  (** Sign: [true] if the literal is positive, [false] for a negated literal.
      Invariants:
      [sign (abs x) = true]
      [sign (neg x) = not (sign x)]
  *)

  val to_int : t -> int
  val to_string : t -> string
  val pp : t printer
end

type assumptions = Lit.t array

module Raw : sig
  type lbool = int (* 0,1,2 *)
  external create : unit -> t = "ml_batsat_new"
  external delete : t -> unit = "ml_batsat_delete"

  (* the [add_clause] functions return [false] if the clause
     immediately makes the problem unsat *)

  external simplify : t -> bool = "ml_batsat_simplify"

  external add_lit : t -> Lit.t -> bool = "ml_batsat_addlit"
  external assume : t -> Lit.t -> unit = "ml_batsat_assume"
  external solve : t -> bool = "ml_batsat_solve"

  external nvars : t -> int = "ml_batsat_nvars"
  external nclauses : t -> int = "ml_batsat_nclauses"
  external nconflicts : t -> int = "ml_batsat_nconflicts"

  external value : t -> Lit.t -> lbool = "ml_batsat_value"
  external check_assumption: t -> Lit.t -> bool = "ml_batsat_check_assumption"
  external unsat_core: t -> Lit.t array = "ml_batsat_unsat_core"

  external n_proved: t -> int = "ml_batsat_n_proved"
  external get_proved: t -> int -> Lit.t = "ml_batsat_get_proved"
  external value_lvl_0 : t -> Lit.t -> lbool = "ml_batsat_value_lvl_0"
end

val create : unit -> t

exception Unsat

val add_clause_l : t -> Lit.t list -> unit
(** @raise Unsat if the problem is unsat *)

val add_clause_a : t -> Lit.t array -> unit
(** @raise Unsat if the problem is unsat *)

val pp_clause : Lit.t list printer

val simplify : t -> unit
(** @raise Unsat if the problem is unsat *)

val solve : ?assumptions:assumptions -> t -> unit
(** @raise Unsat if the problem is unsat *)

val n_vars : t -> int
val n_clauses : t -> int

val is_in_unsat_core : t -> Lit.t -> bool
(** [is_in_unsat_core s lit] checks whether [abs(lit)] is part of the
    unsat core (if it was an assumption)
    precondition: last call to {!solve} raised {!Unsat} *)

val unsat_core : t -> Lit.t array
(** Access the whole unsat core
    precondition: last call to {!solve} raised {!Unsat} *)

val n_proved_lvl_0 : t -> int
(** Number of literals true at level0 (ie proved unconditionally).
    Can only grow. *)

val get_proved_lvl_0 : t -> int -> Lit.t
(** Get the n-th proved literal *)

val proved_lvl_0 : t -> Lit.t array
(** All literals currently proved at level 0 *)

type value =
  | V_undef
  | V_true
  | V_false

val pp_value : value printer
val string_of_value : value -> string

val value : t -> Lit.t -> value

val value_lvl_0 : t -> Lit.t -> value
(** [value_lvl_0 solver lit] returns the value of [lit] if it has this
    value at level 0 (proved), or [V_undef] otherwise *)
