
(* This file is free software. See file "license" for more details. *)

(** {1 Bindings to Batsat} *)

type t
(** An instance of batsat (stateful) *)

type 'a printer = Format.formatter -> 'a -> unit

module Lit : sig
  type t = private int
  (** Some representation of literals that will be accepted by the SAT solver. *)

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
  external create : unit -> t = "caml_batsat_new"
  external delete : t -> unit = "caml_batsat_delete"

  (* the [add_clause] functions return [false] if the clause
     immediately makes the problem unsat *)

  external simplify : t -> bool = "caml_batsat_simplify"

  external add_lit : t -> Lit.t -> bool = "caml_batsat_addlit"
  external assume : t -> Lit.t -> unit = "caml_batsat_assume"
  external solve : t -> bool = "caml_batsat_solve"

  external nvars : t -> int = "caml_batsat_nvars"
  external nclauses : t -> int = "caml_batsat_nclauses"
  external nconflicts : t -> int = "caml_batsat_nconflicts"

  external value : t -> Lit.t -> lbool = "caml_batsat_value"
  external check_assumption: t -> Lit.t -> bool = "caml_batsat_check_assumption"

  external set_verbose: t -> int -> unit = "caml_batsat_set_verbose"
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

type value =
  | V_undef
  | V_true
  | V_false

val value : t -> Lit.t -> value

val set_verbose: t -> int -> unit
