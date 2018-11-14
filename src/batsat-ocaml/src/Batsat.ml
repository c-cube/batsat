
(* This file is free software. See file "license" for more details. *)

type t

type 'a printer = Format.formatter -> 'a -> unit

(* use normal convention of positive/negative ints *)
module Lit = struct
  type t = int
  let make n = assert (n>0); n
  let neg n = -n
  let abs = abs
  let sign n = n > 0
  let to_int n = n
  let to_string x = (if sign x then "" else "-") ^ string_of_int (abs @@ to_int x)
  let pp out x = Format.pp_print_string out (to_string x)
  let equal : t -> t -> bool = Pervasives.(=)
  let compare : t -> t -> int = Pervasives.compare
  let hash : t -> int = Hashtbl.hash
end

type assumptions = Lit.t array

module Raw = struct
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

let create () =
  let s = Raw.create() in
  s

exception Unsat

let check_ret_ b =
  if not b then raise Unsat

let add_clause_a s lits =
  Array.iter (fun x -> let r = Raw.add_lit s x in assert r) lits;
  Raw.add_lit s 0 |> check_ret_

let add_clause_l s lits =
  List.iter (fun x -> let r = Raw.add_lit s x in assert r) lits;
  Raw.add_lit s 0 |> check_ret_

let pp_clause out l =
  Format.fprintf out "[@[<hv>";
  let first = ref true in
  List.iter
    (fun x ->
       if !first then first := false else Format.fprintf out ",@ ";
       Lit.pp out x)
    l;
  Format.fprintf out "@]]"

let simplify s = Raw.simplify s |> check_ret_
let n_vars = Raw.nvars
let n_clauses = Raw.nclauses
let n_proved_lvl_0 = Raw.n_proved
let get_proved_lvl_0 = Raw.get_proved

let proved_lvl_0 s =
  Array.init (n_proved_lvl_0 s) (get_proved_lvl_0 s)

let solve ?(assumptions=[||]) s =
  Array.iter (fun x -> Raw.assume s x) assumptions;
  Raw.solve s |> check_ret_

let is_in_unsat_core s lit = Raw.check_assumption s lit

let unsat_core = Raw.unsat_core

type value =
  | V_undef
  | V_true
  | V_false
let string_of_value = function
  | V_undef -> "undef"
  | V_true -> "true"
  | V_false -> "false"

let pp_value out v = Format.pp_print_string out (string_of_value v)

let mk_val = function
  | 0 -> V_true
  | 1 -> V_false
  | 2 | 3 -> V_undef (* yep… *)
  | n -> failwith (Printf.sprintf "unknown lbool: %d" n)

let value s lit = mk_val @@ Raw.value s lit
let value_lvl_0 s lit = mk_val @@ Raw.value_lvl_0 s lit
