
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

  external set_verbose: t -> int -> unit = "ml_batsat_set_verbose"
end

let create () =
  let s = Raw.create() in
  Gc.finalise Raw.delete s;
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

let solve ?(assumptions=[||]) s =
  simplify s;
  Array.iter (fun x -> Raw.assume s x) assumptions;
  Raw.solve s |> check_ret_

type value =
  | V_undef
  | V_true
  | V_false

let pp_value out = function
  | V_undef -> Format.pp_print_string out "undef"
  | V_true -> Format.pp_print_string out "true"
  | V_false -> Format.pp_print_string out "false"

let value s lit = match Raw.value s lit with
  | 0 -> V_true
  | 1 -> V_false
  | 2 | 3 -> V_undef (* yep… *)
  | n -> failwith (Printf.sprintf "unknown lbool: %d" n)

let set_verbose = Raw.set_verbose
