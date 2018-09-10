
module Vec = CCVector

module Parse : sig
  type 'a event =
    | Add_clause of 'a array
    | Solve of 'a array

  type 'a t

  val make : file:string -> (int -> 'a) -> 'a t

  val next : 'a t -> 'a event (** @raise End_of_file when done *)
end = struct
  module L = Lexer

  type 'a event =
    | Add_clause of 'a array
    | Solve of 'a array

  type 'a t = {
    mk: int -> 'a;
    vec: 'a Vec.vector;
    lex: Lexing.lexbuf;
  }

  let make ~file mk : _ t =
    let ic = open_in file in
    let lex = Lexing.from_channel ic in
    at_exit (fun () -> close_in_noerr ic);
    {lex; vec=Vec.create(); mk; }

  let rec next (self:_ t) : _ event =
    match L.token self.lex with
    | L.EOF -> raise End_of_file
    | L.A ->
      let c = read_ints self in
      Solve c
    | L.I 0 ->
      Add_clause [| |]
    | L.I x ->
      let c = read_ints ~first:(self.mk x) self in
      Add_clause c
  and read_ints ?first self : _ array =
    Vec.clear self.vec; (* reuse local vec *)
    CCOpt.iter (Vec.push self.vec) first;
    let rec aux() =
      match L.token self.lex with
      | L.I 0 -> Vec.to_array self.vec (* done *)
      | L.I n ->
        let x = self.mk n in
        Vec.push self.vec x;
        aux()
      | L.A -> failwith "unexpected \"a\""
      | L.EOF -> failwith "unexpected end of file"
    in
    aux()
end

module Solver = struct
  type 'lit internal = {
    mklit: int -> 'lit;
    to_int: 'lit -> int;
    add_clause: 'lit array -> bool;
    solve: 'lit array -> bool;
  }
  type t = Solver : 'lit internal -> t

  type builder = {
    name: string;
    make: unit -> t;
  }

  let mk_minisat : builder = {
    name="minisat";
    make=(fun () ->
        let module S = Minisat in
        let s = S.create() in
        let mklit i = let v = S.Lit.make (abs i) in if i>0 then v else S.Lit.neg v in
        let add_clause c = try S.add_clause_a s c; true with S.Unsat -> false in
        let solve ass = try S.solve ~assumptions:ass s; true with S.Unsat -> false in
        let to_int i = S.Lit.to_int (S.Lit.abs i) * (if S.Lit.sign i then 1 else -1) in
        Solver { add_clause; solve; mklit; to_int; }
      );
  }

  let mk_batsat : builder = {
    name="batsat";
    make=(fun () ->
        let module S = Batsat in
        let s = S.create() in
        let mklit i = let v = S.Lit.make (abs i) in if i>0 then v else S.Lit.neg v in
        let add_clause c = try S.add_clause_a s c; true with S.Unsat -> false in
        let solve ass = try S.solve ~assumptions:ass s; true with S.Unsat -> false in
        let to_int i = S.Lit.to_int (S.Lit.abs i) * (if S.Lit.sign i then 1 else -1) in
        Solver { add_clause; solve; mklit; to_int; }
      );
  }

  let name b = b.name
  let all = [mk_minisat; mk_batsat]
end

let solve_with_solver ~debug solver file : unit =
  Printf.printf "c process %S with %s\n" file solver.Solver.name;
  let Solver.Solver s = solver.Solver.make() in
  let pp_arr out a =
    Array.iter (fun lit -> Printf.fprintf out "%d " (s.Solver.to_int lit)) a;
  in
  let p = Parse.make ~file s.mklit in
  let rec process_problem () =
    match Parse.next p with
    | Parse.Add_clause c ->
      if debug then (
        Printf.printf "add_clause %a\n%!" pp_arr c;
      );
      let r = s.Solver.add_clause c in
      if r then process_problem()
      else (
        Printf.printf "UNSAT\n%!";
        skip_problem ()
      )
    | Parse.Solve assumptions ->
      if debug then (
        Printf.printf "c solve %a\n%!" pp_arr assumptions;
      );
      let r = s.Solver.solve assumptions in
      Printf.printf "%s\n%!" (if r then "SAT" else "UNSAT");
      (* next problem! *)
      process_problem()
    | exception End_of_file ->
      done_ ()
  and skip_problem() =
    match Parse.next p with
    | Parse.Add_clause _ -> skip_problem()
    | Parse.Solve _ -> process_problem ()
    | exception End_of_file -> done_ ()
  and done_ () =
    Printf.printf "c done for %S with %s\n%!" file solver.name;
    ()
  in
  process_problem ()

let solve_with_file ~debug solvers file : unit =
  List.iter
    (fun s ->
       try solve_with_solver ~debug s file
       with e ->
         Printf.printf "error while solving %S with %s:\n%s"
           file s.Solver.name (Printexc.to_string e);
           exit 1)
    solvers

let () =
  let solvers = ref [] in
  let files = ref [] in
  let debug = ref false in
  let opt_s =
    Arg.Symbol
      (List.map Solver.name Solver.all,
       fun s -> solvers := Solver.(List.find (fun b->b.name=s) all) :: !solvers)
      in
  let opts = [
    "-d", Arg.Set debug, " debug";
    "--solver", opt_s, " use given solver";
    "-s", opt_s, " alias to --solver";
  ] |> Arg.align in
  Arg.parse opts (fun f -> files := f :: !files) "icnf_solve [options] <file>";
  if !solvers=[] then solvers := [Solver.mk_batsat]; (* default *)
  List.iter (fun f -> solve_with_file ~debug:!debug !solvers f) !files;
  ()
