
print_endline "test1...";;

module S = Batsat;;

let s = S.create();;
Printf.printf "nvars: %d\n%!" (S.n_vars s);;
let l1 = S.Lit.make 1;;
let l2 = S.Lit.make 2;;
let l3 = S.Lit.make 3;;
l1;;
S.Lit.neg l1;;
S.Lit.neg l2;;
l1, S.Lit.neg l1, l2, S.Lit.neg l2;;
S.add_clause_l s [l1; S.Lit.neg l2];;
S.add_clause_l s [S.Lit.neg l1; l2];;
S.add_clause_l s [S.Lit.neg l1; S.Lit.neg l3];;
S.add_clause_l s [l1; S.Lit.neg l3];;
print_endline "should succeed with sat...";;
try S.solve s; print_endline "ok!"
with S.Unsat -> print_endline "failure, got unsat";; (* should not fail *)
S.value s l1;;
S.value s l2;;
print_endline "should succeed with sat...";;
try S.solve s; print_endline "ok!"
with S.Unsat -> assert false;; (* should not fail *)
print_endline "should succeed with unsat...";;
try S.solve ~assumptions:[|l3|] s; assert false
with S.Unsat -> print_endline "ok!";; (* should fail *)
print_endline "should succeed with sat...";;
try S.solve s; print_endline "ok!"
with S.Unsat -> assert false;; (* should not fail *)
Format.printf "val(l3) = %a@." S.pp_value (S.value s l3);;
l3, S.value s l3, S.value s (S.Lit.neg l3);;
assert (S.value s l3 = S.V_false);;
assert (S.value s (S.Lit.neg l3) = S.V_true);;
print_endline "ok!";;
print_endline "should return undef...";;
let l2000 = S.Lit.make 2000 ;;
assert (S.value s l2000 = S.V_undef);;
assert (S.value s (S.Lit.neg l2000) = S.V_undef);;
print_endline "ok!";;
