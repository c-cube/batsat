
(prover
  (name batsat)
  (version "git:.")
  (cmd "$cur_dir/../batsat-bin --cpu-lim $timeout $file")
  (unknown "INDETERMINATE")
  (unsat "s UNSATISFIABLE")
  (sat "s SATISFIABLE"))

(prover
  (name minisat)
  (cmd "minisat -cpu-lim=$timeout $file")
  (unknown "INDETERMINATE")
  (unsat "^UNSATISFIABLE")
  (sat "^SATISFIABLE"))

(dir
  (path $cur_dir/basic)
  (pattern ".*\\.cnf\\.gz")
  (expect (const unknown)))

(dir
  (path $cur_dir/sidekick)
  (pattern ".*\\.cnf\\.gz")
  (expect (const unknown)))
