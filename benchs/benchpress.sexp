
(prover
  (name batsat)
  (synopsis "batsat solver in rust: https://github.com/c-cube/batsat")
  (binary "$cur_dir/batsat-bin")
  (version "git:.")
  (cmd "batsat-bin --cpu-lim $timeout $file")
  (unknown "INDETERMINATE")
  (unsat "s UNSATISFIABLE")
  (sat "s SATISFIABLE"))

(dir
  (path $cur_dir/basic)
  (pattern ".*\\.cnf\\.gz")
  (expect (const unknown)))
