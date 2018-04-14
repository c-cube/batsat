/*****************************************************************************************[main.rs]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson (MiniSat)
Copyright (c) 2007-2010, Niklas Sorensson (MiniSat)
Copyright (c) 2018-2018, Masaki Hara

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#[macro_use]
extern crate clap;
extern crate flate2;
extern crate ratsat;

use std::fs::File;
use std::io::{self, BufRead, BufReader, BufWriter, Write};
use std::mem;
use std::process::exit;
use std::time::Instant;
use clap::{App, Arg};
use flate2::bufread::GzDecoder;
use ratsat::{lbool, Solver, SolverOpts};

fn main() {
    let exitcode = main2().unwrap_or_else(|err| {
        eprintln!("{}", err);
        exit(1);
    });
    exit(exitcode);
}

fn main2() -> io::Result<i32> {
    let matches = App::new("RatSat")
        .version("0.0.2")
        .author("Masaki Hara <ackie.h.gmai@gmail.com>")
        .about("MiniSat reimplemented in Rust")
        .arg(Arg::with_name("input-file"))
        .arg(Arg::with_name("result-output-file"))
        .arg(
            Arg::with_name("verbosity")
                .long("verb")
                .default_value("1")
                .takes_value(true),
        )
        .arg(Arg::with_name("is-strict").long("strict"))
        .arg(Arg::with_name("var-decay").long("var-decay")
             .help("The variable activity decay factor")
             .default_value("0.95")
             .takes_value(true))
        .arg(Arg::with_name("clause-decay").long("cla-decay")
             .help("The clause activity decay factor")
             .default_value("0.999")
             .takes_value(true))
        .arg(Arg::with_name("random-var-freq").long("rnd-freq")
             .help("The frequency with which the decision heuristic tries to choose a random variable")
             .default_value("0.0")
             .takes_value(true))
        .arg(Arg::with_name("random-seed").long("rnd-seed")
             .help("The frequency with which the decision heuristic tries to choose a random variable")
             .default_value("91648253.0")
             .takes_value(true))
        .arg(Arg::with_name("ccmin-mode").long("ccmin-mode")
             .help("Controls conflict clause minimization (0=none, 1=basic, 2=deep)")
             .default_value("2")
             .takes_value(true))
        .arg(Arg::with_name("phase-saving").long("phase-saving")
             .help("Controls the level of phase saving (0=none, 1=limited, 2=full)")
             .default_value("2")
             .takes_value(true))
        .arg(Arg::with_name("rnd-init").long("rnd-init")
             .conflicts_with("no-rnd-init")
             .help("Randomize the initial activity"))
        .arg(Arg::with_name("no-rnd-init").long("no-rnd-init")
             .help("Do not randomize the initial activity [default]"))
        .arg(Arg::with_name("luby-restart").long("luby")
             .conflicts_with("no-luby-restart")
             .help("Use the Luby restart sequence [default]"))
        .arg(Arg::with_name("no-luby-restart").long("no-luby")
             .help("Do not use the Luby restart sequence"))
        .arg(Arg::with_name("restart-first").long("rfirst")
             .help("The base restart interval")
             .default_value("100")
             .takes_value(true))
        .arg(Arg::with_name("restart-inc").long("rinc")
             .help("Restart interval increase factor")
             .default_value("2.0")
             .takes_value(true))
        .arg(Arg::with_name("garbage-frac").long("gc-frac")
             .help("The fraction of wasted memory allowed before a garbage collection is triggered")
             .default_value("0.20")
             .takes_value(true))
        .arg(Arg::with_name("min-learnts-lim").long("min-learnts")
             .help("Minimum learnt clause limit")
             .default_value("0")
             .takes_value(true))
        .arg(Arg::with_name("use-asymm").long("asymm")
             .conflicts_with("no-use-asymm")
             .help("Shrink clauses by asymmetric branching."))
        .arg(Arg::with_name("no-use-asymm").long("no-asymm")
             .help("Do not shrink clauses by asymmetric branching. [default]"))
        .arg(Arg::with_name("use-rcheck").long("rcheck")
             .conflicts_with("no-use-rcheck")
             .help("Check if a clause is already implied. (costly)"))
        .arg(Arg::with_name("no-use-rcheck").long("no-rcheck")
             .help("Do not check if a clause is already implied. [default]"))
        .arg(Arg::with_name("use-elim").long("elim")
             .conflicts_with("no-use-elim")
             .help("Perform variable elimination. [default]"))
        .arg(Arg::with_name("no-use-elim").long("no-elim")
             .help("Do not perform variable elimination."))
        .arg(Arg::with_name("grow").long("grow")
             .help("Allow a variable elimination step to grow by a number of clauses.")
             .default_value("0")
             .takes_value(true))
        .arg(Arg::with_name("clause-lim").long("cl-lim")
             .help("Variables are not eliminated if it produces a resolvent with a length above this limit. -1 means no limit")
             .default_value("20")
             .takes_value(true))
        .arg(Arg::with_name("subsumption-lim").long("sub-lim")
             .help("Do not check if subsumption against a clause larger than this. -1 means no limit.")
             .default_value("1000")
             .takes_value(true))
        .arg(Arg::with_name("simp-garbage-frac").long("simp-gc-frac")
             .help("The fraction of wasted memory allowed before a garbage collection is triggered during simplification.")
             .default_value("0.5")
             .takes_value(true))
        .get_matches();

    let mut solver_opts = SolverOpts::default();
    solver_opts.var_decay = value_t_or_exit!(matches, "var-decay", f64);
    solver_opts.clause_decay = value_t_or_exit!(matches, "clause-decay", f64);
    solver_opts.random_var_freq = value_t_or_exit!(matches, "random-var-freq", f64);
    solver_opts.random_seed = value_t_or_exit!(matches, "random-seed", f64);
    solver_opts.ccmin_mode = value_t_or_exit!(matches, "ccmin-mode", i32);
    solver_opts.phase_saving = value_t_or_exit!(matches, "phase-saving", i32);
    solver_opts.rnd_init_act = matches.is_present("rnd-init-act");
    solver_opts.luby_restart = !matches.is_present("no-luby-restart");
    solver_opts.restart_first = value_t_or_exit!(matches, "restart-first", i32);
    solver_opts.restart_inc = value_t_or_exit!(matches, "restart-inc", f64);
    solver_opts.garbage_frac = value_t_or_exit!(matches, "garbage-frac", f64);
    solver_opts.min_learnts_lim = value_t_or_exit!(matches, "min-learnts-lim", i32);

    solver_opts.use_asymm = matches.is_present("use-asymm");
    solver_opts.use_rcheck = matches.is_present("use-rcheck");
    solver_opts.use_elim = !matches.is_present("no-use-elim");
    solver_opts.grow = value_t_or_exit!(matches, "grow", i32);
    solver_opts.clause_lim = value_t_or_exit!(matches, "clause-lim", i32);
    solver_opts.subsumption_lim = value_t_or_exit!(matches, "subsumption-lim", i32);
    solver_opts.simp_garbage_frac = value_t_or_exit!(matches, "simp-garbage-frac", f64);

    if !solver_opts.check() {
        eprintln!("Invalid option value");
        exit(1);
    }

    let input_file = matches.value_of("input-file");
    let result_output_file = matches.value_of("result-output-file");
    let verbosity = matches
        .value_of("verbosity")
        .unwrap()
        .parse::<i32>()
        .unwrap_or(0);
    if verbosity < 0 || verbosity > 2 {
        eprintln!(
            "ERROR! value <{}> is too small for option \"verb\".",
            verbosity
        );
        exit(1);
    }
    let is_strict = matches.value_of("is-strict").is_some();

    let mut solver = Solver::new(&solver_opts);
    solver.set_verbosity(verbosity);

    let initial_time = Instant::now();

    if let Some(input_file) = input_file {
        let file = BufReader::new(File::open(input_file)?);
        read_input_autogz(file, &mut solver, is_strict)?;
    } else {
        println!("Reading from standard input... Use '--help' for help.");
        let stdin = io::stdin();
        read_input_autogz(stdin.lock(), &mut solver, is_strict)?;
    }

    let mut resfile = if let Some(result_output_file) = result_output_file {
        Some(BufWriter::new(File::create(result_output_file)?))
    } else {
        None
    };

    if solver.verbosity() > 0 {
        println!(
            "|  Number of variables:  {:12}                                         |",
            solver.num_vars()
        );
        println!(
            "|  Number of clauses:    {:12}                                         |",
            solver.num_clauses()
        );
    }

    let parsed_time = Instant::now();
    if solver.verbosity() > 0 {
        let duration = parsed_time - initial_time;
        println!(
            "|  Parse time:           {:9}.{:02} s                                       |",
            duration.as_secs(),
            duration.subsec_nanos() / 10_000_000
        );
        println!("|                                                                             |");
    }

    if !solver.simplify() {
        if let Some(resfile) = resfile.as_mut() {
            writeln!(resfile, "UNSAT")?;
            resfile.flush()?;
        }
        mem::drop(resfile);
        if solver.verbosity() > 0 {
            println!(
                "==============================================================================="
            );
            println!("Solved by unit propagation");
            solver.print_stats();
            println!("");
        }
        println!("UNSATISFIABLE");
        exit(20);
    }

    let ret = solver.solve_limited(&[]);
    if solver.verbosity() > 0 {
        solver.print_stats();
        println!("");
    }
    if ret == lbool::TRUE {
        println!("SATISFIABLE");
    } else if ret == lbool::FALSE {
        println!("UNSATISFIABLE");
    } else {
        println!("INDETERMINATE");
    }
    if let Some(resfile) = resfile.as_mut() {
        if ret == lbool::TRUE {
            writeln!(resfile, "SAT")?;
            for i in 0..solver.num_vars() {
                if solver.model[i as usize] != lbool::UNDEF {
                    if i != 0 {
                        write!(resfile, " ")?;
                    }
                    if solver.model[i as usize] == lbool::FALSE {
                        write!(resfile, "-")?;
                    }
                    write!(resfile, "{}", i + 1)?;
                }
            }
            writeln!(resfile, " 0")?;
        } else if ret == lbool::FALSE {
            writeln!(resfile, "UNSAT")?;
        } else {
            writeln!(resfile, "INDET")?;
        }
        resfile.flush()?;
    }
    mem::drop(resfile);

    let exitcode = if ret == lbool::TRUE {
        10
    } else if ret == lbool::FALSE {
        20
    } else {
        0
    };

    if !cfg!(debug_assertions) {
        // (faster than "return", which will invoke the destructor for 'Solver')
        exit(exitcode);
    }

    Ok(exitcode)
}

fn read_input_autogz<R: BufRead>(
    mut input: R,
    solver: &mut Solver,
    is_strict: bool,
) -> io::Result<()> {
    let is_gz = input.fill_buf()?.starts_with(b"\x1F\x8B");
    if is_gz {
        read_input(BufReader::new(GzDecoder::new(input)), solver, is_strict)
    } else {
        read_input(input, solver, is_strict)
    }
}

fn read_input<R: BufRead>(mut input: R, solver: &mut Solver, is_strict: bool) -> io::Result<()> {
    if solver.verbosity() > 0 {
        println!("============================[ Problem Statistics ]=============================");
        println!("|                                                                             |");
    }
    ratsat::dimacs::parse(&mut input, solver, is_strict)?;
    Ok(())
}
