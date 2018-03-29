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
        .version("0.0.1")
        .author("Masaki Hara <ackie.h.gmai@gmail.com>")
        .about("Rust port of MiniSAT")
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
        .get_matches();

    let mut solver_opts = SolverOpts::default();
    solver_opts.var_decay = matches
        .value_of("var-decay")
        .and_then(|s| s.parse().ok())
        .unwrap_or(solver_opts.var_decay);
    solver_opts.clause_decay = matches
        .value_of("clause-decay")
        .and_then(|s| s.parse().ok())
        .unwrap_or(solver_opts.clause_decay);
    solver_opts.random_var_freq = matches
        .value_of("random-var-freq")
        .and_then(|s| s.parse().ok())
        .unwrap_or(solver_opts.random_var_freq);
    solver_opts.random_seed = matches
        .value_of("random-seed")
        .and_then(|s| s.parse().ok())
        .unwrap_or(solver_opts.random_seed);
    solver_opts.ccmin_mode = matches
        .value_of("ccmin-mode")
        .and_then(|s| s.parse().ok())
        .unwrap_or(solver_opts.ccmin_mode);
    solver_opts.phase_saving = matches
        .value_of("phase-saving")
        .and_then(|s| s.parse().ok())
        .unwrap_or(solver_opts.phase_saving);
    solver_opts.rnd_init_act = matches.is_present("rnd-init-act");
    solver_opts.luby_restart = !matches.is_present("no-luby-restart");
    solver_opts.restart_first = matches
        .value_of("restart-first")
        .and_then(|s| s.parse().ok())
        .unwrap_or(solver_opts.restart_first);
    solver_opts.restart_inc = matches
        .value_of("restart-inc")
        .and_then(|s| s.parse().ok())
        .unwrap_or(solver_opts.restart_inc);
    solver_opts.garbage_frac = matches
        .value_of("garbage-frac")
        .and_then(|s| s.parse().ok())
        .unwrap_or(solver_opts.garbage_frac);
    solver_opts.min_learnts_lim = matches
        .value_of("min-learnts-lim")
        .and_then(|s| s.parse().ok())
        .unwrap_or(solver_opts.min_learnts_lim);

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
    eprintln!("input_file = {:?}", input_file);
    eprintln!("result_output_file = {:?}", result_output_file);
    eprintln!("is_strict = {:?}", is_strict);

    let mut solver = Solver::new(solver_opts);
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
