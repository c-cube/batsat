extern crate clap;
extern crate flate2;
extern crate ratsat;

use std::fs::File;
use std::io::{self, BufRead, BufReader};
use std::process::exit;
use clap::{App, Arg};
use flate2::bufread::GzDecoder;
use ratsat::{SimpSolver, Solver};

fn main() {
    main2().unwrap_or_else(|err| {
        eprintln!("{}", err);
        exit(1);
    })
}

fn main2() -> io::Result<()> {
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
        .get_matches();

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

    let mut solver = SimpSolver::default();
    solver.set_verbosity(verbosity);

    if let Some(input_file) = input_file {
        let file = BufReader::new(File::open(input_file)?);
        read_input_autogz(file, &mut solver, is_strict)?;
    } else {
        println!("Reading from standard input... Use '--help' for help.");
        let stdin = io::stdin();
        read_input_autogz(stdin.lock(), &mut solver, is_strict)?;
    }
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
    Ok(())
}

fn read_input_autogz<R: BufRead, S: Solver>(
    mut input: R,
    solver: &mut S,
    is_strict: bool,
) -> io::Result<()> {
    let is_gz = input.fill_buf()?.starts_with(b"\x1F\x8B");
    if is_gz {
        read_input(BufReader::new(GzDecoder::new(input)), solver, is_strict)
    } else {
        read_input(input, solver, is_strict)
    }
}

fn read_input<R: BufRead, S: Solver>(
    mut input: R,
    solver: &mut S,
    is_strict: bool,
) -> io::Result<()> {
    if solver.verbosity() > 0 {
        println!("============================[ Problem Statistics ]=============================");
        println!(
            "|                                                                             |\n"
        );
    }
    ratsat::dimacs::parse(&mut input, solver, is_strict)?;
    Ok(())
}
