extern crate clap;

use clap::{Arg, App};

fn main() {
    let matches = App::new("RatSat")
        .version("0.0.1")
        .author("Masaki Hara <ackie.h.gmai@gmail.com>")
        .about("Rust port of MiniSAT")
        .arg(Arg::with_name("input-file"))
        .arg(Arg::with_name("result-output-file"))
        .get_matches();

    let input_file = matches.value_of("input-file");
    let result_output_file = matches.value_of("result-output-file");
    eprintln!("input_file = {:?}", input_file);
    eprintln!("result_output_file = {:?}", result_output_file);
}
