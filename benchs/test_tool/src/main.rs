
/// Script to run tests by comparing *Minisat* and *Ratsat* on
/// a bunch of files.

extern crate subprocess;
extern crate walkdir;

use std::env;
use std::path::Path;
use std::collections::HashMap;
use std::time::Instant;
use walkdir::WalkDir;
use subprocess::{Exec,ExitStatus as ES};

type Result<T> = std::result::Result<T, Box<std::error::Error>>;

#[derive(Debug)]
struct Solver {
    name: String,
    cmd: String,
    args: Vec<String>,
}

// build set of solvers
fn mk_solvers(timeout: i64) -> Vec<Solver> {
    vec![
        Solver {
            name: "minisat".to_owned(),
            cmd:"minisat".to_owned(),
            args: vec![format!("-cpu-lim={}", timeout)]
        },
        Solver {
            name: "ratsat".to_owned(),
            cmd:"./../ratsat-bin".to_owned(),
            args: vec!["--cpu-lim".to_owned(), format!("{}", timeout)]
        },
    ]
}

#[derive(Debug,Copy,Clone)]
struct Call {
    time: f64,
    res: CallResult,
}

#[derive(Debug,Copy,Clone,PartialEq)]
enum CallResult {
    Unknown,
    Sat,
    Unsat,
}

use CallResult::*;

#[derive(Debug,Copy,Clone)]
// Statistics for one prover
struct Stats {
    unknown: i32,
    sat: i32,
    unsat: i32,
    ctime: f64,
}

impl Stats {
    fn new() -> Stats {  Stats {unknown: 0, sat:0, unsat: 0, ctime: 0.} }

    // update with the given results
    fn update(&mut self, r: &CallResult) {
        match r {
            Unknown => self.unknown += 1,
            Sat => self.sat += 1,
            Unsat => self.unsat += 1
        }
    }
}

#[derive(Debug,Clone)]
/// Results of all solvers on a given file
struct FileResult(HashMap<String, Call>);

#[derive(Debug)]
struct DirResult {
    results: Vec<FileResult>,
    stats: HashMap<String, Stats>,
    failures: Vec<FileResult>,
}

fn process_dir(f: &Path, timeout: i64) -> Result<DirResult> {
    println!("process {}", f.display());

    let solvers = mk_solvers(timeout);

    // allocate stats for each solver
    let mut stats: HashMap<String,Stats> =
        solvers.iter()
            .map(|s| (s.name.clone(), Stats::new()))
            .collect();
    let mut results = vec![];
    let mut failures = vec![];

    // traverse dir, keep only files
    let files = WalkDir::new(f)
        .follow_links(true)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.file_type().is_file())
        .map(|e| e.into_path())
        .filter(|p| p.extension().map(|e| e == "cnf").unwrap_or(false));

    for path in files {
        println!("test on {}", path.display());
        let mut tbl: HashMap<String,_> = HashMap::new();
        let mut expected = None;
        let mut must_fail = false; // true if solvers mismatch

        for solver in solvers.iter() {
            let start = Instant::now();

            // run the solver on the file
            let p = Exec::cmd(&solver.cmd)
                .args(solver.args.as_slice())
                .arg(path.as_os_str())
                .stdout(subprocess::NullFile)
                .stderr(subprocess::NullFile)
                .join()?;
            let time = (Instant::now() - start).as_secs() as f64;

            // parse error code
            let res = match p {
                ES::Exited(0) => Unknown,
                ES::Exited(10) => Sat,
                ES::Exited(20) => Unsat,
                x => panic!("unknown exit code for solver {:?}: {:?}", solver.cmd, x)
            };
            // look for mismatches
            if let Some(res_exp) = expected {
                if res != Unknown && res_exp != res {
                    must_fail = true;
                }

            } else if res != Unknown {
                expected = Some(res);
            };


            // update stats for this solver
            {
                let s = &mut stats.get_mut(& solver.name).unwrap();
                s.update(&res);
                s.ctime += time;
            }

            let c = Call {time, res};

            tbl.insert(solver.name.clone(), c);
            println!("  {:-15}: {:?}", solver.name, c);
        }

        let res = FileResult(tbl);
        if must_fail {
            failures.push(res.clone());
        }

        results.push(res);
    };

    Ok(DirResult {stats, results, failures})
}



fn main() -> Result<()> {
    let dir = env::var("DIR").ok().unwrap_or("msat".to_owned());
    let timeout: i64 = env::var("TIMEOUT").ok().unwrap_or("10".to_owned()).parse()?;

    let dres = process_dir(Path::new(&dir), timeout)?;

    println!("{:?}", dres.stats);
    if dres.failures.len() == 0 {
        println!("OK");
        Ok(())
    } else {
        println!("FAILURE ({})", dres.failures.len());
        for f in dres.failures.iter() {
            println!("  failure on: {:?}", f)
        }
        panic!() // oh no
    }
}
