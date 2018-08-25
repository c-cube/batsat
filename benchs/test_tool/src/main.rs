
/// Script to run tests by comparing *Minisat* and *Ratsat* on
/// a bunch of files.

extern crate subprocess;
extern crate walkdir;
extern crate threadpool;

use std::env;
use std::path::{PathBuf,Path};
use std::collections::{HashMap,HashSet};
use std::time::Instant;
use std::thread;
use std::sync::mpsc;
use walkdir::WalkDir;
use subprocess::{Exec,ExitStatus as ES};
use threadpool::ThreadPool;

type Result<T> = std::result::Result<T, Box<std::error::Error>>;

#[derive(Debug,Clone,PartialEq,Eq,Hash)]
struct SolverName(String);

impl SolverName {
    fn new(s: &str) -> SolverName { SolverName(s.to_owned()) }
}

#[derive(Debug,Clone)]
struct Solver {
    name: SolverName,
    cmd: String,
    args: Vec<String>,
}

// build set of solvers
fn mk_solvers(timeout: i64) -> Vec<Solver> {
    vec![
        Solver {
            name: SolverName::new("minisat"),
            cmd:"minisat".to_owned(),
            args: vec![format!("-cpu-lim={}", timeout)]
        },
        Solver {
            name: SolverName::new("ratsat"),
            cmd:"./../ratsat-bin".to_owned(),
            args: vec!["--cpu-lim".to_owned(), format!("{}", timeout)]
        },
    ]
}

#[derive(Debug,Clone)]
/// A call along with what solver and what file it was
struct SolverResult {
    name: SolverName,
    path: PathBuf,
    time: f64,
    res: SolverAnswer,
}

#[derive(Debug,Copy,Clone,PartialEq)]
enum SolverAnswer {
    Unknown,
    Sat,
    Unsat,
}

use SolverAnswer::*;


#[derive(Debug,Copy,Clone)]
/// Statistics for one prover
struct Stats {
    unknown: i32,
    sat: i32,
    unsat: i32,
    ctime: f64,
}

impl Stats {
    fn new() -> Stats {  Stats {unknown: 0, sat:0, unsat: 0, ctime: 0.} }

    // update with the given results
    fn update(&mut self, r: SolverAnswer) {
        match r {
            Unknown => self.unknown += 1,
            Sat => self.sat += 1,
            Unsat => self.unsat += 1
        }
    }
}

#[derive(Debug,Clone)]
/// Results of all solvers on a given file
struct FileResult(HashMap<SolverName, SolverResult>);

struct DirResult {
    results: HashMap<PathBuf,FileResult>,
    stats: HashMap<SolverName, Stats>,
    failures: HashSet<PathBuf>,
    expected: HashMap<PathBuf, SolverAnswer>, // if a solver found a result
}

impl DirResult {
    fn update(&mut self, c: SolverResult) {
        // look for mismatches
        let mut is_present = false;
        let is_fail =
            if let Some(res_exp) = self.expected.get(&c.path) {
                is_present = true;
                c.res != Unknown && res_exp != &c.res
            } else {
                false
            };

        if is_fail {
            self.failures.insert(c.path.clone());
        } else if c.res != Unknown && !is_present {
            self.expected.insert(c.path.clone(), c.res); // we know what to expect!
        }

        // update stats for this solver
        {
            let s = &mut self.stats.get_mut(& c.name).unwrap();
            s.update(c.res);
            s.ctime += c.time;
        }

        println!("  {:-15}: {:?}", c.name.0, c);
        // update entry for this file
        let tbl = self.results
            .entry(c.path.to_owned())
            .or_insert_with(|| FileResult(HashMap::new()));
        tbl.0.insert(c.name.clone(), c);
    }
}

/// Call a solver on a file
fn solve_file(solver: Solver, path: &Path) -> Result<SolverResult> {
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

    Ok(SolverResult {name: solver.name.clone(), path: path.to_owned(), time, res})
}

/// message sent on channels
enum SyncMsg {
    StartedJob,
    SentAllJobs,
    JobResult(SolverResult),
}

/// Main thread that collects results and aggregates them into `res`
fn collect_thread(mut res: DirResult, rx: mpsc::Receiver<SyncMsg>) -> DirResult {
    use SyncMsg::*;

    let mut sent_all_jobs = false;
    let mut n_jobs = 0;
    // process messages
    loop {
        match rx.recv().unwrap() {
            StartedJob => n_jobs += 1,
            SentAllJobs => sent_all_jobs = true,
            JobResult(c) => {
                res.update(c);
                n_jobs -= 1;
                if sent_all_jobs && n_jobs == 0 {
                    break; // done
                }
            }
        }
    }
    res
}

fn process_dir(f: &Path, timeout: i64, jobs: usize) -> Result<DirResult> {
    println!("process {} with {} jobs", f.display(), jobs);

    let solvers = mk_solvers(timeout);
    let pool = ThreadPool::new(jobs);
    let (tx, rx) = mpsc::channel();

    // main thread
    let main_thread = {
        let mut stats: HashMap<SolverName,Stats> =
            solvers.iter()
            .map(|s| (s.name.clone(), Stats::new()))
            .collect();
        let state = DirResult {
            stats, results: HashMap::new(),
            failures: HashSet::new(), expected: HashMap::new(),
        };
        thread::spawn(move || collect_thread(state, rx))
    };

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
        for solver in solvers.iter() {
            // solve in a worker thread
            let tx = tx.clone();
            let solver = solver.clone();
            let path = path.to_owned();
            tx.send(SyncMsg::StartedJob).unwrap(); // must wait for one more job

            pool.execute(move || {
                let c = solve_file(solver, &path).unwrap();
                tx.send(SyncMsg::JobResult(c)).unwrap() // result of the job
            });
        }
    };
    tx.send(SyncMsg::SentAllJobs).unwrap(); // only now can the main thread consider stopping

    // wait for the main thread to be done
    let state = main_thread.join().unwrap();

    Ok(state)
}

fn main() -> Result<()> {
    let dir = env::var("DIR").ok().unwrap_or("msat".to_owned());
    let timeout: i64 = env::var("TIMEOUT").ok().unwrap_or("10".to_owned()).parse()?;
    let jobs: usize = env::var("JOBS").ok().unwrap_or("3".to_owned()).parse()?;

    let dres = process_dir(Path::new(&dir), timeout, jobs)?;

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
