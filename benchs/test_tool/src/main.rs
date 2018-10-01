
/// Script to run tests by comparing *Minisat* and *Ratsat* on
/// a bunch of files.

extern crate walkdir;
extern crate threadpool;
extern crate ansi_term;

use std::path::{Path,PathBuf};
use std::collections::{HashMap,HashSet};
use std::time::{Instant,Duration};
use std::thread;
use std::sync::{Arc,mpsc};
use threadpool::ThreadPool;
use std::process::{Command,Stdio};
use std::io::Write;
use ansi_term::Colour::{Green,Red};

type Result<T> = std::result::Result<T, Box<std::error::Error>>;

#[derive(Clone,PartialEq,Eq,Hash)]
struct SolverName(String);

impl std::fmt::Debug for SolverName {
    fn fmt(&self, out: &mut std::fmt::Formatter) -> std::fmt::Result {
        out.write_str(&self.0)
    }
}

impl SolverName {
    fn new(s: &str) -> SolverName { SolverName(s.to_owned()) }
}

#[derive(Debug,Clone)]
struct Solver {
    name: Arc<SolverName>,
    mk_proof: bool, // produces proofs?
    cmd: String,
    args: Vec<String>,
}

// build set of solvers
fn mk_solvers(task: &DirTask) -> Vec<Solver> {
    let mut v = vec![
        Solver {
            name: Arc::new(SolverName::new("minisat")),
            mk_proof: false,
            cmd:"minisat".to_owned(),
            args: vec![format!("-cpu-lim={}", task.timeout)]
        },
        {
            let mut args = vec!["--cpu-lim".to_owned(), format!("{}", task.timeout)];
            let mk_proof = task.checker.is_some();
            if mk_proof {
                args.push("--proof".to_owned()); // output DRAT!
            };
            Solver {
                name: Arc::new(SolverName::new("batsat")),
                mk_proof: false,
                cmd:"./../batsat-bin".to_owned(),
                args: vec!["--cpu-lim".to_owned(), format!("{}", task.timeout)],
            }
        },
    ];
    // add a checked version of batsat, if there's a checker
    if task.checker.is_some() {
        v.push({
            let args =
                vec!["--proof".to_owned(), "--cpu-lim".to_owned(), format!("{}", task.timeout)];
            Solver {
                name: Arc::new(SolverName::new("batsat-proof")),
                mk_proof: true,
                cmd:"./../batsat-bin".to_owned(),
                args,
            }
        });
    }
    v
}

#[derive(Debug,Clone)]
/// A call along with what solver and what file it was
struct SolverResult {
    name: Arc<SolverName>,
    path: Arc<PathBuf>,
    time: f64,
    res: SolverAnswer,
}

#[derive(Debug,Clone,PartialEq)]
enum SolverAnswer {
    CheckFailed,
    SolverFailed(String),
    Unknown,
    Sat,
    Unsat,
}

use SolverAnswer::*;

impl SolverAnswer {
    fn is_definite(&self) -> bool {
        *self == Sat || *self == Unsat
    }
}

#[derive(Debug,Copy,Clone)]
/// Statistics for one prover
struct Stats {
    unknown: i32,
    sat: i32,
    unsat: i32,
    check_failed: i32,
    solver_fail: i32,
    total_time: f64,
}

impl Stats {
    fn new() -> Stats {
        Stats {
            unknown: 0, sat: 0, unsat: 0, check_failed: 0,
            solver_fail: 0, total_time: 0.}
    }

    // update with the given results
    fn update(&mut self, r: &SolverAnswer) {
        match r {
            Unknown => self.unknown += 1,
            Sat => self.sat += 1,
            Unsat => self.unsat += 1,
            CheckFailed => self.check_failed += 1,
            SolverFailed(_) => self.solver_fail += 1,
        }
    }
}

#[derive(Debug,Clone)]
/// Results of all solvers on a given file
struct FileResult(HashMap<Arc<SolverName>, SolverResult>);

#[derive(Debug)]
/// A test task
struct DirTask {
    path: PathBuf,
    timeout: i64,
    jobs: usize,
    checker: Option<String>,
}

struct DirResult {
    results: HashMap<Arc<PathBuf>,FileResult>,
    stats: HashMap<Arc<SolverName>, Stats>,
    failures: HashSet<Arc<PathBuf>>,
    n_check_failed: usize,
    expected: HashMap<Arc<PathBuf>, SolverAnswer>, // if a solver found a result
}

impl DirResult {
    fn update(&mut self, c: SolverResult) {
        // look for mismatches
        let mut is_present = false;
        let is_fail =
            if let Some(res_exp) = self.expected.get(&c.path) {
                is_present = true;
                c.res.is_definite() && res_exp != &c.res
            } else {
                false
            };

        if is_fail {
            self.failures.insert(c.path.clone());
        } else if c.res.is_definite() && !is_present {
            self.expected.insert(c.path.clone(), c.res.clone()); // we know what to expect!
        }
        if let SolverAnswer::CheckFailed = c.res {
            self.n_check_failed += 1;
        }

        // update stats for this solver
        {
            let s = &mut self.stats.get_mut(& c.name).unwrap();
            s.update(&c.res);
            s.total_time += c.time;
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
fn solve_file(solver: Solver, path: Arc<PathBuf>, checker: &Option<String>) -> Result<SolverResult> {
    let start = Instant::now();

    // run the solver on the file
    let out = Command::new(&solver.cmd)
        .args(solver.args.as_slice())
        .arg(path.as_os_str())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()?
        .wait_with_output()?;
    let time = Instant::now() - start;
    let time = time.as_secs() as f64 + (time.subsec_millis() as f64 / 1_000.);

    // parse error code
    let mut res = match out.status.code() {
        Some(0) => Unknown,
        Some(10) => Sat,
        Some(20) => Unsat,
        x => {
            let s = String::from_utf8(out.stdout.clone())?;
            println!("unknown exit code for solver {:?}: {:?}\nstdout: {:?}", solver.cmd, x, s);
            SolverFailed(s)
        },
    };

    if let Some(check_cmd) = checker {
        if res == Unsat && solver.mk_proof {
            // run checker now!
            let mut checker_p = Command::new(&check_cmd)
                .arg(path.as_os_str()) // give problem as argument
                .stdin(Stdio::piped()) // give proof on stdin
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .spawn()?;
            {
                // write proof into its output
                let stdin = checker_p.stdin.as_mut().expect("cannot get stdin of checker");
                stdin.write_all(out.stdout.as_slice())?;
            }
            let checker_out = checker_p.wait()?;

            if ! checker_out.success() {
                println!("checking failed for {:?} on {}", solver.name, path.display());
                res = CheckFailed
            }
        }
    };

    Ok(SolverResult {name: solver.name.clone(), path: path.clone(), time, res})
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
        match rx.recv_timeout(Duration::from_secs(3_600)) {
            Err(_) => {
                println!("collect thread: timeout");
                std::process::exit(1) // fail
            },
            Ok(StartedJob) => n_jobs += 1,
            Ok(SentAllJobs) => sent_all_jobs = true,
            Ok(JobResult(c)) => {
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

fn process_task(task: &DirTask) -> Result<DirResult> {
    println!("process {} with {} jobs (proof: {})",
        task.path.display(), task.jobs, task.checker.is_some());

    let solvers = mk_solvers(&task);
    let pool = ThreadPool::new(task.jobs);
    let (tx, rx) = mpsc::channel();

    // main thread
    let main_thread = {
        let mut stats: HashMap<_,Stats> =
            solvers.iter()
            .map(|s| (s.name.clone(), Stats::new()))
            .collect();
        let state = DirResult {
            stats, results: HashMap::new(), n_check_failed: 0,
            failures: HashSet::new(), expected: HashMap::new(),
        };
        thread::spawn(move || collect_thread(state, rx))
    };

    // traverse dir, keep only files
    let files = walkdir::WalkDir::new(&task.path)
        .follow_links(true)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.file_type().is_file())
        .map(|e| e.into_path())
        .filter(|p| p.extension().map(|e| e == "cnf").unwrap_or(false));

    for path in files {
        let path = Arc::new(path);
        //println!("test on {}", path.display());
        for solver in solvers.iter() {
            // solve in a worker thread
            let tx = tx.clone();
            let checker = task.checker.clone();
            let solver = solver.clone();
            let path = path.clone();
            tx.send(SyncMsg::StartedJob).unwrap(); // must wait for one more job

            pool.execute(move || {
                let c = solve_file(solver, path, &checker).unwrap();
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
    let dir = std::env::var("DIR").ok().unwrap_or("msat".to_owned());
    let timeout: i64 = std::env::var("TIMEOUT").ok().unwrap_or("10".to_owned()).parse()?;
    let jobs: usize = std::env::var("JOBS").ok().unwrap_or("3".to_owned()).parse()?;
    let checker = std::env::var("CHECKER").ok();

    let dres = process_task(
        &DirTask {path: Path::new(&dir).to_owned(), timeout, jobs, checker})?;

    println!("{:?}", dres.stats);
    if dres.failures.len() != 0 {
        println!("{} ({})", Red.bold().paint("FAILURE"), dres.failures.len());
        for f in dres.failures.iter() {
            println!("  failure on: {:?}", f)
        }
        panic!() // oh no
    } else if dres.n_check_failed != 0 {
        println!("{} ({})", Red.bold().paint("CHECK FAILURE(S)"), dres.n_check_failed);
        panic!() // oh no
    } else {
        println!("{}", Green.bold().paint("OK"));
        Ok(())
    }
}
