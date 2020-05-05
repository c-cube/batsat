/*****************************************************************************************[dimacs.rs]
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

use {
    crate::{
        interface::SolverInterface,
        {lbool, Lit},
    },
    std::io::{self, BufRead},
};

/// `parse(input, solver)` adds the content of `input` to the solver
///
/// ## Params
/// - `is_strict` if true, will fail if number of clauses/vars does not match the declared header
/// - `incremental` if true, accept the [.icnf format](http://www.siert.nl/icnf/)
/// - `solver` is used to process incremental calls (`a` lines in icnf)
/// - `th` is given to `solver` to solve.
pub fn parse<S: SolverInterface, R: BufRead>(
    input: &mut R,
    solver: &mut S,
    is_strict: bool,
    incremental: bool,
) -> io::Result<()> {
    let mut lits = vec![];
    // let mut num_vars = 0;
    let mut num_clauses = 0;
    let mut num_read_clauses = 0;
    loop {
        skip_whitespace(input)?;
        let ch = next_byte(input)?;
        if ch == Some(b'p') {
            if incremental {
                skip_line(input)?;
                continue;
            }
            let mut header = [0; 5];
            input.read_exact(&mut header)?;
            if &header != b"p cnf" {
                return parse_error(format!("PARSE ERROR! Unexpected char: p"));
            }
            // num_vars = parse_int(input)?;
            parse_int(input)?;
            num_clauses = parse_int(input)?;
        // eprintln!("num_vars = {}", num_vars);
        // eprintln!("num_clauses = {}", num_clauses);
        } else if ch == Some(b'c') {
            skip_line(input)?;
        } else if incremental && ch == Some(b'a') {
            input.consume(1); // skip 'a'
            read_clause(input, solver, &mut lits)?;
            debug!(
                "solve with assumptions {:?} (ok: {})",
                &lits,
                solver.is_ok()
            );
            solver.simplify();
            let res = solver.solve_limited(&lits); // solve under assumptions
            match res {
                x if x == lbool::TRUE => println!("SAT"),
                x if x == lbool::FALSE => println!("UNSAT"),
                x => {
                    assert_eq!(x, lbool::UNDEF);
                    println!("UNKNOWN")
                }
            }
        } else if let Some(_) = ch {
            read_clause(input, solver, &mut lits)?;
            solver.add_clause_reuse(&mut lits);
            num_read_clauses += 1;
        } else {
            break;
        }
    }
    if is_strict && !incremental && num_clauses != num_read_clauses {
        return parse_error(format!(
            "PARSE ERROR! DIMACS header mismatch: wrong number of clauses"
        ));
    }
    Ok(())
}

fn read_clause<S: SolverInterface, R: BufRead>(
    input: &mut R,
    solver: &mut S,
    lits: &mut Vec<Lit>,
) -> io::Result<()> {
    lits.clear();
    loop {
        let parsed_lit = parse_int(input)?;
        if parsed_lit == 0 {
            return Ok(());
        }
        let var = (parsed_lit.abs() - 1) as u32;
        let lit = Lit::new(solver.var_of_int(var), parsed_lit > 0);
        lits.push(lit);
    }
}

fn parse_int<R: BufRead>(input: &mut R) -> io::Result<i32> {
    skip_whitespace(input)?;
    let ch = next_byte(input)?;
    let neg = if ch == Some(b'+') || ch == Some(b'-') {
        input.consume(1);
        ch == Some(b'-')
    } else {
        false
    };
    if let Some(ch) = next_byte(input)? {
        if !(b'0' <= ch && ch <= b'9') {
            return parse_error(format!("PARSE ERROR! Unexpected char: {}", ch as char));
        }
    } else {
        return parse_error(format!("PARSE ERROR! Unexpected EOF"));
    };
    let mut val = 0;
    while let Some(ch) = next_byte(input)? {
        if !(b'0' <= ch && ch <= b'9') {
            break;
        }
        input.consume(1);
        val = val * 10 + (ch - b'0') as i32;
    }
    if neg {
        Ok(-val)
    } else {
        Ok(val)
    }
}

#[inline(always)]
fn is_whitespace(ch: Option<u8>) -> bool {
    ch.map(|ch| b'\x09' <= ch && ch <= b'\x0d' || ch == b' ')
        .unwrap_or(false)
}

fn skip_whitespace<R: BufRead>(input: &mut R) -> io::Result<()> {
    while is_whitespace(next_byte(input)?) {
        input.consume(1);
    }
    Ok(())
}

fn skip_line<R: BufRead>(input: &mut R) -> io::Result<()> {
    loop {
        if let Some(ch) = next_byte(input)? {
            input.consume(1);
            if ch == b'\n' {
                return Ok(());
            }
        } else {
            return Ok(());
        }
    }
}

fn next_byte<R: BufRead>(input: &mut R) -> io::Result<Option<u8>> {
    Ok(input.fill_buf()?.first().map(|&ch| ch))
}

fn parse_error<T>(message: String) -> io::Result<T> {
    Err(io::Error::new(io::ErrorKind::InvalidInput, message))
}
