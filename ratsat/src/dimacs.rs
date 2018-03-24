use std::io::{self, BufRead};
use {Lit, Var, Solver};

pub fn parse<R: BufRead, S: Solver>(input: &mut R, solver: &mut S, is_strict: bool) -> io::Result<()> {
    let mut num_vars = 0;
    let mut num_clauses = 0;
    let mut num_read_clauses = 0;
    loop {
        skip_whitespace(input)?;
        let ch = next_byte(input)?;
        if ch == Some(b'p') {
            let mut header = [0; 5];
            input.read_exact(&mut header)?;
            if &header != b"p cnf" {
                return parse_error(format!("PARSE ERROR! Unexpected char: p"));
            }
            num_vars = parse_int(input)?;
            num_clauses = parse_int(input)?;
            eprintln!("num_vars = {}", num_vars);
            eprintln!("num_clauses = {}", num_clauses);
        } else if ch == Some(b'c') {
            skip_line(input)?;
        } else if let Some(_) = ch {
            let lits = read_clause(input, solver)?;
            solver.add_clause_owned(lits);
            num_read_clauses += 1;
        } else {
            break;
        }
    }
    if is_strict && num_clauses != num_read_clauses {
        return parse_error(format!("PARSE ERROR! DIMACS header mismatch: wrong number of clauses"));
    }
    Ok(())
}

fn read_clause<R: BufRead, S: Solver>(input: &mut R, solver: &mut S) -> io::Result<Vec<Lit>> {
    let mut lits = vec![];
    loop {
        let parsed_lit = parse_int(input)?;
        if parsed_lit == 0 {
            return Ok(lits);
        }
        let var = (parsed_lit.abs() - 1) as u32;
        while var >= solver.num_vars() {
            solver.new_var();
        }
        lits.push(Lit::new(Var::from_idx(var), parsed_lit < 0));
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

fn skip_whitespace<R: BufRead>(input: &mut R) -> io::Result<()> {
    let is_whitespace = |ch: Option<u8>| {
        ch.map(|ch| b'\x09' <= ch && ch <= b'\x0d' || ch == b' ')
            .unwrap_or(false)
    };
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
