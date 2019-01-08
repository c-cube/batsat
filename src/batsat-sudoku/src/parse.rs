
//! Sudoku parser.
//!
//! A sudoku is represented by 81 characters, either `.` or a `1-9` integer.

use {
    crate::{Grid,Cell,Result},
    std::io::{Read, BufRead, BufReader},
};

/// Parse grids from the given reader.
pub fn parse<R:Read>(r: R) -> Result<Vec<Grid>> {
    let r = BufReader::new(r);
    let mut res = vec!();

    for line in r.lines() {
        let line = line?;
        let line = line.trim().as_bytes();
        if line == &[] {
            continue // blank line
        } else if line.len() < 81 {
            let msg = format!("cannot parse {:?}, too short", line);
            return Err(msg.into());
        }

        let line = &line[..81]; // ignore the end of the line
        let mut cells = [[Cell::Empty; 9]; 9];
        for (idx,c) in line.iter().enumerate() {
            let cell = match *c {
                b'0' | b'.' => Cell::Empty,
                b'1' ..= b'9' => {
                    let n = *c as u8 - b'0' as u8;
                    assert!(n >= 1 && n <= 9);
                    Cell::Full(n)
                },
                _ => {
                    let msg = format!("unknown cell {:?}",
                                      std::char::from_u32(*c as u32).unwrap());
                    return Err(msg.into());
                }
            };

            let i = idx / 9;
            let j = idx % 9;
            cells[i][j] = cell;
        }
        res.push(Grid::new(cells))
    }

    Ok(res)
}


