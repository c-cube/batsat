//! Representation of sudoku grids.

/// Dimension of the grid
pub const DIM: usize = 9;

pub type CellValue = u8;

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub enum Cell {
    Empty,
    Full(CellValue),
}

/// A sudoku grid.
#[derive(Clone, Debug)]
pub struct Grid {
    cells: [[Cell; DIM]; DIM],
}

/// A position in the grid.
pub type Position = (u8, u8);

impl std::cmp::PartialEq<u8> for Cell {
    fn eq(&self, x: &u8) -> bool {
        match self {
            Cell::Full(n) => n == x,
            Cell::Empty => false,
        }
    }
}

impl Cell {
    /// Is the cell empty?
    #[inline(always)]
    pub fn empty(&self) -> bool {
        match self {
            Cell::Empty => true,
            _ => false,
        }
    }

    #[inline(always)]
    pub fn full(&self) -> bool {
        !self.empty()
    }
}

impl Grid {
    /// New sudoku, from the given grid.
    pub fn new(cells: [[Cell; DIM]; DIM]) -> Self {
        Grid { cells }
    }

    /// Iterate over all cells.
    pub fn iter_cells(&self) -> impl Iterator<Item = &Cell> {
        self.cells.iter().flat_map(|row| row.iter())
    }

    /// Iterate over all cells, with their position.
    pub fn iter(&self) -> impl Iterator<Item = (&Cell, Position)> {
        self.cells.iter().enumerate().flat_map(move |(i, row)| {
            row.iter()
                .enumerate()
                .map(move |(j, c)| (c, (i as u8, j as u8)))
        })
    }

    /// All cells are full?
    pub fn full(&self) -> bool {
        self.iter_cells().all(|&c| c != Cell::Empty)
    }

    /// Make a string representing the grid.
    pub fn render(&self) -> String {
        let mut s = String::new();
        for _i in 0..11 {
            s.push('-');
        }
        s.push('\n');
        for row in self.cells.iter() {
            s.push('|');
            for &c in row.iter() {
                let c: char = match c {
                    Cell::Empty => '.',
                    Cell::Full(n) => std::char::from_u32((n + b'0') as u32).unwrap(),
                };
                s.push(c);
            }
            s.push('|');
            s.push('\n');
        }
        for _i in 0..11 {
            s.push('-');
        }
        s.push('\n');
        s
    }

    /// Iterate over distinct pairs of `(position,cell)` that belong in the same square.
    pub fn iter_square_pairs(
        &self,
    ) -> impl Iterator<Item = ((Position, &Cell), (Position, &Cell))> {
        IterSq {
            grid: &self,
            line: 0,
            col: 0,
            i: 0,
            j: 1,
        }
    }

    /// Does this grid satisfy normal constraints?
    pub fn is_correct(&self) -> bool {
        // rows
        for row in self.cells.iter() {
            for i in 0..DIM as u8 {
                for j in i + 1..DIM as u8 {
                    if row[i as usize] == row[j as usize] {
                        return false;
                    }
                }
            }
        }

        for col in 0..DIM as u8 {
            for i in 0..DIM as u8 {
                for j in i + 1..DIM as u8 {
                    if self[(i, col)] == self[(j, col)] {
                        return false;
                    }
                }
            }
        }

        for ((p1, c1), (p2, c2)) in self.iter_square_pairs() {
            assert_ne!(p1, p2);
            if c1 == c2 {
                return false;
            }
        }

        true
    }
}

impl std::ops::Index<Position> for Grid {
    type Output = Cell;
    #[inline(always)]
    fn index(&self, p: Position) -> &Self::Output {
        &self.cells[p.0 as usize][p.1 as usize]
    }
}

impl std::ops::IndexMut<Position> for Grid {
    #[inline(always)]
    fn index_mut(&mut self, p: Position) -> &mut Self::Output {
        &mut self.cells[p.0 as usize][p.1 as usize]
    }
}

// iterator over squares.
// invariant: i<j
struct IterSq<'a> {
    grid: &'a Grid,
    line: u8,
    col: u8,
    i: u8,
    j: u8,
}

impl<'a> Iterator for IterSq<'a> {
    type Item = ((Position, &'a Cell), (Position, &'a Cell));
    fn next(&mut self) -> Option<Self::Item> {
        if self.j == 9 {
            self.i += 1;
            self.j = self.i + 1; // j>i
        }
        if self.i >= 8 {
            // means j >= 9
            self.j = 1;
            self.i = 0;
            self.col += 1;
        }
        if self.col == 3 {
            self.line += 1;
            self.col = 0;
        }
        if self.line == 3 {
            return None; // done
        }
        debug_assert!(self.i < 9 && self.j < 9 && self.col < 3 && self.line < 3);

        let pos1 = (3 * self.line + self.i / 3, 3 * self.col + self.i % 3);
        let pos2 = (3 * self.line + self.j / 3, 3 * self.col + self.j % 3);
        debug_assert_ne!(pos1, pos2);

        self.j += 1;

        Some(((pos1, &self.grid[pos1]), (pos2, &self.grid[pos2])))
    }
}
