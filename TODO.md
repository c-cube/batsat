
- use bitset for more compact `IntMap<K,bool>`
- redo allocator, ECS style
  * `headers: Vec<ClauseHeader>` (also use it for `size`), touched the most often
  * `lits: Vec<Lit>` flat array of lits
  * `data: Vec<ClauseData>` where `ClauseData = union { reloc: u32, offset: u32 }`
    (either reloc'd to another clause, or offset in `lits`.
    with `data[i].offset` and `headers[i].size()` one can reconstruct a slice in `lits`
  * `extra: Vec<u64>` non-empty iff extra data enabled (all or none)

- parametrize to get SMT like stuff?
- push/pop
- finish ipasir interface and test it

http://algo.informatik.uni-tuebingen.de/forschung/sat/SlidesDanielLeBerreWorkshopTuebingen.pdf

- lingeling optim for binary clauses:
  https://www.msoos.org/2014/08/on-using-less-memory-for-binary-clauses-in-lingeling/
  * separate watches for binary clauses? store the other literal
    in the watchlist  (e.g. for `a ∨ b` store `b` in watch list for `¬a`)
  * propagate binary clauses first (faster)
  * for conflict, fill local vector eagerly? or be able to point to the binary clause somehow?

## Done

- optional DRAT output
- provide closure `|| -> bool` for checking resources
  * move libc dep into the binary itself
  * update ipasir interface
- unsat cores
- ~~Pseudo Boolean~~ ~~cardinality constraints~~ --> minimal unsat cores
