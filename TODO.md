
- theory:
  * remove `add theory lemma` (until we can add clauses during search)
  * add `add theory conflict` that would shortpath into `analyze`
    (start with an initial clause that is `&[Lit]`, no allocation, no theory lemma,
     just the learnt clause)
  * use this `add theory conflict` in batsmt
  * generalize conflict analysis so every resolution step can use `{CRef,&[Lit],Propagation}`
    (then enable propagations in batsmt)
  * add `propagate` to the TheoryArg, with `lit * SmallVec<lit>`
    → need to properly use it in explanation
      (turn it into a clause on the fly if used in a conflict?
       or resolve directly anyway?)

- use bitset for more compact `IntMap<K,bool>`
- redo allocator, ECS style
  * `headers: Vec<ClauseHeader>` (also use it for `size`), touched the most often
  * `lits: Vec<Lit>` flat array of lits
  * `data: Vec<ClauseData>` where `ClauseData = union { reloc: u32, offset: u32 }`
    (either reloc'd to another clause, or offset in `lits`.
    with `data[i].offset` and `headers[i].size()` one can reconstruct a slice in `lits`
  * `extra: Vec<u64>` non-empty iff extra data enabled (all or none)

- try using https://crates.io/crates/roaring for watch lists?

- push/pop
- try http://contain-rs.github.io/bit-vec/bit_vec/ for IntSet (more compact)
- nice API around the core solver for unsat cores, push/pop, etc.
  which allocates new literals as needed
- minimal unsat cores using card constraints
- finish ipasir interface
- ~~Pseudo Boolean~~ cardinality constraints --> minimal unsat cores

http://algo.informatik.uni-tuebingen.de/forschung/sat/SlidesDanielLeBerreWorkshopTuebingen.pdf

- lingeling optim for binary clauses:
  https://www.msoos.org/2014/08/on-using-less-memory-for-binary-clauses-in-lingeling/
  * separate watches for binary clauses? store the other literal
    in the watchlist  (e.g. for `a ∨ b` store `b` in watch list for `¬a`)
  * propagate binary clauses first (faster)
  * for conflict, fill local vector eagerly? or be able to point to the binary clause somehow?

## Done

- parametrize to get SMT like-theory
- optional DRAT output
- provide closure `|| -> bool` for checking resources
  * move libc dep into the binary itself
  * update ipasir interface
- unsat cores
- ~~Pseudo Boolean~~ ~~cardinality constraints~~ --> minimal unsat cores
- rename into "batsat" (done in Austin!)
