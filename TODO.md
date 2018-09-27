- use bitset for more compact `IntMap<K,bool>`
- parametrize to get SMT like stuff?
- push/pop
- finish ipasir interface and test it

http://algo.informatik.uni-tuebingen.de/forschung/sat/SlidesDanielLeBerreWorkshopTuebingen.pdf

- lingeling optim for binary clauses:
  https://www.msoos.org/2014/08/on-using-less-memory-for-binary-clauses-in-lingeling/

## Done

- optional DRAT output
- provide closure `|| -> bool` for checking resources
  * move libc dep into the binary itself
  * update ipasir interface
- unsat cores
- ~~Pseudo Boolean~~ ~~cardinality constraints~~ --> minimal unsat cores
