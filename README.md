# cubing

An interactive cubing reference and trainer, formalised in Lean 4. Every definition is Lean
code, every claim is a machine-checked theorem, and every cube diagram is computed from the
formal model when the site is built.

The first part builds the 3x3x3 cube group from Mathlib's semidirect products and proves the
fundamental theorem. A state can be reached exactly when its corner twists total zero, its edge
flips total zero, and its corner and edge permutations have the same parity. There are
43,252,003,274,489,856,000 such states.

Next come solving methods, treated as programs: proved correct, and compared by number of
algorithms, number of moves, and amount to memorise.

```sh
lake exe cache get
lake build --wfail                       # the library; the theorems are the tests
cd book && lake build && lake exe cubing-site   # the site
```

The site is written to `book/_out/html-multi`.
