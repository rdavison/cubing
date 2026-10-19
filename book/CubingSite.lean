import VersoManual
import CubingSite.Chapters
import CubingSite.Widget

open Verso.Genre Manual
open CubingSite

#doc (Manual) "Cubing" =>

%%%
authors := ["Richard Davison"]
%%%

An interactive cubing reference and trainer. Every definition is Lean code, every claim is a
theorem checked by Lean, and every cube diagram is computed from the formal model when the site
is built. Step through any algorithm move by move, and hover over any code to see its type.

Solving methods are treated as programs: they can be proved correct and compared by number of
algorithms, number of moves, and amount to memorise. The first part is a precise model of the
3x3x3 cube.

```cube
R U R' U'
```

# The 3x3x3 cube

These chapters build the cube group from Mathlib's semidirect products, give the face turns as
tables, and prove the fundamental theorem. A state can be reached exactly when its corner twists
total zero, its edge flips total zero, and its corner and edge permutations have the same parity.

A face turn moves four corners and four edges round a cycle.

```cube
F
```

{chapter Cubing.Cube3x3.Basic "Pieces and states"}

{chapter Cubing.Cube3x3.Moves "Face turns"}

{chapter Cubing.Cube3x3.Notation "Move notation"}

{chapter Cubing.Cube3x3.Invariants "Invariants"}

{chapter Cubing.Cube3x3.Generate "Generating the cube group"}

## Algorithms used in the proof

The proof that every valid state is reachable uses these algorithms. The T-perm swaps two corners
and two edges:

```cube
R U R' U' R' F R2 U' R' U' R U R' F'
```

The A-perm cycles three corners and nothing else:

```cube
R' F R' B2 R F' R' B2 R2
```

The U-perm cycles three edges and nothing else:

```cube
R U' R U R U R U' R' U' R2
```

Repeated sledgehammers twist two corners in opposite directions:

```cube
R' D' R D R' D' R D U R' D' R D R' D' R D R' D' R D R' D' R D U'
```

and a fourteen-move sequence flips two edges:

```cube
F R B L U L' U B' R' F' L' U' L U'
```

{chapter Cubing.Cube3x3.Solvable "Reachable states"}

{chapter Cubing.Cube3x3.Facelets "Stickers and facelets"}

{checkCoverage}
