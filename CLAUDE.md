# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

cubing is an interactive cubing reference and trainer: a Lean 4 formalization published
as a Verso site. Code and documentation are both first-class: the library's modules *are* the book's
chapters, every reference in their prose is elaborated, and every cube picture in the book is
computed from the formal model. Changing either side without the other fails the build. There is
no test framework: the theorems are the tests.

The long-term goal is to formalise blindfolded solving methods as a DSL and optimise them for
different objectives (fewest algorithms, fewest moves, least to memorise). The 3x3x3 cube
model comes first.

## Commands

```sh
lake exe cache get     # fetch prebuilt mathlib oleans — do this before the first build
lake build --wfail     # Cubing and CubingAudit (default targets); --wfail as CI does
lake build Cubing.Cube3x3.Solvable   # build one module and its deps
lake env lean Cubing/Cube3x3/Basic.lean   # elaborate one file; needs its imports built first
lake build cubing-exe && lake exe cubing-exe   # prints the net after R U R' U'

cd book                          # the site is a separate Lake package
lake build                       # elaborates every chapter and computes every cube picture
lake exe cubing-site        # writes the site to book/_out/html-multi
python3 -m http.server 8737 --directory _out/html-multi   # preview it
```

`lean-toolchain` pins `leanprover/lean4:v4.29.0-rc4` (also in `book/`). mathlib is required at
`rev = "master"` and Verso at the tag `v4.29.0-rc4`, both resolved to fixed commits in
`lake-manifest.json`. Never run a bare `lake update`: it moves mathlib to current master. To add or
move one dependency, run `lake update <name>`.

## The experimental module system

Every file under `Cubing/` and `CubingImpl/` opens with a bare `module` line. Imports that
re-export must be `public import`; declarations are private unless public, and these files open
an `@[expose] public section` so everything is public and definitionally transparent.
`@[expose]` is load-bearing: the cube proofs evaluate closed states by `rfl`.

A macro may only call `meta` definitions. The `cube[…]` notation therefore has its own
compile-time token reader (`tokenNames?`), mirroring `Move.ofChars?`.

`Main.lean`, `CubingAudit.lean`, `CubingResults.lean` and everything in `book/` are not
modules.

**Option names in `lakefile.toml` must be unquoted dotted keys**, e.g.
`leanOptions = {doc.verso = true, linter.missingDocs = true}`. A quoted key `"doc.verso"` becomes
the single atomic name `«doc.verso»`. In `leanOptions` it is rejected; in `weakLeanOptions` it is
silently ignored. Check `.lake/build/ir/<Mod>.setup.json` to see which options actually reach
Lean.

## Code is documentation is code

- `Cubing` is built with `doc.verso = true` and `linter.missingDocs = true`, and CI uses
  `--wfail`. Docstrings and `/-! … -/` module docs are Verso markup:
  - `` {name}`x` `` and `` {lean}`term` `` are elaborated, so renames and type changes break
    them;
  - `` {given}`x : T` `` introduces one variable for later `{lean}` uses;
  - `` {lit}`…` `` is for things that are not Lean, such as move sequences like {lit}`R U R' U'`;
  - plain backticks are a warning ("could be more specific"), and therefore an error in CI.
- Prose can only refer to declarations above it. Put a module doc after the declarations it
  mentions.
- **Every library file must contain the line `set_option doc.verso true`** right after its
  imports. Verso's literate extractor re-elaborates each file with only its in-file options, so
  without the line the prose reaches the book as raw markup. `{chapter}` enforces this.
- A `/-! … -/` placed directly before `end` rendered as raw text in the book. Follow mid-file
  prose with a declaration.
- `book/` sets `packagesDir = "../.lake/packages"` (and the same in its manifest), so both
  workspaces share one Mathlib and one compiled Verso. CI caches `.lake` and `book/.lake` together,
  after the site build. The site executable links Mathlib, and Mathlib's cache ships only
  `.olean` files, so the cache keeps Mathlib's compiled objects (`build/ir`, about 300 MB) and
  excludes only its `build/lib`.
- `book/` is a separate Lake package because each `{chapter}` runs `lake query
  +Mod:literate` in the root project. Running that query in the workspace that is already
  building would contend for its lock.
- Each chapter is a whole module, included by `{chapter Module "Title"}`
  (`book/CubingSite/Chapters.lean`). `{checkCoverage}` at the end of the book fails if any
  `Cubing/**/*.lean` is not a chapter. Adding a module means adding its chapter.
- Verso's `literate` facet is traced on the module's public `.olean`, which does not change when
  only prose changes (module docs live in `.olean.server`). `{chapter}` therefore deletes the
  extracted JSON whenever any library source differs from the hash in
  `.lake/build/literate/**/*.src-hash`.
- Cube pictures: a ```` ```cube ```` block in the book (`book/CubingSite/Widget.lean`)
  parses its moves with the library's `parseAlg?` and colours every intermediate state with
  `Cubing.Cube3x3.colors`, at elaboration time. The page's JS only draws. Keep all puzzle logic
  out of the JS.
- CI builds the library, then the book, and on pushes to `main` deploys `book/_out/html-multi`
  to GitHub Pages.

## Architecture

Namespace `Cubing.Cube3x3`, one module per chapter, in reading order. Name things
matter-of-factly: no trademarked puzzle names and no jokes. Standard cubing terms such as T-perm
are fine.

- **`Cube3x3/Basic.lean`.** `Corner` (8) and `Edge` (12), named by Singmaster slot.
  - The generic `OPerm α n := (α → Multiplicative (ZMod n)) ⋊[mulAutArrow] Perm α`, where
    `⟨o, σ⟩` sends the piece in slot `a` to `σ a` and it gains twist `o (σ a)`.
  - `Cube := OPerm Corner 3 × OPerm Edge 2`.
  - **`g * h` does `h` first**, so the sequence "R U" is `move .U * move .R`.
- **`Cube3x3/Moves.lean`.** Six quarter turns as explicit tables, generated from Kociemba's standard
  cubie tables (U/D twist nothing; F/B flip edges).
  - `cube_eq` proves closed state equalities slot by slot (ext + `rfl`).
  - `reachable` is the closure of the six turns.
- **`Cube3x3/Notation.lean`.** `Move`, `alg` (left-to-right sequences), `alg_cons`/`alg_append`,
  and the `cube[R U R' U']` term notation.
  - `parseAlg?` and `renderAlg` work over `List Char`, because `String` functions do not reduce
    in proofs.
  - Sanity theorems (`commutatorRU_pow_six`, `RU_pow_105`, `tPerm_sq`): R U R' U' has order
    dividing 6, R U dividing 105, and the T-perm is an
    involution.
- **`Cube3x3/Invariants.lean`.** `twistSum` (via `SemidirectProduct.lift`), `parity`,
  `invariants`, `valid := invariants.ker`.
  - `reachable_le_valid`; face-turn signs come from explicit 3-swap decompositions.
  - `card_cube`, `invariants_surjective`, `card_valid = 43252003274489856000`.
- **`Cube3x3/Generate.lean`.** The generic generation lemma `OPerm.SetUp.le`. It assumes full set-up
  moves, one 3-cycle, one two-slot twist (`pairTwist`) and total twist zero, and concludes that
  every zero-twist even state is in K. It uses Mathlib's `closure_three_cycles_eq_alternating`
  and `isConj_iff_cycleType_eq`.
- **`Cube3x3/Solvable.lean`.** The lemma applied to corners and edges with concrete algorithms
  (T-perm, A-perm, U-perm, `twoCornerTwist`, `twoEdgeFlip`, and a corner 8-cycle and an edge
  12-cycle for `closure_cycle_adjacent_swap`).
  - Headline: `reachable_eq_valid`, `card_reachable`.
- **`Cube3x3/Facelets.lean`.** The sticker action `OPerm α n` on `α × ZMod n` (faithful).
  - `toStickers : Cube →* Perm Sticker` with `toStickers_injective`.
  - `colors` on the 54-facelet net, tied to `toStickers` by `colors_corner` and `colors_edge`.
  - Geometry for the 3D view: `Facelet.cubie`/`Facelet.normal` in ℤ³, `Face.layer`,
    `Face.turnVec`. `colors_move_mul` proves a face turn is that rotation of its layer.

Libraries: `Cubing` (maths, Mathlib), `CubingImpl` (executable, no Mathlib,
`precompileModules`; currently a stub), `CubingAudit` (axiom pins, non-module, default target),
`CubingResults` (the only place for `native_decide`; not a default target; empty). CI greps
`CubingImpl` for `implemented_by`, `@[extern`, `unsafe`, `partial def`, `native_decide`,
`bv_decide`.

## Proof conventions

- Closed cube equalities: `cube_eq`, or `Equiv.ext fun c => by cases c <;> rfl` for one
  permutation. Plain `decide` gets stuck on an `Eq.rec` inside Mathlib's decidability instances
  for these types. `decide +kernel` works for `Finset` products over the enums
  (`twistSum_move_fst`).
- Long words need `set_option maxRecDepth 100000 in` (the `alg` fold).
- Signs of concrete permutations: rewrite to a product of `swap`s by `Equiv.ext`, then
  `Perm.sign_swap`. Cycles: rewrite to `List.formPerm` and use `List.isCycle_formPerm` and
  `support_formPerm_of_nodup`. 3-cycles: `isThreeCycle_swap_mul_swap_same`.
- State generic facts once, on `OPerm α n`, and instantiate them for corners and edges.
- Raise `maxRecDepth` rather than reaching for `native_decide` outside `CubingResults`.
