# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

tom-y-jerry is a Lean 4 formalization with machine-checked proofs. There is no test framework:
the theorems *are* the tests, so `lake build` succeeding is the only correctness signal. CI
(`.github/workflows/lean_action_ci.yml`) runs `leanprover/lean-action@v1`, which is just a build.

## Commands

```sh
lake exe cache get     # fetch prebuilt mathlib oleans — do this before the first build
lake build             # builds TomYJerry and TomYJerryAudit (default targets); the real "test suite"
lake build TomYJerry.Basic       # build one module and its deps
lake build tom-y-jerry-exe       # native build; `lake build` alone leaves the binary stale
lake exe tom-y-jerry-exe
lake env lean TomYJerry/Basic.lean   # elaborate one file directly; fastest edit loop
```

`lean-toolchain` pins `leanprover/lean4:v4.29.0-rc4` and elan selects it automatically.
mathlib is required at `rev = "master"` in `lakefile.toml` but resolved to a fixed commit in
`lake-manifest.json` — do not run `lake update` casually, as it moves mathlib to current master
and can break every proof at once.

## The experimental module system

`lakefile.toml` sets `weakLeanOptions = {"experimental.module" = true}` on `TomYJerry` and
`TomYJerryImpl`. This changes the surface syntax:

- Every file in those libraries opens with a bare `module` line.
- Imports that re-export must be `public import` (see `TomYJerry.lean`, the library root). A plain
  `import` is private to that file.
- Declarations are private by default. Either annotate each one `public`/`private`, or open an
  `@[expose] public section` after the imports so everything below is public *and* definitionally
  transparent. `@[expose]` is load-bearing: without it, downstream `rfl`/`decide` cannot unfold
  the definitions.

`Main.lean`, `TomYJerryAudit.lean` and `TomYJerryResults.lean` are *not* modules — plain `import`.

## The four libraries

- **`TomYJerry`** — the mathematics and the correctness proofs, with Mathlib.
- **`TomYJerryImpl`** — executable code. It imports **no Mathlib** and has
  `precompileModules = true`, so `native_decide` over it runs compiled code rather than the
  (far slower) interpreter. Keep Mathlib out of it.
- **`TomYJerryAudit`** pins each headline theorem's axioms with `#guard_msgs in #print axioms`. It
  is a separate **non-module** library because `#print axioms` is rejected inside a `module` file,
  and it is a default target so `lake build` enforces it.
- **`TomYJerryResults`** holds `native_decide` results and is the only place native evaluation is
  allowed. It is **not** a default target.

CI greps `TomYJerryImpl` for `implemented_by`, `@[extern`, `unsafe`, `partial def`,
`native_decide` and `bv_decide`: the axiom audit cannot see a definition whose compiled code
differs from its logical model. Write verified loops as structural recursion on a `Nat` fuel, not
`for`/`mut`.

## Proof conventions

- Prefer `by decide` for finite enumerations; raise `maxRecDepth` (4096) rather than reaching for
  `native_decide` outside `TomYJerryResults`.
- For a closed equality of lists or other data, prefer `rfl` to `decide`.
- `Finset` operations reduce through `Quot` and are far slower in the kernel than `List` ones;
  prefer `List` for anything quantified over many cases.
- Downstream of a module exposing closed `Finset` data, mark it `attribute [local irreducible]`
  in a `section` and use stated membership lemmas. Symptom otherwise:
  `(deterministic) timeout at 'whnf'` on a proof that looks trivial.
- A `Fintype` instance on a huge closed type runs at module initialisation and can hang the
  executable before `main`; make such instances `noncomputable`.
