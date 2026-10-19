module
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.DeriveFintype

set_option doc.verso true

/-!
A 3x3x3 cube has twenty moving pieces: eight corners and twelve edges. The centres never move
relative to each other, so they fix the frame. A blindfolded solver reasons about exactly what
this chapter formalises. Each piece sits in a *slot*, and each piece has an *orientation*
relative to its slot: a corner can be twisted three ways, an edge flipped two ways.

Pieces are named by the slot they occupy when the cube is solved, in Singmaster notation.
-/

@[expose] public section

namespace Cubing.Cube3x3

/-- The eight corner slots, named by the faces they touch, the up or down face first. -/
inductive Corner where
  /-- Up, right, front. -/ | URF
  /-- Up, front, left. -/ | UFL
  /-- Up, left, back. -/ | ULB
  /-- Up, back, right. -/ | UBR
  /-- Down, front, right. -/ | DFR
  /-- Down, left, front. -/ | DLF
  /-- Down, back, left. -/ | DBL
  /-- Down, right, back. -/ | DRB
  deriving DecidableEq, Fintype, Repr, Inhabited

/-- The twelve edge slots, named by the faces they touch. -/
inductive Edge where
  /-- Up, right. -/ | UR
  /-- Up, front. -/ | UF
  /-- Up, left. -/ | UL
  /-- Up, back. -/ | UB
  /-- Down, right. -/ | DR
  /-- Down, front. -/ | DF
  /-- Down, left. -/ | DL
  /-- Down, back. -/ | DB
  /-- Front, right. -/ | FR
  /-- Front, left. -/ | FL
  /-- Back, left. -/ | BL
  /-- Back, right. -/ | BR
  deriving DecidableEq, Fintype, Repr, Inhabited

/-!
# Orientation and permutation together

A move does two things to a family of pieces: it permutes them among their slots, and it changes
how each one sits in its new slot. Mathlib's {name}`SemidirectProduct` captures exactly this. An
element pairs an orientation change for every slot, a function into the cyclic group
{lean}`Multiplicative (ZMod 3)` (for corners), with a permutation of the slots. Permutations
act on orientation vectors through {name}`mulAutArrow`, by relabelling slots.

The same construction serves corners (three twists) and edges (two flips), so it is defined once.
-/

/--
The orientation-permutation group of pieces of type {lean}`α` with {lean}`n` orientations each.
For {given}`o : α → Multiplicative (ZMod n)`, {given}`σ : Equiv.Perm α` and {given}`a : α`, the
element {lean}`(⟨o, σ⟩ : OPerm α n)` sends the piece in slot {lean}`a` to slot {lean}`σ a`, and
that piece gains the twist {lean}`o (σ a)` there.
-/
abbrev OPerm (α : Type) (n : ℕ) :=
  (α → Multiplicative (ZMod n)) ⋊[mulAutArrow] Equiv.Perm α

/-- Corner states: eight corners, each twisted one of three ways. -/
abbrev CornerGroup := OPerm Corner 3

/-- Edge states: twelve edges, each flipped one of two ways. -/
abbrev EdgeGroup := OPerm Edge 2

/-!
Corners and edges never trade places, so a cube state is a corner state together with an edge
state. Mathlib's product group does the rest.
-/

/-- A state of the cube, relative to the fixed centres. -/
abbrev Cube := CornerGroup × EdgeGroup

/-!
# Composition order

Group multiplication is composition of functions. For {given}`g : Cube` and {given}`h : Cube`,
the product {lean}`g * h` does {lean}`h` first and then {lean}`g`. So the move sequence written
{lit}`R U`, which turns R and then U, is the product of the U turn on the left with the R turn on
the right. This is the one place where the notation of cubers and the notation of group theory
disagree. The chapter on notation proves that the two agree once the order is reversed.
-/

/-- Multiplication in {name}`OPerm` composes the permutations, the right factor acting first. -/
theorem OPerm.mul_right {α : Type} {n : ℕ} (g h : OPerm α n) :
    (g * h).right = g.right * h.right := rfl

/-- The orientation of a product: the left factor's twist, plus the right factor's twist carried
along by the left factor's permutation. -/
theorem OPerm.mul_left_apply {α : Type} {n : ℕ} (g h : OPerm α n) (a : α) :
    (g * h).left a = g.left a * h.left (g.right⁻¹ a) := rfl

end Cubing.Cube3x3
