module
public import Cubing.Cube3x3.Basic
public import Mathlib.Algebra.Group.Subgroup.Lattice
meta import CubingDoc

set_option doc.verso true

/-!
The cube is turned by quarter turns of its six faces. Each is given here as a table. A table
lists, for every corner and edge slot, where the piece in that slot goes. Where a turn twists or
flips pieces, a second table lists the twist or flip each piece gains on arrival.

The orientation convention is the standard one for computer cube solving. A corner's twist is
measured from its sticker facing up or down. An edge's flip is measured from its sticker facing
up or down, or, for the four middle-layer edges, facing front or back. Under this convention the
up and down turns change no orientation, the four side turns twist corners, and only the front
and back turns flip edges.
-/

@[expose] public section

namespace Cubing.Cube3x3

/-- The six faces of the cube. -/
inductive Face where
  /-- The up face. -/ | U
  /-- The down face. -/ | D
  /-- The front face. -/ | F
  /-- The back face. -/ | B
  /-- The left face. -/ | L
  /-- The right face. -/ | R
  deriving DecidableEq, Fintype, Repr, Inhabited

/-- Where each corner goes under a clockwise quarter turn of a face. -/
def cornerPerm : Face → Equiv.Perm Corner
  | .U => {
    toFun := fun
      | .URF => .UFL
      | .UFL => .ULB
      | .ULB => .UBR
      | .UBR => .URF
      | .DFR => .DFR
      | .DLF => .DLF
      | .DBL => .DBL
      | .DRB => .DRB
    invFun := fun
      | .URF => .UBR
      | .UFL => .URF
      | .ULB => .UFL
      | .UBR => .ULB
      | .DFR => .DFR
      | .DLF => .DLF
      | .DBL => .DBL
      | .DRB => .DRB
    left_inv := by intro a; cases a <;> rfl
    right_inv := by intro a; cases a <;> rfl }
  | .D => {
    toFun := fun
      | .URF => .URF
      | .UFL => .UFL
      | .ULB => .ULB
      | .UBR => .UBR
      | .DFR => .DRB
      | .DLF => .DFR
      | .DBL => .DLF
      | .DRB => .DBL
    invFun := fun
      | .URF => .URF
      | .UFL => .UFL
      | .ULB => .ULB
      | .UBR => .UBR
      | .DFR => .DLF
      | .DLF => .DBL
      | .DBL => .DRB
      | .DRB => .DFR
    left_inv := by intro a; cases a <;> rfl
    right_inv := by intro a; cases a <;> rfl }
  | .F => {
    toFun := fun
      | .URF => .DFR
      | .UFL => .URF
      | .ULB => .ULB
      | .UBR => .UBR
      | .DFR => .DLF
      | .DLF => .UFL
      | .DBL => .DBL
      | .DRB => .DRB
    invFun := fun
      | .URF => .UFL
      | .UFL => .DLF
      | .ULB => .ULB
      | .UBR => .UBR
      | .DFR => .URF
      | .DLF => .DFR
      | .DBL => .DBL
      | .DRB => .DRB
    left_inv := by intro a; cases a <;> rfl
    right_inv := by intro a; cases a <;> rfl }
  | .B => {
    toFun := fun
      | .URF => .URF
      | .UFL => .UFL
      | .ULB => .DBL
      | .UBR => .ULB
      | .DFR => .DFR
      | .DLF => .DLF
      | .DBL => .DRB
      | .DRB => .UBR
    invFun := fun
      | .URF => .URF
      | .UFL => .UFL
      | .ULB => .UBR
      | .UBR => .DRB
      | .DFR => .DFR
      | .DLF => .DLF
      | .DBL => .ULB
      | .DRB => .DBL
    left_inv := by intro a; cases a <;> rfl
    right_inv := by intro a; cases a <;> rfl }
  | .L => {
    toFun := fun
      | .URF => .URF
      | .UFL => .DLF
      | .ULB => .UFL
      | .UBR => .UBR
      | .DFR => .DFR
      | .DLF => .DBL
      | .DBL => .ULB
      | .DRB => .DRB
    invFun := fun
      | .URF => .URF
      | .UFL => .ULB
      | .ULB => .DBL
      | .UBR => .UBR
      | .DFR => .DFR
      | .DLF => .UFL
      | .DBL => .DLF
      | .DRB => .DRB
    left_inv := by intro a; cases a <;> rfl
    right_inv := by intro a; cases a <;> rfl }
  | .R => {
    toFun := fun
      | .URF => .UBR
      | .UFL => .UFL
      | .ULB => .ULB
      | .UBR => .DRB
      | .DFR => .URF
      | .DLF => .DLF
      | .DBL => .DBL
      | .DRB => .DFR
    invFun := fun
      | .URF => .DFR
      | .UFL => .UFL
      | .ULB => .ULB
      | .UBR => .URF
      | .DFR => .DRB
      | .DLF => .DLF
      | .DBL => .DBL
      | .DRB => .UBR
    left_inv := by intro a; cases a <;> rfl
    right_inv := by intro a; cases a <;> rfl }

/-- The twist each corner gains on arriving in its new slot, as an element of {lean}`ZMod 3`. -/
def cornerTwist : Face → Corner → ZMod 3
  | .U, _ => 0
  | .D, _ => 0
  | .F, .URF => 1
  | .F, .UFL => 2
  | .F, .ULB => 0
  | .F, .UBR => 0
  | .F, .DFR => 2
  | .F, .DLF => 1
  | .F, .DBL => 0
  | .F, .DRB => 0
  | .B, .URF => 0
  | .B, .UFL => 0
  | .B, .ULB => 1
  | .B, .UBR => 2
  | .B, .DFR => 0
  | .B, .DLF => 0
  | .B, .DBL => 2
  | .B, .DRB => 1
  | .L, .URF => 0
  | .L, .UFL => 1
  | .L, .ULB => 2
  | .L, .UBR => 0
  | .L, .DFR => 0
  | .L, .DLF => 2
  | .L, .DBL => 1
  | .L, .DRB => 0
  | .R, .URF => 2
  | .R, .UFL => 0
  | .R, .ULB => 0
  | .R, .UBR => 1
  | .R, .DFR => 1
  | .R, .DLF => 0
  | .R, .DBL => 0
  | .R, .DRB => 2

/-- Where each edge goes under a clockwise quarter turn of a face. -/
def edgePerm : Face → Equiv.Perm Edge
  | .U => {
    toFun := fun
      | .UR => .UF
      | .UF => .UL
      | .UL => .UB
      | .UB => .UR
      | .DR => .DR
      | .DF => .DF
      | .DL => .DL
      | .DB => .DB
      | .FR => .FR
      | .FL => .FL
      | .BL => .BL
      | .BR => .BR
    invFun := fun
      | .UR => .UB
      | .UF => .UR
      | .UL => .UF
      | .UB => .UL
      | .DR => .DR
      | .DF => .DF
      | .DL => .DL
      | .DB => .DB
      | .FR => .FR
      | .FL => .FL
      | .BL => .BL
      | .BR => .BR
    left_inv := by intro a; cases a <;> rfl
    right_inv := by intro a; cases a <;> rfl }
  | .D => {
    toFun := fun
      | .UR => .UR
      | .UF => .UF
      | .UL => .UL
      | .UB => .UB
      | .DR => .DB
      | .DF => .DR
      | .DL => .DF
      | .DB => .DL
      | .FR => .FR
      | .FL => .FL
      | .BL => .BL
      | .BR => .BR
    invFun := fun
      | .UR => .UR
      | .UF => .UF
      | .UL => .UL
      | .UB => .UB
      | .DR => .DF
      | .DF => .DL
      | .DL => .DB
      | .DB => .DR
      | .FR => .FR
      | .FL => .FL
      | .BL => .BL
      | .BR => .BR
    left_inv := by intro a; cases a <;> rfl
    right_inv := by intro a; cases a <;> rfl }
  | .F => {
    toFun := fun
      | .UR => .UR
      | .UF => .FR
      | .UL => .UL
      | .UB => .UB
      | .DR => .DR
      | .DF => .FL
      | .DL => .DL
      | .DB => .DB
      | .FR => .DF
      | .FL => .UF
      | .BL => .BL
      | .BR => .BR
    invFun := fun
      | .UR => .UR
      | .UF => .FL
      | .UL => .UL
      | .UB => .UB
      | .DR => .DR
      | .DF => .FR
      | .DL => .DL
      | .DB => .DB
      | .FR => .UF
      | .FL => .DF
      | .BL => .BL
      | .BR => .BR
    left_inv := by intro a; cases a <;> rfl
    right_inv := by intro a; cases a <;> rfl }
  | .B => {
    toFun := fun
      | .UR => .UR
      | .UF => .UF
      | .UL => .UL
      | .UB => .BL
      | .DR => .DR
      | .DF => .DF
      | .DL => .DL
      | .DB => .BR
      | .FR => .FR
      | .FL => .FL
      | .BL => .DB
      | .BR => .UB
    invFun := fun
      | .UR => .UR
      | .UF => .UF
      | .UL => .UL
      | .UB => .BR
      | .DR => .DR
      | .DF => .DF
      | .DL => .DL
      | .DB => .BL
      | .FR => .FR
      | .FL => .FL
      | .BL => .UB
      | .BR => .DB
    left_inv := by intro a; cases a <;> rfl
    right_inv := by intro a; cases a <;> rfl }
  | .L => {
    toFun := fun
      | .UR => .UR
      | .UF => .UF
      | .UL => .FL
      | .UB => .UB
      | .DR => .DR
      | .DF => .DF
      | .DL => .BL
      | .DB => .DB
      | .FR => .FR
      | .FL => .DL
      | .BL => .UL
      | .BR => .BR
    invFun := fun
      | .UR => .UR
      | .UF => .UF
      | .UL => .BL
      | .UB => .UB
      | .DR => .DR
      | .DF => .DF
      | .DL => .FL
      | .DB => .DB
      | .FR => .FR
      | .FL => .UL
      | .BL => .DL
      | .BR => .BR
    left_inv := by intro a; cases a <;> rfl
    right_inv := by intro a; cases a <;> rfl }
  | .R => {
    toFun := fun
      | .UR => .BR
      | .UF => .UF
      | .UL => .UL
      | .UB => .UB
      | .DR => .FR
      | .DF => .DF
      | .DL => .DL
      | .DB => .DB
      | .FR => .UR
      | .FL => .FL
      | .BL => .BL
      | .BR => .DR
    invFun := fun
      | .UR => .FR
      | .UF => .UF
      | .UL => .UL
      | .UB => .UB
      | .DR => .BR
      | .DF => .DF
      | .DL => .DL
      | .DB => .DB
      | .FR => .DR
      | .FL => .FL
      | .BL => .BL
      | .BR => .UR
    left_inv := by intro a; cases a <;> rfl
    right_inv := by intro a; cases a <;> rfl }

/-- The flip each edge gains on arriving in its new slot, as an element of {lean}`ZMod 2`. -/
def edgeFlip : Face → Edge → ZMod 2
  | .U, _ => 0
  | .D, _ => 0
  | .F, .UR => 0
  | .F, .UF => 1
  | .F, .UL => 0
  | .F, .UB => 0
  | .F, .DR => 0
  | .F, .DF => 1
  | .F, .DL => 0
  | .F, .DB => 0
  | .F, .FR => 1
  | .F, .FL => 1
  | .F, .BL => 0
  | .F, .BR => 0
  | .B, .UR => 0
  | .B, .UF => 0
  | .B, .UL => 0
  | .B, .UB => 1
  | .B, .DR => 0
  | .B, .DF => 0
  | .B, .DL => 0
  | .B, .DB => 1
  | .B, .FR => 0
  | .B, .FL => 0
  | .B, .BL => 1
  | .B, .BR => 1
  | .L, _ => 0
  | .R, _ => 0

/-!
# The six generators

A quarter turn is the corner and edge tables put together. The twist tables are additive, in
{lean}`ZMod 3`, and {name}`Multiplicative.ofAdd` moves them into the multiplicative group that
{name}`OPerm` is built from.
-/

/-- The clockwise quarter turn of a face, as a cube state. -/
def move (f : Face) : Cube :=
  (⟨fun c => Multiplicative.ofAdd (cornerTwist f c), cornerPerm f⟩,
   ⟨fun e => Multiplicative.ofAdd (edgeFlip f e), edgePerm f⟩)

/--
Prove an equation between closed cube states slot by slot: split it into the four tables
(corner twists, corner permutation, edge flips, edge permutation) and evaluate each at every slot.
-/
macro "cube_eq" : tactic => `(tactic|
  (refine Prod.ext (SemidirectProduct.ext ?_ ?_) (SemidirectProduct.ext ?_ ?_) <;>
    first
      | (funext a; cases a <;> rfl)
      | (refine Equiv.ext fun a => ?_; cases a <;> rfl)))

/-- Four quarter turns of any face restore the cube. -/
theorem move_pow_four (f : Face) : move f ^ 4 = 1 := by
  cases f <;> cube_eq

/-!
Here is {lean}`move .U` applied to a solved cube. The up turn cycles four corners and four edges
and, under this convention, twists and flips nothing:

```cube
U
```

{lean}`move .R` also cycles four corners and four edges, but it twists the corners it moves, as
{name}`cornerTwist` records. The right face keeps its colour; the corner stickers that were facing
up or down now face sideways:

```cube
R
```

{lean}`move .F` additionally flips the four edges it moves, as {name}`edgeFlip` records. Four
turns of any face restore the cube, which is {name}`move_pow_four`:

```cube
F F F F
```

The states that can actually be reached are those built from face turns. In group-theoretic
terms they form the subgroup generated by the six quarter turns. Inverses come for free: the
inverse of a quarter turn is three more of the same.
-/

/-- The states reachable from the solved cube by turning faces. -/
def reachable : Subgroup Cube := Subgroup.closure (Set.range move)

/-- Every face turn is reachable. -/
theorem move_mem_reachable (f : Face) : move f ∈ reachable :=
  Subgroup.subset_closure ⟨f, rfl⟩

end Cubing.Cube3x3
