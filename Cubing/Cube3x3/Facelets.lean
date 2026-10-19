module
public import Cubing.Cube3x3.Notation
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.Tactic.Abel

set_option doc.verso true

/-!
A cube in the hand is not a pair of permutations. It is 54 coloured stickers. This chapter
connects the two views. The forty-eight stickers that move are exactly the pairs of a piece and
one of its orientations. A state acts on them faithfully, so it is determined by where it sends
the stickers. The same action colours the familiar unfolded net, which is how the book draws
cubes.
-/

@[expose] public section

namespace Cubing.Cube3x3

open Equiv

namespace OPerm

variable {α : Type} {n : ℕ}

/-!
# States act on stickers

A sticker of a piece type is a slot together with an orientation. A state carries the sticker
of the piece in slot {lit}`a` at orientation {lit}`t` to its new slot, adding the twist that piece gains.
-/

/-- A state moves stickers: the piece's slot is permuted and its twist is added. -/
instance : MulAction (OPerm α n) (α × ZMod n) where
  smul g p := (g.right p.1, p.2 + Multiplicative.toAdd (g.left (g.right p.1)))
  one_smul p := by
    change ((1 : Perm α) p.1, p.2 + Multiplicative.toAdd (1 : Multiplicative (ZMod n))) = p
    simp
  mul_smul g h p := by
    change ((g * h).right p.1, p.2 + Multiplicative.toAdd ((g * h).left ((g * h).right p.1))) =
      (g.right (h.right p.1), p.2 + Multiplicative.toAdd (h.left (h.right p.1)) +
        Multiplicative.toAdd (g.left (g.right (h.right p.1))))
    simp only [OPerm.mul_right, OPerm.mul_left_apply, Perm.mul_apply, Perm.inv_def, Equiv.symm_apply_apply,
      toAdd_mul]
    ext
    · rfl
    · change _ = _
      abel_nf

/-- How a state moves a sticker. -/
theorem smul_def (g : OPerm α n) (a : α) (t : ZMod n) :
    g • (a, t) = (g.right a, t + Multiplicative.toAdd (g.left (g.right a))) := rfl

/-- Undoing a state on a sticker: back to the slot it came from, removing the twist. -/
theorem inv_smul (g : OPerm α n) (a : α) (t : ZMod n) :
    g⁻¹ • (a, t) = (g.right⁻¹ a, t - Multiplicative.toAdd (g.left a)) := by
  rw [inv_smul_eq_iff, smul_def]
  simp

/-- A state is determined by how it moves the stickers. -/
instance : FaithfulSMul (OPerm α n) (α × ZMod n) where
  eq_of_smul_eq_smul {g h} H := by
    have hr : g.right = h.right := Equiv.ext fun a => congrArg Prod.fst (H (a, 0))
    have hl (a : α) : g.left (g.right a) = h.left (h.right a) := by
      have := congrArg Prod.snd (H (a, 0))
      simpa [smul_def] using this
    ext a
    · simpa [hr] using hl (h.right⁻¹ a)
    · rw [hr]

end OPerm

open OPerm

/-- The forty-eight moving stickers: corner stickers and edge stickers. -/
abbrev Sticker := (Corner × ZMod 3) ⊕ (Edge × ZMod 2)

/-- A cube state as a permutation of the moving stickers. -/
def toStickers : Cube →* Perm Sticker :=
  (Perm.sumCongrHom _ _).comp
    ((MulAction.toPermHom CornerGroup (Corner × ZMod 3)).prodMap
      (MulAction.toPermHom EdgeGroup (Edge × ZMod 2)))

/-- Different states move the stickers differently: the cubie model loses nothing. -/
theorem toStickers_injective : Function.Injective toStickers :=
  Perm.sumCongrHom_injective.comp
    (MulAction.toPerm_injective.prodMap MulAction.toPerm_injective)

/-!
# Colouring the net

The unfolded net shows all 54 facelets: six fixed centres and the forty-eight moving stickers.
To colour a facelet, find the sticker that has arrived there and paint it the colour of its
home face. The tables below give each piece's stickers and the place of each facelet on the net,
following the standard numbering used by computer solvers.
-/

/-- A facelet of the cube's surface: a centre, or a sticker position of a corner or edge slot. -/
inductive Facelet where
  /-- The centre of a face. -/ | centre (f : Face)
  /-- The sticker of corner slot {lean}`c` at orientation {lean}`k`. -/ | corner (c : Corner) (k : ZMod 3)
  /-- The sticker of edge slot {lean}`e` at orientation {lean}`k`. -/ | edge (e : Edge) (k : ZMod 2)
  deriving DecidableEq

/-- The faces of a corner's three stickers, in orientation order: the up or down sticker
first, then clockwise. -/
def cornerStickers : Corner → Face × Face × Face
  | .URF => (.U, .R, .F)
  | .UFL => (.U, .F, .L)
  | .ULB => (.U, .L, .B)
  | .UBR => (.U, .B, .R)
  | .DFR => (.D, .F, .R)
  | .DLF => (.D, .L, .F)
  | .DBL => (.D, .B, .L)
  | .DRB => (.D, .R, .B)

/-- The faces of an edge's two stickers, in orientation order. -/
def edgeStickers : Edge → Face × Face
  | .UR => (.U, .R)
  | .UF => (.U, .F)
  | .UL => (.U, .L)
  | .UB => (.U, .B)
  | .DR => (.D, .R)
  | .DF => (.D, .F)
  | .DL => (.D, .L)
  | .DB => (.D, .B)
  | .FR => (.F, .R)
  | .FL => (.F, .L)
  | .BL => (.B, .L)
  | .BR => (.B, .R)

/-- The facelet at each position of the net. Each face's nine positions are numbered row by
row, as seen looking straight at that face from outside the cube. -/
def netFacelet : Face → Fin 9 → Facelet
  | .U, 0 => .corner .ULB 0
  | .U, 1 => .edge .UB 0
  | .U, 2 => .corner .UBR 0
  | .U, 3 => .edge .UL 0
  | .U, 4 => .centre .U
  | .U, 5 => .edge .UR 0
  | .U, 6 => .corner .UFL 0
  | .U, 7 => .edge .UF 0
  | .U, 8 => .corner .URF 0
  | .R, 0 => .corner .URF 1
  | .R, 1 => .edge .UR 1
  | .R, 2 => .corner .UBR 2
  | .R, 3 => .edge .FR 1
  | .R, 4 => .centre .R
  | .R, 5 => .edge .BR 1
  | .R, 6 => .corner .DFR 2
  | .R, 7 => .edge .DR 1
  | .R, 8 => .corner .DRB 1
  | .F, 0 => .corner .UFL 1
  | .F, 1 => .edge .UF 1
  | .F, 2 => .corner .URF 2
  | .F, 3 => .edge .FL 0
  | .F, 4 => .centre .F
  | .F, 5 => .edge .FR 0
  | .F, 6 => .corner .DLF 2
  | .F, 7 => .edge .DF 1
  | .F, 8 => .corner .DFR 1
  | .D, 0 => .corner .DLF 0
  | .D, 1 => .edge .DF 0
  | .D, 2 => .corner .DFR 0
  | .D, 3 => .edge .DL 0
  | .D, 4 => .centre .D
  | .D, 5 => .edge .DR 0
  | .D, 6 => .corner .DBL 0
  | .D, 7 => .edge .DB 0
  | .D, 8 => .corner .DRB 0
  | .L, 0 => .corner .ULB 1
  | .L, 1 => .edge .UL 1
  | .L, 2 => .corner .UFL 2
  | .L, 3 => .edge .BL 1
  | .L, 4 => .centre .L
  | .L, 5 => .edge .FL 1
  | .L, 6 => .corner .DBL 2
  | .L, 7 => .edge .DL 1
  | .L, 8 => .corner .DLF 1
  | .B, 0 => .corner .UBR 1
  | .B, 1 => .edge .UB 1
  | .B, 2 => .corner .ULB 2
  | .B, 3 => .edge .BR 0
  | .B, 4 => .centre .B
  | .B, 5 => .edge .BL 0
  | .B, 6 => .corner .DRB 2
  | .B, 7 => .edge .DB 1
  | .B, 8 => .corner .DBL 1

/-- The home face of a corner sticker. -/
def cornerFace (c : Corner) (k : ZMod 3) : Face :=
  if k = 0 then (cornerStickers c).1 else if k = 1 then (cornerStickers c).2.1
  else (cornerStickers c).2.2

/-- The home face of an edge sticker. -/
def edgeFace (e : Edge) (k : ZMod 2) : Face :=
  if k = 0 then (edgeStickers e).1 else (edgeStickers e).2

/-- The home face of a moving sticker, which is its colour. -/
def Sticker.face : Sticker → Face
  | .inl (c, k) => cornerFace c k
  | .inr (e, k) => edgeFace e k

/-- The colour showing at each facelet in a given state. -/
def colors (g : Cube) : Facelet → Face
  | .centre f => f
  | .corner c k => cornerFace (g.1.right⁻¹ c) (k - Multiplicative.toAdd (g.1.left c))
  | .edge e k => edgeFace (g.2.right⁻¹ e) (k - Multiplicative.toAdd (g.2.left e))

/-!
The colouring is not a separate model. At every sticker position it shows the colour of the
sticker that the state has carried there.
-/

/-- At a corner sticker position, the colour is that of the sticker carried there. -/
theorem colors_corner (g : Cube) (c : Corner) (k : ZMod 3) :
    colors g (.corner c k) = Sticker.face ((toStickers g)⁻¹ (.inl (c, k))) := by
  simp [colors, toStickers, Sticker.face, Perm.sumCongr_inv, inv_smul]

/-- At an edge sticker position, the colour is that of the sticker carried there. -/
theorem colors_edge (g : Cube) (e : Edge) (k : ZMod 2) :
    colors g (.edge e k) = Sticker.face ((toStickers g)⁻¹ (.inr (e, k))) := by
  simp [colors, toStickers, Sticker.face, Perm.sumCongr_inv, inv_smul]

/-- On the solved cube, every face of the net shows a single colour. -/
theorem colors_one_net (f : Face) (i : Fin 9) : colors 1 (netFacelet f i) = f := by
  revert f i; decide

end Cubing.Cube3x3
