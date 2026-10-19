module
public import Cubing.Cube3x3.Notation
meta import CubingDoc
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Tactic.NormNum
public import Mathlib.Data.Fintype.Units
public import Mathlib.Data.Finite.Perm
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

set_option doc.verso true

/-!
Not every arrangement of the pieces can be reached by turning faces. A cuber learns three
obstructions, usually the hard way, after reassembling a cube wrongly:

* the corner twists always add up to a multiple of three;
* the edge flips always add up to a multiple of two;
* the corner permutation and the edge permutation are both even or both odd.

This chapter defines the three quantities as group homomorphisms and proves that every face turn
leaves them unchanged. Every reachable state therefore satisfies all three. The next chapters
prove the converse.
-/

@[expose] public section

namespace Cubing.Cube3x3

open Equiv

namespace OPerm

variable {α : Type} [Fintype α] {n : ℕ}

/-- The product of an orientation vector's entries, that is, its total twist. -/
def total : (α → Multiplicative (ZMod n)) →* Multiplicative (ZMod n) where
  toFun o := ∏ a, o a
  map_one' := by simp
  map_mul' _ _ := Finset.prod_mul_distrib

/-- Relabelling the slots does not change the total twist. -/
theorem total_mulAutArrow (σ : Perm α) (o : α → Multiplicative (ZMod n)) :
    total (mulAutArrow σ o) = total o := by
  simp only [total, MonoidHom.coe_mk, OneHom.coe_mk, mulAutArrow_apply_apply]
  exact Equiv.prod_comp σ⁻¹ o

/--
The total twist of a state, as a homomorphism. The total of a product is the product of the
totals, because a permutation only relabels the slots it carries twists between.
-/
def twistSum : OPerm α n →* Multiplicative (ZMod n) :=
  SemidirectProduct.lift total 1 fun σ => by
    ext o
    simp [total_mulAutArrow]

/-- The total twist of a state is the total of its orientation vector. -/
theorem twistSum_apply (g : OPerm α n) : twistSum g = ∏ a, g.left a :=
  mul_one _

/-- The sign of a state's permutation. -/
def parity [DecidableEq α] : OPerm α n →* ℤˣ := Perm.sign.comp SemidirectProduct.rightHom

end OPerm

open OPerm

/-!
# The three invariants together

On the whole cube the two parities are multiplied, since only their agreement is preserved.
-/

/-- The invariants of a cube state: the product of the corner and edge parities, the total
corner twist, and the total edge flip. -/
def invariants : Cube →* ℤˣ × Multiplicative (ZMod 3) × Multiplicative (ZMod 2) :=
  (parity.comp (MonoidHom.fst _ _) * parity.comp (MonoidHom.snd _ _)).prod
    ((twistSum.comp (MonoidHom.fst _ _)).prod (twistSum.comp (MonoidHom.snd _ _)))

/-- The valid states: those whose invariants are all trivial. -/
def valid : Subgroup Cube := invariants.ker

/-- A state is valid exactly when its parities agree, its corner twists sum to zero, and its
edge flips sum to zero. -/
theorem mem_valid (g : Cube) :
    g ∈ valid ↔ parity g.1 = parity g.2 ∧ twistSum g.1 = 1 ∧ twistSum g.2 = 1 := by
  simp only [valid, MonoidHom.mem_ker, invariants, MonoidHom.prod_apply, MonoidHom.mul_apply,
    MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd,
    Prod.mk_eq_one]
  constructor
  · rintro ⟨h, h1, h2⟩
    refine ⟨?_, h1, h2⟩
    rw [eq_inv_of_mul_eq_one_left h, Int.units_inv_eq_self]
  · rintro ⟨h, h1, h2⟩
    exact ⟨by rw [h, Int.units_mul_self], h1, h2⟩

/-!
# Every face turn is valid

Each face turn moves four corners round a 4-cycle and four edges round a 4-cycle. A 4-cycle is a
product of three transpositions, so both parities are odd and they agree.
-/

private theorem sign_cycle4 {β : Type} [Fintype β] [DecidableEq β] {a b c d : β}
    (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) :
    Perm.sign (swap a b * swap b c * swap c d) = -1 := by
  simp [Perm.sign_swap hab, Perm.sign_swap hbc, Perm.sign_swap hcd]

/-- Each face turn moves its four corners round a 4-cycle, a product of three transpositions. -/
theorem cornerPerm_eq (f : Face) : ∃ a b c d : Corner, a ≠ b ∧ b ≠ c ∧ c ≠ d ∧
    cornerPerm f = swap a b * swap b c * swap c d := by
  cases f
  · exact ⟨.URF, .UFL, .ULB, .UBR, by decide, by decide, by decide,
      Equiv.ext fun x => by cases x <;> rfl⟩
  · exact ⟨.DFR, .DRB, .DBL, .DLF, by decide, by decide, by decide,
      Equiv.ext fun x => by cases x <;> rfl⟩
  · exact ⟨.URF, .DFR, .DLF, .UFL, by decide, by decide, by decide,
      Equiv.ext fun x => by cases x <;> rfl⟩
  · exact ⟨.ULB, .DBL, .DRB, .UBR, by decide, by decide, by decide,
      Equiv.ext fun x => by cases x <;> rfl⟩
  · exact ⟨.UFL, .DLF, .DBL, .ULB, by decide, by decide, by decide,
      Equiv.ext fun x => by cases x <;> rfl⟩
  · exact ⟨.URF, .UBR, .DRB, .DFR, by decide, by decide, by decide,
      Equiv.ext fun x => by cases x <;> rfl⟩

/-- Each face turn moves its four edges round a 4-cycle, a product of three transpositions. -/
theorem edgePerm_eq (f : Face) : ∃ a b c d : Edge, a ≠ b ∧ b ≠ c ∧ c ≠ d ∧
    edgePerm f = swap a b * swap b c * swap c d := by
  cases f
  · exact ⟨.UR, .UF, .UL, .UB, by decide, by decide, by decide,
      Equiv.ext fun x => by cases x <;> rfl⟩
  · exact ⟨.DR, .DB, .DL, .DF, by decide, by decide, by decide,
      Equiv.ext fun x => by cases x <;> rfl⟩
  · exact ⟨.UF, .FR, .DF, .FL, by decide, by decide, by decide,
      Equiv.ext fun x => by cases x <;> rfl⟩
  · exact ⟨.UB, .BL, .DB, .BR, by decide, by decide, by decide,
      Equiv.ext fun x => by cases x <;> rfl⟩
  · exact ⟨.UL, .FL, .DL, .BL, by decide, by decide, by decide,
      Equiv.ext fun x => by cases x <;> rfl⟩
  · exact ⟨.UR, .BR, .DR, .FR, by decide, by decide, by decide,
      Equiv.ext fun x => by cases x <;> rfl⟩

/-- Every face turn is an odd permutation of the corners. -/
theorem parity_move_fst (f : Face) : parity (move f).1 = -1 := by
  obtain ⟨a, b, c, d, hab, hbc, hcd, h⟩ := cornerPerm_eq f
  simp only [parity, MonoidHom.coe_comp, Function.comp_apply, SemidirectProduct.rightHom_eq_right,
    move, h]
  exact sign_cycle4 hab hbc hcd

/-- Every face turn is an odd permutation of the edges. -/
theorem parity_move_snd (f : Face) : parity (move f).2 = -1 := by
  obtain ⟨a, b, c, d, hab, hbc, hcd, h⟩ := edgePerm_eq f
  simp only [parity, MonoidHom.coe_comp, Function.comp_apply, SemidirectProduct.rightHom_eq_right,
    move, h]
  exact sign_cycle4 hab hbc hcd

/-- Every face turn twists the corners by a total of zero. -/
theorem twistSum_move_fst (f : Face) : twistSum (move f).1 = 1 := by
  rw [twistSum_apply]
  cases f <;> decide +kernel

/-- Every face turn flips the edges by a total of zero. -/
theorem twistSum_move_snd (f : Face) : twistSum (move f).2 = 1 := by
  rw [twistSum_apply]
  cases f <;> decide +kernel

/-- Every face turn is a valid state. -/
theorem move_mem_valid (f : Face) : move f ∈ valid := by
  rw [mem_valid, parity_move_fst, parity_move_snd]
  exact ⟨rfl, twistSum_move_fst f, twistSum_move_snd f⟩

/-!
Turning a face moves pieces but keeps all three totals. Longer sequences can reorient corners
considerably, yet the twists they leave always add up to a multiple of three, because the total
is a homomorphism ({name}`twistSum`) that is trivial on every generator. The Sune is a familiar
example:

```cube
R U R' U R U2 R'
```

Likewise {lean}`move .F` flips four edges, an even number, so the flip total stays a multiple of
two:

```cube
F
```

Since the valid states form a subgroup containing every generator, they contain everything the
generators produce.
-/

/-- Every reachable state is valid. -/
theorem reachable_le_valid : reachable ≤ valid :=
  (Subgroup.closure_le _).mpr <| by
    rintro _ ⟨f, rfl⟩
    exact move_mem_valid f

/-!
# Counting

Without the invariants there are {lean}`3 ^ 8 * Nat.factorial 8 * 2 ^ 12 * Nat.factorial 12`
states: a twist for every corner, an arrangement of the corners, a flip for every edge, and an
arrangement of the edges. Mathlib counts each factor: {name}`SemidirectProduct.card`,
{name}`Nat.card_fun`, {name}`Nat.card_perm`.
-/

/-- The number of cube states, valid or not. -/
theorem card_cube :
    Nat.card Cube = 3 ^ 8 * Nat.factorial 8 * 2 ^ 12 * Nat.factorial 12 := by
  have hc : Nat.card Corner = 8 := by rw [Nat.card_eq_fintype_card]; rfl
  have he : Nat.card Edge = 12 := by rw [Nat.card_eq_fintype_card]; rfl
  have hm (k : ℕ) : Nat.card (Multiplicative (ZMod k)) = k :=
    (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod k)
  rw [Nat.card_prod, SemidirectProduct.card, SemidirectProduct.card, Nat.card_fun, Nat.card_fun,
    Nat.card_perm, Nat.card_perm, hc, he, hm, hm, ← mul_assoc]

/-!
The invariants take every one of their {lean}`2 * 3 * 2` possible values. Twisting a single
corner, flipping a single edge, or swapping two corners alone changes exactly one invariant.
-/

/-- A corner state twisting one corner by {lean}`a` and permuting by {lean}`σ`. -/
private def cornerWith (a : ZMod 3) (σ : Perm Corner) : CornerGroup :=
  ⟨Pi.mulSingle .URF (Multiplicative.ofAdd a), σ⟩

/-- Every combination of invariants occurs. -/
theorem invariants_surjective : Function.Surjective invariants := by
  rintro ⟨s, a, b⟩
  obtain rfl | rfl := Int.units_eq_one_or s
  · refine ⟨(cornerWith a.toAdd 1, ⟨Pi.mulSingle .UR b, 1⟩), ?_⟩
    simp [invariants, cornerWith, parity, twistSum_apply, Finset.prod_pi_mulSingle']
  · refine ⟨(cornerWith a.toAdd (swap .URF .UFL), ⟨Pi.mulSingle .UR b, 1⟩), ?_⟩
    simp [invariants, cornerWith, parity, twistSum_apply, Finset.prod_pi_mulSingle',
      Perm.sign_swap (show Corner.URF ≠ .UFL by decide)]

/-- There are twelve combinations of invariants, so a twelfth of all states is valid. -/
theorem index_valid : valid.index = 12 := by
  rw [valid, Subgroup.index_ker, MonoidHom.range_eq_top.mpr invariants_surjective,
    Subgroup.card_top, Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card (α := ℤˣ),
    Nat.card_congr (Multiplicative.toAdd (α := ZMod 3)),
    Nat.card_congr (Multiplicative.toAdd (α := ZMod 2)), Nat.card_zmod, Nat.card_zmod,
    Fintype.card_units_int]

/-- The number of valid cube states. -/
theorem card_valid : Nat.card valid = 43252003274489856000 := by
  have h := valid.card_mul_index
  rw [index_valid, card_cube] at h
  norm_num [Nat.factorial] at h
  omega

end Cubing.Cube3x3
