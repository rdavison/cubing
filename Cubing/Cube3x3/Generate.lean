module
public import Cubing.Cube3x3.Invariants
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Data.ZMod.Basic

set_option doc.verso true

/-!
To show that every valid state is reachable, it is enough to produce a few special states and
let group theory do the rest: a pure 3-cycle of pieces, and a pure twist of two pieces in
opposite directions. Combined with set-up moves, these solve any valid cube.

This chapter proves that principle once, for any finite type of slots and any number of
orientations. The next chapter applies it twice, to corners and to edges.
-/

@[expose] public section

namespace Cubing.Cube3x3

open Equiv SemidirectProduct

namespace OPerm

variable {α : Type} [Fintype α] [DecidableEq α] {n : ℕ}

/-!
# Set-up moves

3-cycles and twists are moved into position by conjugation: do a set-up, then the tool, then undo the set-up.
For pure twists the effect is especially simple. Twists commute with one another, so
conjugating a pure twist only relabels its slots.
-/

omit [Fintype α] in
/-- Relabelling a twist concentrated on one slot moves it to the image slot. -/
theorem mulAutArrow_mulSingle (σ : Perm α) (i : α) (c : Multiplicative (ZMod n)) :
    mulAutArrow σ (Pi.mulSingle i c) = Pi.mulSingle (σ i) c := by
  funext a
  change (Pi.mulSingle i c : α → Multiplicative (ZMod n)) (σ⁻¹ a) =
    (Pi.mulSingle (σ i) c : α → Multiplicative (ZMod n)) a
  simp only [Pi.mulSingle_apply, Perm.inv_eq_iff_eq]

omit [Fintype α] [DecidableEq α] in
/-- Conjugating a pure twist by any state relabels the twist by that state's permutation. -/
theorem conj_inl (l : OPerm α n) (o : α → Multiplicative (ZMod n)) :
    l * inl o * l⁻¹ = inl (mulAutArrow l.right o) := by
  ext a
  · simp [mul_comm]
  · simp

omit [Fintype α] in
/-- Any two distinct slots can be carried to any other two distinct slots. -/
theorem exists_perm_pair {i₀ j₀ i j : α} (h₀ : i₀ ≠ j₀) (h : i ≠ j) :
    ∃ σ : Perm α, σ i₀ = i ∧ σ j₀ = j := by
  set j₁ := swap i₀ i j₀
  have hj₁ : i ≠ j₁ := by
    intro e
    have := congrArg (swap i₀ i) e
    simp only [swap_apply_right, j₁, swap_apply_self] at this
    exact h₀ this
  refine ⟨swap j₁ j * swap i₀ i, ?_, ?_⟩
  · simp [swap_apply_of_ne_of_ne hj₁ h]
  · simp [j₁]

/-!
# Pure twists

The pure twists in a subgroup of states form a subgroup of orientation vectors. When the set-up moves realise every permutation, this subgroup is closed under
relabelling. Then one two-slot twist yields every two-slot twist, and two-slot twists generate
every orientation vector with total zero.
-/

/-- The two-slot twist turning slot {lean}`i` forward by one and slot {lean}`j` back by one. -/
def pairTwist (i j : α) : α → Multiplicative (ZMod n) :=
  Pi.mulSingle i (Multiplicative.ofAdd 1) * (Pi.mulSingle j (Multiplicative.ofAdd 1))⁻¹

/-- The orientation vectors whose pure twist lies in {lean}`K`. -/
def twists (K : Subgroup (OPerm α n)) : Subgroup (α → Multiplicative (ZMod n)) := K.comap inl

/-- Conjugation by {lean}`L` keeps {lean}`K`, and {lean}`L` realises every permutation. -/
structure SetUp (K L : Subgroup (OPerm α n)) : Prop where
  /-- Conjugating an element of {lean}`K` by an element of {lean}`L` stays in {lean}`K`. -/
  conj_mem : ∀ l ∈ L, ∀ k ∈ K, l * k * l⁻¹ ∈ K
  /-- Every permutation is the permutation of some element of {lean}`L`. -/
  surj : ∀ σ : Perm α, ∃ l ∈ L, l.right = σ

variable {K L : Subgroup (OPerm α n)}

omit [Fintype α] [DecidableEq α] in
/-- With full set-up moves, the pure twists in {lean}`K` are closed under relabelling. -/
theorem SetUp.relabel (hs : SetUp K L) (σ : Perm α) {o : α → Multiplicative (ZMod n)}
    (ho : o ∈ twists K) : mulAutArrow σ o ∈ twists K := by
  obtain ⟨l, hl, rfl⟩ := hs.surj σ
  change inl _ ∈ K
  rw [← conj_inl]
  exact hs.conj_mem l hl _ ho

omit [Fintype α] in
/-- One two-slot twist in {lean}`K` gives every two-slot twist. -/
theorem SetUp.pairTwist_mem (hs : SetUp K L) {i₀ j₀ : α} (h₀ : i₀ ≠ j₀)
    (hK : pairTwist i₀ j₀ ∈ twists K) (i j : α) : pairTwist i j ∈ twists K := by
  by_cases h : i = j
  · simp [h, pairTwist, (twists K).one_mem]
  obtain ⟨σ, rfl, rfl⟩ := exists_perm_pair h₀ h
  have := hs.relabel σ hK
  simpa [pairTwist, map_mul, map_inv, mulAutArrow_mulSingle] using this

/-- Every orientation vector with total zero is a product of two-slot twists. -/
theorem SetUp.mem_twists [NeZero n] (hs : SetUp K L) {i₀ j₀ : α} (h₀ : i₀ ≠ j₀)
    (hK : pairTwist i₀ j₀ ∈ twists K) (o : α → Multiplicative (ZMod n)) (ho : total o = 1) :
    o ∈ twists K := by
  have hpow (c : Multiplicative (ZMod n)) :
      c = Multiplicative.ofAdd 1 ^ (Multiplicative.toAdd c : ZMod n).val := by
    rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
  -- Each slot's twist is paired against slot `j₀`, which then carries the total, namely zero.
  have hdecomp : o = ∏ a, pairTwist a j₀ ^ (Multiplicative.toAdd (o a) : ZMod n).val := by
    have hsum : ∏ a, (Pi.mulSingle j₀ (o a) : α → Multiplicative (ZMod n)) = 1 := by
      have h := map_prod (MonoidHom.mulSingle (fun _ : α => Multiplicative (ZMod n)) j₀) o
        Finset.univ
      simp only [MonoidHom.mulSingle_apply] at h
      rw [← h]
      change (Pi.mulSingle j₀ (total o) : α → Multiplicative (ZMod n)) = 1
      rw [ho, Pi.mulSingle_one]
    conv_lhs => rw [← Finset.univ_prod_mulSingle o, ← mul_one (∏ a, _), ← inv_one, ← hsum,
      ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    set k := (Multiplicative.toAdd (o a) : ZMod n).val
    rw [show o a = Multiplicative.ofAdd 1 ^ k from hpow _, pairTwist, mul_pow, inv_pow,
      Pi.mulSingle_pow, Pi.mulSingle_pow]
  rw [hdecomp]
  exact Subgroup.prod_mem _ fun a _ => Subgroup.pow_mem _ (hs.pairTwist_mem h₀ hK a j₀) _

/-!
# Permutations

The permutations that {lean}`K` realises form a normal subgroup of all permutations, because
the set-up moves realise every permutation. All 3-cycles are conjugate. So one 3-cycle gives
them all, and 3-cycles generate the even permutations.
-/

/-- With full set-up moves, {lean}`K` realises every even permutation once it realises one
3-cycle. -/
theorem SetUp.alternating_le (hs : SetUp K L) {k : OPerm α n} (hk : k ∈ K)
    (h3 : k.right.IsThreeCycle) : alternatingGroup α ≤ K.map rightHom := by
  rw [← Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
  intro c hc
  obtain ⟨g, hg⟩ :=
    isConj_iff.mp (Perm.isConj_iff_cycleType_eq.mpr (h3.cycleType.trans hc.cycleType.symm))
  obtain ⟨l, hl, rfl⟩ := hs.surj g
  exact ⟨l * k * l⁻¹, hs.conj_mem l hl k hk, by simpa [rightHom_eq_right] using hg⟩

/-!
# Combining 3-cycles and twists

A state with total twist zero and an even permutation is reached in two steps. First realise
its permutation by some element of {lean}`K`. What is left over is a pure twist with total
zero.
-/

/--
**The generation lemma.** Suppose {lean}`K` is closed under set-up moves that realise every
permutation, contains a state permuting by a 3-cycle and a two-slot twist, and has total twist
zero throughout. Then {lean}`K` contains every state with total twist zero and an even
permutation.
-/
theorem SetUp.le [NeZero n] (hs : SetUp K L) (hK : K ≤ twistSum.ker)
    {k : OPerm α n} (hk : k ∈ K) (h3 : k.right.IsThreeCycle)
    {i₀ j₀ : α} (h₀ : i₀ ≠ j₀) (htw : pairTwist i₀ j₀ ∈ twists K) :
    twistSum.ker ⊓ (alternatingGroup α).comap rightHom ≤ K := by
  rintro x ⟨hx, hxa⟩
  obtain ⟨k', hk', hright⟩ := hs.alternating_le hk h3 hxa
  rw [rightHom_eq_right] at hright
  -- `x * k'⁻¹` permutes nothing, so it is the pure twist of its own orientation vector.
  have hpure : x * k'⁻¹ = inl (x * k'⁻¹).left := by
    ext a
    · rfl
    · simp [hright]
  have htot : total (x * k'⁻¹).left = 1 := by
    have h1 : twistSum (x * k'⁻¹) = 1 := by
      rw [map_mul, map_inv, MonoidHom.mem_ker.mp hx, MonoidHom.mem_ker.mp (hK hk'), inv_one,
        one_mul]
    rwa [hpure, twistSum_apply, left_inl] at h1
  have hmem : x * k'⁻¹ ∈ K := by
    rw [hpure]
    exact hs.mem_twists h₀ htw _ htot
  simpa using K.mul_mem hmem hk'

end OPerm

end Cubing.Cube3x3
