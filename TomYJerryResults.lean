import TomYJerry

/-!
# Results that rely on native evaluation

The only place `native_decide` is allowed. Its axioms are pinned below. Not a default target.
-/

theorem double_21 : TomYJerryImpl.double 21 = 42 := by
  native_decide
