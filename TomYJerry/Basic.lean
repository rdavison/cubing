module
public import Mathlib.Data.Nat.Basic
public import TomYJerryImpl

@[expose] public section

namespace TomYJerry

/-- `TomYJerryImpl.double` computes `2 * n`. -/
theorem double_eq (n : Nat) : TomYJerryImpl.double n = 2 * n := by
  unfold TomYJerryImpl.double; omega

end TomYJerry
