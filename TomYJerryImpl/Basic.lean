module

/-!
Executable code. Imports no Mathlib, so it can be precompiled; its correctness proofs live in
`TomYJerry`.
-/

@[expose] public section

namespace TomYJerryImpl

def double (n : Nat) : Nat := n + n

end TomYJerryImpl
