module

/-!
Executable code. Imports no Mathlib, so it can be precompiled; its correctness proofs live in
`Cubing`.
-/

@[expose] public section

namespace CubingImpl

def double (n : Nat) : Nat := n + n

end CubingImpl
