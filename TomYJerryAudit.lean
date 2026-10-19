import TomYJerry

/-!
# Axiom audit

Each headline theorem's axioms are pinned with `#guard_msgs`, so a new dependency such as
`sorryAx`, a custom axiom, or native evaluation fails the build instead of passing silently.

This is its own non-module library because `#print axioms` cannot be used inside a `module`. It is
a default target, so `lake build` enforces it.
-/

/-- info: 'TomYJerry.double_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TomYJerry.double_eq
