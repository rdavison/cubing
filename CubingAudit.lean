import Cubing

/-!
# Axiom audit

Each headline theorem's axioms are pinned with `#guard_msgs`, so a new dependency such as
`sorryAx`, a custom axiom, or native evaluation fails the build instead of passing silently.

This is its own non-module library because `#print axioms` cannot be used inside a `module`. It is
a default target, so `lake build` enforces it.
-/

/-- info: 'Cubing.Cube3x3.reachable_eq_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cubing.Cube3x3.reachable_eq_valid

/-- info: 'Cubing.Cube3x3.card_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cubing.Cube3x3.card_reachable

/-- info: 'Cubing.Cube3x3.card_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cubing.Cube3x3.card_valid

/-- info: 'Cubing.Cube3x3.toStickers_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cubing.Cube3x3.toStickers_injective

/-- info: 'Cubing.Cube3x3.colors_corner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cubing.Cube3x3.colors_corner

/-- info: 'Cubing.Cube3x3.colors_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cubing.Cube3x3.colors_edge

/-- info: 'Cubing.Cube3x3.Facelet.cubie_normal_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cubing.Cube3x3.Facelet.cubie_normal_injective

/-- info: 'Cubing.Cube3x3.colors_move_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cubing.Cube3x3.colors_move_mul
