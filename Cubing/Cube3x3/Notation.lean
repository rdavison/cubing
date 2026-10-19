module
public import Cubing.Cube3x3.Moves
meta import CubingDoc

set_option doc.verso true

/-!
Cubers write move sequences in Singmaster notation. A face letter alone is a clockwise quarter
turn, a trailing prime is anticlockwise, and a trailing two is a half turn. A sequence is read
left to right, so {lit}`R U R' U'` turns R first. This chapter gives the notation a meaning and
proves that it composes the way cubers expect.
-/

@[expose] public section

namespace Cubing.Cube3x3

/-- How far a face is turned. -/
inductive Turn where
  /-- A clockwise quarter turn, written with the bare face letter. -/ | cw
  /-- A half turn, written with a trailing {lit}`2`. -/ | half
  /-- An anticlockwise quarter turn, written with a trailing prime. -/ | ccw
  deriving DecidableEq, Fintype, Repr, Inhabited

/-- The number of clockwise quarter turns a {name}`Turn` amounts to. -/
def Turn.quarters : Turn → ℕ
  | .cw => 1
  | .half => 2
  | .ccw => 3

/-- A single move in Singmaster notation: a face and how far to turn it. -/
structure Move where
  /-- The face that turns. -/
  face : Face
  /-- How far it turns. -/
  turn : Turn
  deriving DecidableEq, Fintype, Repr, Inhabited

/-- The cube state a single move produces. -/
def Move.toCube (m : Move) : Cube := move m.face ^ m.turn.quarters

/-!
A bare letter is a clockwise quarter turn, a prime undoes it and a two is a half turn:

```cube
R
```

```cube
R'
```

```cube
R2
```
-/

/-!
# Sequences

A sequence of moves is applied left to right. Each new move multiplies on the *left*, because
the product of two states performs its right factor first.
-/

/-- The cube state a sequence of moves produces, applying the moves left to right. -/
def alg (ms : List Move) : Cube := ms.foldl (fun acc m => m.toCube * acc) 1

private theorem foldl_mul (ms : List Move) (x : Cube) :
    ms.foldl (fun acc m => m.toCube * acc) x = alg ms * x := by
  induction ms generalizing x with
  | nil => simp [alg]
  | cons m ms ih =>
    simp only [List.foldl_cons, alg]
    rw [ih, ih (m.toCube * 1), mul_one, mul_assoc]

/-- The empty sequence does nothing. -/
@[simp] theorem alg_nil : alg [] = 1 := rfl

/-- A sequence starting with {lean}`m` performs {lean}`m` first, so it is the rest of the
sequence composed after {lean}`m`. -/
@[simp] theorem alg_cons (m : Move) (ms : List Move) : alg (m :: ms) = alg ms * m.toCube := by
  simp only [alg, List.foldl_cons, mul_one]
  exact foldl_mul ms m.toCube

/-- Doing one sequence and then another: the second is composed after the first. -/
theorem alg_append (xs ys : List Move) : alg (xs ++ ys) = alg ys * alg xs := by
  simp only [alg, List.foldl_append]
  exact foldl_mul ys _

/-!
Order matters. {lean}`alg [⟨.R, .cw⟩, ⟨.U, .cw⟩]` turns R first and then U, which gives a different
state from U first and then R. Step through both:

```cube
R U
```

```cube
U R
```

Longer sequences give the familiar algorithms. Repeating the four moves {lit}`R U R' U'` six times
restores the cube, which is proved at the end of this chapter:

```cube
R U R' U'
```

Every sequence is a reachable state, since each move is a power of a face turn.
-/

/-- Every move sequence produces a reachable state. -/
theorem alg_mem_reachable (ms : List Move) : alg ms ∈ reachable := by
  induction ms with
  | nil => exact reachable.one_mem
  | cons m ms ih =>
    rw [alg_cons]
    exact reachable.mul_mem ih (reachable.pow_mem (move_mem_reachable m.face) _)

/-!
# Writing sequences

The term {lit}`cube[R U R' U']` is the state that sequence produces. Primes and twos are part of
the identifiers {lit}`R'` and {lit}`R2`, so the notation is checked when it is elaborated. An
unknown move is an error, not a silent no-op.
-/

/-- The {name}`Move` named by the characters of a Singmaster token, if any. -/
def Move.ofChars? : List Char → Option Move
  | [f] => face? f |>.map (⟨·, .cw⟩)
  | [f, '2'] => face? f |>.map (⟨·, .half⟩)
  | [f, '\''] => face? f |>.map (⟨·, .ccw⟩)
  | _ => none
where
  /-- The face named by a letter. -/
  face? : Char → Option Face
    | 'U' => some .U | 'D' => some .D | 'F' => some .F
    | 'B' => some .B | 'L' => some .L | 'R' => some .R
    | _ => none

/-- The characters of the Singmaster token of a {name}`Move`. -/
def Move.toChars (m : Move) : List Char :=
  let f := match m.face with
    | .U => 'U' | .D => 'D' | .F => 'F' | .B => 'B' | .L => 'L' | .R => 'R'
  match m.turn with
    | .cw => [f] | .half => [f, '2'] | .ccw => [f, '\'']

/-- The {name}`Move` named by a Singmaster token, if any. -/
def Move.ofToken? (s : String) : Option Move := Move.ofChars? s.toList

/-- The Singmaster token of a {name}`Move`. -/
def Move.toToken (m : Move) : String := String.ofList m.toChars

/-- Reading back a rendered move recovers it. -/
theorem Move.ofToken?_toToken (m : Move) : Move.ofToken? m.toToken = some m := by
  obtain ⟨f, t⟩ := m
  simp only [Move.ofToken?, Move.toToken, String.toList_ofList]
  cases f <;> cases t <;> rfl

/-- Reading a sequence of Singmaster tokens separated by spaces. -/
def parseAlg? (s : String) : Option (List Move) :=
  (s.splitOn " ").filter (· ≠ "") |>.mapM Move.ofToken?

/-- Writing a sequence back as Singmaster tokens. -/
def renderAlg (ms : List Move) : String := " ".intercalate (ms.map Move.toToken)

/--
The constructor names of the face and turn a Singmaster token denotes. Macros may only call
compile-time code, so this mirrors {name}`Move.ofToken?`; the theorem
{name}`Move.ofToken?_toToken` checks the runtime side.
-/
meta def tokenNames? (s : String) : Option (String × String) := do
  let f ← match s.front with
    | 'U' => some "U" | 'D' => some "D" | 'F' => some "F"
    | 'B' => some "B" | 'L' => some "L" | 'R' => some "R"
    | _ => none
  let t ← match (s.drop 1).toString with
    | "" => some "cw" | "2" => some "half" | "'" => some "ccw"
    | _ => none
  if s.isEmpty then none else some (f, t)

/-- Elaborates {lit}`cube[R U R' U']` to the state that sequence of moves produces. -/
syntax "cube[" ident* "]" : term

macro_rules
  | `(cube[$ms*]) => do
    let moves ← ms.mapM fun m => do
      let some (f, t) := tokenNames? m.getId.toString
        | Lean.Macro.throwErrorAt m s!"not a Singmaster move: {m.getId}"
      `(Cubing.Cube3x3.Move.mk $(Lean.mkIdent (.str `Cubing.Cube3x3.Face f))
          $(Lean.mkIdent (.str `Cubing.Cube3x3.Turn t)))
    `(Cubing.Cube3x3.alg [$moves,*])

/-!
The notation agrees with the product order fixed in the first chapter: {lit}`R U` is the U turn
composed after the R turn.
-/

/-- Cubers' left-to-right sequences are group products read right to left. -/
example : cube[R U] = move .U * move .R := by
  simp [Move.toCube, Turn.quarters]

/-!
# Checking the tables against known facts

The move tables were typed in from the standard computer-cubing tables. Three known facts check
them: the commutator {lit}`R U R' U'` restores the cube after six repetitions,
{lit}`R U` after 105, and the T-perm after two. A wrong entry anywhere in the R, U or F tables
would break at least one of these.
-/

set_option maxRecDepth 100000 in
/-- Six repetitions of {lit}`R U R' U'` restore the cube. -/
theorem commutatorRU_pow_six : cube[R U R' U'] ^ 6 = 1 := by cube_eq

set_option maxRecDepth 100000 in
/-- {lit}`R U` repeated 105 times restores the cube. -/
theorem RU_pow_105 : cube[R U] ^ 105 = 1 := by cube_eq

set_option maxRecDepth 100000 in
/-- The T-perm is its own inverse. -/
theorem tPerm_sq : cube[R U R' U' R' F R2 U' R' U' R U R' F'] ^ 2 = 1 := by cube_eq

end Cubing.Cube3x3
