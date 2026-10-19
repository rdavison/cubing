import Cubing

open Cubing.Cube3x3

def main : IO Unit := do
  let g := cube[R U R' U']
  for f in [Face.U, .R, .F, .D, .L, .B] do
    let row := (List.finRange 9).map fun i => reprStr (colors g (netFacelet f i))
    IO.println s!"{reprStr f}: {String.intercalate " " row}"
