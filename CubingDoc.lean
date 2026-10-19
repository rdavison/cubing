module
public meta import Lean.Elab.DocString
meta import Init.Data.String.Legacy

open Lean Doc Elab

/-- Prefix that marks a code block as a cube picture on its way to the book. -/
public meta def cubeMarker : String := "\x01cube\n"

/-- The faces a Singmaster token can start with. -/
meta def validToken (s : String) : Bool :=
  match s.toList with
  | [f] | [f, '2'] | [f, '\''] => "UDFBLR".contains f
  | _ => false

namespace Cubing.Cube3x3

/-- A cube picture: a Singmaster sequence, drawn by the book from the model. -/
@[doc_code_block]
public meta def cube (code : StrLit) : DocM (Block ElabInline ElabBlock) := do
  let src := code.getString.trimAscii.copy
  for t in src.splitOn " " do
    unless t.isEmpty || validToken t do
      throwErrorAt code "not a Singmaster move: {t}"
  return .code (cubeMarker ++ src)

end Cubing.Cube3x3
