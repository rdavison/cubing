import VersoManual
import CubingSite.Widget

/-!
Chapters are whole library modules, included literately. Every inclusion is recorded so that
`checkCoverage` can fail the build when a module under `../Cubing` is left out of the book.
-/

open Lean Elab Term
open Lean.Doc.Syntax
open Verso Doc Elab
open Verso.ArgParse
open Verso.Genre Manual
open PartElabM

namespace CubingSite

/-- Library modules included so far, in this elaboration. -/
initialize includedChapters : IO.Ref NameSet ← IO.mkRef {}

/-- Arguments of `{chapter Module "Title"}`. -/
structure ChapterConfig where
  modName : Ident
  title : StrLit

instance [Monad m] [MonadError m] [MonadLiftT CoreM m] : FromArgs ChapterConfig m where
  fromArgs := ChapterConfig.mk <$> .positional' `name <*> .positional' `title

/-- Hash of every library source file. -/
def librarySourceHash : IO UInt64 := do
  let mut h : UInt64 := 7
  for f in ((← ("../Cubing" : System.FilePath).walkDir).qsort (·.toString < ·.toString)) do
    if f.extension == some "lean" then
      h := mixHash h (hash f.toString)
      h := mixHash h (hash (← IO.FS.readFile f))
  return h

/--
Verso's `literate` facet is traced on the module's public `.olean`, which does not change when
only prose changes (module docs live in `.olean.server`). Delete a chapter's extracted JSON
whenever any library source differs from the last extraction, so edited prose always reaches
the book.
-/
def invalidateStaleLiterate (mod : Name) : IO Unit := do
  let base := mod.components.foldl (fun p c => p / c.toString)
    ("../.lake/build/literate" : System.FilePath)
  let json := base.addExtension "json"
  let stamp := base.addExtension "src-hash"
  let now := toString (← librarySourceHash)
  let before ← if ← stamp.pathExists then IO.FS.readFile stamp else pure ""
  if before != now then
    for f in [json, json.addExtension "trace", json.addExtension "hash"] do
      if ← f.pathExists then IO.FS.removeFile f
    if let some dir := stamp.parent then IO.FS.createDirAll dir
    IO.FS.writeFile stamp now

/-- Include a library module, prose and code, as a chapter of the book. -/
@[part_command Lean.Doc.Syntax.command]
def chapter : PartCommand
  | `(block|command{chapter $args* }) => do
    let {modName, title} ← parseThe ChapterConfig (← parseArgs args)
    -- The literate extractor re-elaborates the file with only its own options, so without this
    -- line the prose would reach the book as raw markup.
    let file := modName.getId.components.foldl (fun p c => p / c.toString) ("..": System.FilePath)
    let src ← IO.FS.readFile (file.addExtension "lean")
    unless (src.splitOn "\nset_option doc.verso true\n").length > 1 do
      throwErrorAt modName "{modName.getId} must contain the line `set_option doc.verso true`"
    includedChapters.modify (·.insert modName.getId)
    invalidateStaleLiterate modName.getId
    let name ← getModuleWithDocs (Syntax.mkStrLit "..") modName title none
    let name ← do
      let name' ← mkFreshUserName (name ++ `cubes)
      addAndCompile <| .defnDecl {
        name := name', levelParams := [],
        type := .app (mkConst ``Verso.Doc.VersoDoc) (mkConst ``Manual),
        value := .app (mkConst ``CubingSite.cubeifyDoc) (mkConst name),
        hints := .regular 0, safety := .safe
      }
      pure name'
    -- Chapters sit directly under a top-level part, after any section opened before them.
    closePartsUntil 2 (← getRef).getHeadInfo.getPos!
    addPart <| .included (mkIdentFrom modName name)
  | _ => throwUnsupportedSyntax

/-- The library modules on disk: every `.lean` file under `../Cubing`. -/
partial def libraryModules : IO (Array Name) := do
  let root : System.FilePath := ".."
  let files ← (root / "Cubing").walkDir
  let mut mods := #[]
  for f in files do
    if f.extension == some "lean" then
      let some rel := f.toString.dropPrefix? (root.toString ++ "/") | continue
      let comps := (rel.toString.dropSuffix ".lean").toString.splitOn "/"
      mods := mods.push (comps.foldl Name.str .anonymous)
  return mods.qsort Name.lt

/-- Fail unless every library module has been included with `{chapter …}`. -/
@[part_command Lean.Doc.Syntax.command]
def checkCoverage : PartCommand
  | `(block|command{checkCoverage}) => do
    let included ← includedChapters.get
    let missing := (← libraryModules).filter (!included.contains ·)
    unless missing.isEmpty do
      throwError m!"These library modules are not chapters of the book: {missing.toList}"
  | _ => throwUnsupportedSyntax

end CubingSite
