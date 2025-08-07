import Lean

open Lean

structure Edit where
  range : String.Range
  replacement : String
deriving BEq, Repr

def String.Pos.cmp (p₁ p₂ : String.Pos) : Ordering :=
  compareOfLessAndBEq p₁ p₂

def String.Range.cmp (r₁ r₂ : String.Range) : Ordering :=
  r₁.start.cmp r₂.start |>.then <| r₁.stop.cmp r₂.stop

def Edit.cmp (e₁ e₂ : Edit) : Ordering :=
  e₁.range.cmp e₂.range

initialize editExt : PersistentEnvExtension Edit Edit (List Edit) ←
  registerPersistentEnvExtension {
    mkInitial       := pure {}
    addImportedFn   := fun _ _ => pure {}
    addEntryFn      := fun edits e => e :: edits
    exportEntriesFn := fun edits =>
      edits.toArray.qsort fun e₁ e₂ => e₁.cmp e₂ |>.isLT
    statsFn         := fun s => "edits added: " ++ f!"{repr s}"
    asyncMode       := .sync -- hmm
    replay?         := none
  }

@[inline] private def Lean.Environment.getModuleName (env : Environment) (idx : Nat) :
    Option Name := env.header.modules[idx]?.map (·.module)

-- From Mathlib.Tactic.Core:
/-- Returns the root directory which contains the package root file, e.g. `Mathlib.lean`. -/
def getPackageDir (pkg : String) : IO System.FilePath := do
  let sp ← getSrcSearchPath
  let root? ← sp.findM? fun p =>
    (p / pkg).isDir <||> ((p / pkg).withExtension "lean").pathExists
  if let some root := root? then return root
  throw <| IO.userError s!"Could not find {pkg} directory. \
    Make sure the LEAN_SRC_PATH environment variable is set correctly."
-- end Mathlib.Tactic.Core

-- From CacheM.mathlibDepPath
def getDirOfModule (sp : SearchPath) (mod : Name) : IO System.FilePath := do
  let modSourceFile ← Lean.findLean sp mod
  let some modSourceDir ← pure modSourceFile.parent
    | throw <| IO.userError s!"{mod} not found on search path:\n  {sp}"
  return modSourceDir

def executeEdits (env : Environment) (root : Name) : IO Unit := do
  let sourceDir ← getDirOfModule (← getSrcSearchPath) root
  let editss := (editExt.toEnvExtension.getState env).importedEntries
  for h : idx in [:editss.size] do
    let edits := editss[idx]
    unless edits.isEmpty do
      let some mod := env.getModuleName idx | continue
      if mod.getRoot != root || mod == env.mainModule then continue
      let path := modToFilePath sourceDir mod "lean"
      IO.println
        s!"writing {edits.size} edit{if edits.size == 1 then "" else "s"} to {mod} @ {path}"
      -- Mario's code:
      let text ← IO.FS.readFile path
      let mut pos : String.Pos := 0
      let mut out : String := ""
      for edit in edits do -- already sorted
        if pos ≤ edit.range.start then
          out := out ++ text.extract pos edit.range.start ++ edit.replacement
          pos := edit.range.stop
      out := out ++ text.extract pos text.endPos
      IO.FS.writeFile path out

def showEdits (env : Environment) (root : Name) : IO Unit := do
  -- let base ← Mathlib.getPackageDir "Mathlib"
  let sourceDir ← getDirOfModule (← getSrcSearchPath) `EditTest
  let editss := (editExt.toEnvExtension.getState env).importedEntries
  for h : idx in [:editss.size] do
    let edits := editss[idx]
    unless edits.isEmpty do
      let some mod := env.getModuleName idx | continue
      if mod.getRoot != root || mod == env.mainModule then continue
      let path := modToFilePath sourceDir mod "lean"
      -- Mario's code:
      IO.println s!"writing {edits.size} edits to {mod} @ {path}:"
      let text ← IO.FS.readFile path
      let mut pos : String.Pos := 0
      let mut out : String := ""
      for edit in edits do -- already sorted
        if pos ≤ edit.range.start then
          out := out ++ text.extract pos edit.range.start ++ edit.replacement
          pos := edit.range.stop
      out := out ++ text.extract pos text.endPos
      IO.println <| s!"-----\n" ++ out ++ s!"-----"
      -- IO.FS.writeFile path out
