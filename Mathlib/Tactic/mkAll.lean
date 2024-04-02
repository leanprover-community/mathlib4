/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Util.Path

/-!
#  An implementation of the `mk_all.sh` script in Lean
-/

namespace Mathlib.MKAll

/-- the command `git ls-files '*.lean'` -/
def gitLSFiles : IO.Process.SpawnArgs where
  cmd := "git"
  args := #["ls-files", "*.lean"]

open Lean System.FilePath in
/-- `getAll str` takes all Git-managed `.lean` files in the repository in the dir `str` and
returns the string
```
import file₁
...
import fileₙ
```
The string `str` is optional and the stript defaults to `Mathlib` if unprovided. -/
def getAll (ml : String := "Mathlib") : IO String := do
  let ml.lean := addExtension ⟨ml⟩ "lean"  -- `Mathlib.lean`
  let mlDir := ml.push pathSeparator       -- `Mathlib/`
  let allLean ← IO.Process.run gitLSFiles
  let files : List System.FilePath := ((allLean.splitOn "\n").filter mlDir.isPrefixOf).map (⟨·⟩)
  let files := (files.erase ml.lean).toArray.qsort (·.toString < ·.toString)
  let withImport ← files.mapM fun f => return "import " ++ (← moduleNameOfFileName f none).toString
  return ("\n".intercalate withImport.toList).push '\n'

/-- the "Mathlib usual suspects" for "import all" files. -/
abbrev candidates := #["Mathlib", "MathlibExtras", "Mathlib/Tactic", "Counterexamples", "Archive"]

open System.FilePath in
/-- running `#eval mkAll arr` creates an "import all" file for each of the roots in the array `arr`.
The input `arr` is optional and `mkAll` defaults to using `candidates`, if unprovided. -/
def mkAll (cands : Array String := candidates) : IO Unit := do
  for d in cands do
    IO.FS.writeFile (addExtension ⟨d⟩ "lean") (← getAll d)
