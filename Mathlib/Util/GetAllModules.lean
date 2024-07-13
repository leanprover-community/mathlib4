/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison, Damiano Testa
-/

import Lean.Util.Path


/-!
# Utility functions for finding all `.lean` files or modules in a project.

TODO:
`getLeanLibs` contains a hard-coded choice of which dependencies should be built and which ones
should not.  Could this be made more structural and robust, possibly with extra `Lake` support?

-/

open Lean System.FilePath

/-- `getAllFiles git ml` takes all `.lean` files in the directory `ml`
(recursing into sub-directories) and returns the `Array` of `String`s
```
#[file₁, ..., fileₙ]
```
of all their file names. These are not sorted in general.

The input `git` is a `Bool`ean flag:
* `true` means that the command uses `git ls-files` to find the relevant files;
* `false` means that the command recursively scans all dirs searching for `.lean` files.
-/
def getAllFiles (git : Bool) (ml : String) : IO (Array System.FilePath) := do
  let ml.lean := addExtension ⟨ml⟩ "lean"  -- for example, `Mathlib.lean`
  let allModules : Array System.FilePath ← (do
    if git then
      let mlDir := ml.push pathSeparator   -- for example, `Mathlib/`
      let allLean ← IO.Process.run { cmd := "git", args := #["ls-files", mlDir ++ "*.lean"] }
      return (((allLean.dropRightWhile (· == '\n')).splitOn "\n").map (⟨·⟩)).toArray
    else do
      let all ← walkDir ml
      return all.filter (·.extension == some "lean"))
  -- Filter out all files which do not exist.
  -- This check is helpful in case the `git` option is on and a local file has been removed.
  return ← (allModules.erase ml.lean).filterMapM (fun f ↦ do
    if ← pathExists f then pure (some f) else pure none
  )

/-- Like `getAllFiles`, but return an array of *module* names instead,
i.e. names of the form `Mathlib.Algebra.Algebra.Basic`.
In addition, these names are sorted in a platform-independent order. -/
def getAllModulesSorted (git : Bool) (ml : String) : IO (Array String) := do
  let files ← getAllFiles git ml
  let names := ← files.mapM fun f => do
     return (← moduleNameOfFileName f none).toString
  return names.qsort (· < ·)
