/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison, Damiano Testa
-/
module

public meta import Lean.Util.Path

import Mathlib.Init

/-!
# Utility functions for finding all `.lean` files or modules in a project.

TODO: Could this be made more structural and robust, possibly with extra `Lake` support?
-/

public meta section

open Lean System.FilePath

/-- `getAllFiles git dir` takes all `.lean` files in the directory `dir`
(recursing into sub-directories) and returns the `Array` of `System.FilePath`s
```
#[file₁, ..., fileₙ]
```
of all their file names. These are not sorted in general.

The input `git` is a `Bool`ean flag:
* `true` means that the command uses `git ls-files` to find the relevant files;
* `false` means that the command recursively scans all dirs searching for `.lean` files.
-/
def getAllFiles (git : Bool) (dir : System.FilePath) : IO (Array System.FilePath) := do
  let allModules : Array System.FilePath ←
    if git then
      let dir ← IO.FS.realPath dir
      let allLean ← IO.Process.run
        { cmd := "git", args := #["ls-files", (dir / "*.lean").toString] }
      pure <| ((allLean.dropEndWhile (· == '\n')).copy.splitOn "\n").toArray.map (⟨·⟩)
    else
      let all ← walkDir dir
      pure <| all.filter (·.extension == some "lean")
  -- Filter out all files which do not exist.
  -- This check is helpful in case the `git` option is on and a local file has been removed.
  allModules.filterM fun modPath => modPath.pathExists

/-- Like `getAllFiles`, but return an array of *module* names instead,
i.e. names of the form `Mathlib.Algebra.Algebra.Basic`. In addition, these names are sorted in a
platform-independent order.

`srcDir` is the part of the path that is not part of the module name, and should be specified when
to using a top-level directory in order to peel off the correct number of components from the path
for the resulting names. -/
def getAllModulesSorted (git : Bool) (dir : System.FilePath)
    (srcDir := dir.parent.getD ".") : IO (Array Name) := do
  let files ← getAllFiles git dir
  let names ← files.mapM fun f => moduleNameOfFileName f srcDir
  return names.qsort (·.toString < ·.toString)
