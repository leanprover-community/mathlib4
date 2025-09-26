/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
--import Mathlib --.Deprecated.Order
import Lean
--import Mathlib.mwe_deprecations

/-!
d
-/

open Lean Elab Command

/--
This is the name of the directory containing all the files that should be inspected.
For reporting, the script assumes there is no sub-dir of the `repo` dir that contains
`repo` as a substring.
However, the script should still remove old deprecations correctly even if that happens.
-/
def repo : Name := `Mathlib

/--
The main structure containing the information a deprecated declaration.
* `module` is the name of the module containing the deprecated declaration;
* `rgStart` is the `Position` where the deprecated declaration starts;
* `rgStop` is the `Position` where the deprecated declaration ends;
* `since` is the date when the declaration was deprecated.
-/
structure DeprecationInfo where
  /-- `module` is the name of the module containing the deprecated declaration. -/
  module : Name
  /-- `rgStart` is the `Position` where the deprecated declaration starts. -/
  rgStart : Position
  /-- `rgStop` is the `Position` where the deprecated declaration ends. -/
  rgStop : Position
  /-- `since` is the date when the declaration was deprecated. -/
  since : String

def getPosAfterImports (fname : String) : CommandElabM String.Pos := do
  let file ← IO.FS.readFile fname
  let fm := file.toFileMap
  let (_, fileStartPos, _) ← parseImports fm.source (← getFileName)
  return fm.ofPosition fileStartPos

def addAfterImports (fname s : String) : CommandElabM String := do
  let pos ← getPosAfterImports fname
  let file ← IO.FS.readFile fname
  let fileSubstring := file.toSubstring
  return {fileSubstring with stopPos := pos}.toString ++ s ++
    {fileSubstring with startPos := pos}.toString

/--
If `nm` is the name of a declaration, then `getDeprecatedInfo nm` returns the
`DeprecationInfo` data for `nm`.
Otherwise, it returns `none`.

If the `verbose?` input is `true`, then the command also summarizes what the data is.
-/
def getDeprecatedInfo (nm : Name) (verbose? : Bool) :
    CommandElabM (Option DeprecationInfo) := do
  let env ← getEnv
  -- if there is a `since` in the deprecation
  if let some {since? := some since, ..} := Linter.deprecatedAttr.getParam? env nm
  then
    -- retrieve the `range` for the declaration
    if let some {range := rg, ..} ← findDeclarationRanges? nm
    then
      -- retrieve the module where the declaration is located
      if let some mod ← findModuleOf? nm
      then
        if verbose? then
          logInfo
            s!"In the module '{mod}', the declaration {nm} at {rg.pos}--{rg.endPos} \
              is deprecated since {since}"
        return some {module := mod, rgStart := rg.pos, rgStop := rg.endPos, since := since}
  return none

/--
Assume that the input `fin` is sorted so that the `start` of each entry is not larger than
the start of the following one.
`cleanUpRanges fin` is the sub-array of `fin` consisting of all the entries that do not
correspond to ranges entirely contained in the previous one.
-/
def cleanUpRanges (fin : Array String.Range) : Array String.Range :=
  fin.foldl (init := #[]) fun tot n =>
    if let some back := tot.back? then
      if back.start ≤ n.start && n.stop ≤ back.stop then
        tot
      else
        tot.push n
    else
        tot.push n

/--
The output is the `HashMap` whose keys are the names of the files containing
deprecated declarations, and whose values are the arrays of ranges
corresponding to the deprecated declarations in that file.
The input `oldDate` and `newDate` are strings of the form "YYYY-MM-DD".
The output contains all the declarations that were deprecated after `oldDate`
and before `newDate`.
-/
def deprecatedHashMap (oldDate newDate : String) :
    CommandElabM (Std.HashMap String (Array String.Range)) := do
  let mut fin := ∅
  let searchPath ← getSrcSearchPath
  for (nm, _) in (← getEnv).constants.map₁ do
    if let some ⟨modName, rgStart, rgStop, since⟩ ← getDeprecatedInfo nm false
    then
      if modName.getRoot != repo then continue
      if oldDate ≤ since && since ≤ newDate then
        continue
      try
        let lean ← findLean searchPath modName
        dbg_trace lean
        let file ← IO.FS.readFile lean
        dbg_trace file.take 80
        let fm := FileMap.ofString file
        let rg : String.Range := ⟨fm.ofPosition rgStart, fm.ofPosition rgStop⟩
        --dbg_trace (rgStart, rgStop)
        fin := fin.alter lean.toString fun a =>
          (a.getD #[⟨fm.positions.back!, fm.positions.back! + ⟨1⟩⟩]).binInsert (·.1 < ·.1) rg
      catch e =>
        if let .error ref msg := e then
          logInfoAt ref m!"error on {modName}: {msg}"
        --dbg_trace "error on {modName}"
        continue
  return fin

def removeDeprecations (fname : String) (rgs : Array String.Range) : IO String := do
  let file ← IO.FS.readFile fname
  let mut curr : String.Pos := 0
  let mut fileSubstring := file.toSubstring
  let mut tot := ""
  for next in rgs do
    if next.start < curr then continue
    let part := {fileSubstring with stopPos := next.start}.toString
    tot := tot ++ part
    curr := next.start
    fileSubstring :=
      ({fileSubstring with startPos := next.stop}.dropWhile (!·.isWhitespace)).trimLeft
  return tot

open Lean Elab Command in
elab "#regenerate_deprecations " oldDate:str newDate:str really?:("really")? : command => do
  let repo := repo.toString
  let oldDate := oldDate.getString
  let newDate := newDate.getString
  let dmap ← deprecatedHashMap oldDate newDate
  for (mod, rgs) in dmap.toArray.qsort (·.1 < ·.1) do
    let option := s!"\nset_option linter.removeDeprecations \"{oldDate} {newDate}\"\n"
    dbg_trace s!"Adding '{option}' to '{mod}'"
    let optionAdded ← addAfterImports mod option
    --dbg_trace optionAdded
    let newName := mod.dropRight ".lean".length ++ "_with_option.lean"
    dbg_trace s!"Writing to '{newName}'"
    if really?.isSome then
      IO.FS.writeFile newName optionAdded
    if false then
    let mod1 := repo ++ (mod.splitOn repo).getLast!
    let rgs := cleanUpRanges rgs
    let num := rgs.size - 1
    dbg_trace "remove {num} declaration{if num == 1 then " " else "s"} from '{mod1}'"
    if really?.isSome then
      IO.FS.writeFile mod (← removeDeprecations mod rgs)

--#regenerate_deprecations "2025-07-19" "2025-09-20" --really

open Lean Elab Command in
elab "#remove_deprecated_declarations " oldDate:str newDate:str really?:("really")? : command => do
  let repo := repo.toString
  let oldDate := oldDate.getString
  let newDate := newDate.getString
  let dmap ← deprecatedHashMap oldDate newDate
  dbg_trace "{dmap.fold (init := 0) fun tot _ rgs => tot + rgs.size - 1} \
      deprecations among {dmap.size} files"
  for (mod, rgs) in dmap.toArray.qsort (·.1 < ·.1) do
    let mod1 := repo ++ (mod.splitOn repo).getLast!
    let rgs := cleanUpRanges rgs
    dbg_trace
      "From '{mod1}' remove\n{rgs.map fun | ⟨a, b⟩ => (a, b)}\n---\n{← removeDeprecations mod rgs}"
    let num := rgs.size - 1
    dbg_trace "remove {num} declaration{if num == 1 then " " else "s"} from '{mod1}'"
    if really?.isSome then
      IO.FS.writeFile mod (← removeDeprecations mod rgs)

--#remove_deprecated_declarations "2025-07-19" "2025-09-20" --really
