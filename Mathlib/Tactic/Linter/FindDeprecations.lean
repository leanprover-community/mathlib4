/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import ImportGraph.Imports

/-!
# The `#clear_deprecations` command

This file defines the `#clear_deprecations date₁ date₂ really` command.

This function is intended for automated use by the `remove_deprecations` automation.
It removes declarations that have been deprecated in the time range starting from `date₁` and
ending with `date₂`.

See the doc-string for the command for more information.
-/

open Lean Elab Command

namespace Mathlib.Tactic

/-- A convenience instance to print a `String.Range` as the corresponding pair of `String.Pos`. -/
local instance : ToString String.Range where
  toString | ⟨s, e⟩ => s!"({s}, {e})"

/--
These are the names of the directories containing all the files that should be inspected.
For reporting, the script assumes there is no sub-dir of the `repo` dir that contains
`repo` as a substring.
However, the script should still remove old deprecations correctly even if that happens.
-/
def repos : NameSet := .ofArray #[`Mathlib, `Archive, `Counterexamples]

/--
The main structure containing the information a deprecated declaration.
* `module` is the name of the module containing the deprecated declaration;
* `decl` is the name of the deprecated declaration;
* `rgStart` is the `Position` where the deprecated declaration starts;
* `rgStop` is the `Position` where the deprecated declaration ends;
* `since` is the date when the declaration was deprecated.
-/
structure DeprecationInfo where
  /-- `module` is the name of the module containing the deprecated declaration. -/
  module : Name
  /-- `decl` is the name of the deprecated declaration. -/
  decl : Name
  /-- `rgStart` is the `Position` where the deprecated declaration starts. -/
  rgStart : Position
  /-- `rgStop` is the `Position` where the deprecated declaration ends. -/
  rgStop : Position
  /-- `since` is the date when the declaration was deprecated. -/
  since : String

/--
`getPosAfterImports fname` parses the imports of `fname` and returns the position just after them.

This position is after all trailing whitespace and comments that may follow the imports of `fname`.
-/
def getPosAfterImports (fname : String) : CommandElabM String.Pos.Raw := do
  let file ← IO.FS.readFile fname
  let fm := file.toFileMap
  let (_, fileStartPos, _) ← parseImports fm.source (← getFileName)
  return fm.ofPosition fileStartPos

/--
`addAfterImports fname s` returns the content of the file `fname`, with the string `s` added
after the imports of `fname`.
-/
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
        -- We filter here based on the top dir of the declaration.
        unless repos.contains mod.getRoot do
          return none
        if verbose? then
          logInfo
            s!"In the module '{mod}', the declaration {nm} at {rg.pos}--{rg.endPos} \
              is deprecated since {since}"
        return some { module := mod
                      decl := nm
                      rgStart := rg.pos
                      rgStop := rg.endPos
                      since := since }
  return none

/--
The output is the `HashMap` whose keys are the names of the files containing
deprecated declarations, and whose values are the arrays of ranges
corresponding to the deprecated declarations in that file.
The input `oldDate` and `newDate` are strings of the form "YYYY-MM-DD".
The output contains all the declarations that were deprecated after `oldDate`
and before `newDate`.
-/
def deprecatedHashMap (oldDate newDate : String) :
    CommandElabM (Std.HashMap (Name × String) (Array (Name × String.Range))) := do
  let mut fin := ∅
  --let searchPath ← getSrcSearchPath
  for (nm, _) in (← getEnv).constants.map₁ do
    if let some ⟨modName, decl, rgStart, rgStop, since⟩ ← getDeprecatedInfo nm false
    then
      unless repos.contains modName.getRoot do continue
      if !(oldDate ≤ since && since ≤ newDate) then
        continue
      -- Ideally, `lean` would be computed by `← findLean (← getSrcSearchPath) modName`
      -- However, while this works locally, CI throws the error ` unknown module prefix 'Mathlib'`
      let lean := (modName.components.foldl (init := "")
        fun a b => (a.push System.FilePath.pathSeparator) ++ b.toString) ++ ".lean" |>.drop 1
      --let lean ← findLean searchPath modName
      let file ← IO.FS.readFile lean
      let fm := FileMap.ofString file
      let rg : String.Range := ⟨fm.ofPosition rgStart, fm.ofPosition rgStop⟩
      fin := fin.alter (modName, lean) fun a =>
        (a.getD #[]).binInsert (·.2.1 < ·.2.1) (decl, rg)
  return fin

/--
`removeRanges file rgs` removes from the string `file` the substrings whose ranges are in the array
`rgs`.

*Notes*.
* The command makes the assumption that `rgs` is *sorted*.
* The command removes all consecutive whitespace following the end of each range.
-/
def removeRanges (file : String) (rgs : Array String.Range) : String := Id.run do
  let mut curr : String.Pos.Raw := 0
  let mut fileSubstring := file.toSubstring
  let mut tot := ""
  let last := fileSubstring.stopPos
  for next in rgs.push ⟨last, last⟩ do
    if next.start < curr then continue
    let part := {fileSubstring with stopPos := next.start}.toString
    tot := tot ++ part
    curr := next.start
    fileSubstring := {fileSubstring with startPos := next.stop}.trimLeft
  return tot

/--
`removeDeprecations fname rgs` reads the content of `fname` and removes from it the substrings
whose ranges are in the array `rgs`.

The command makes the assumption that `rgs` is *sorted*.
-/
def removeDeprecations (fname : String) (rgs : Array String.Range) : IO String :=
  return removeRanges (← IO.FS.readFile fname) rgs

/--
`parseLine line` assumes that the input string is of the form
```
info: File/Path.lean:12:0: [362, 398, 399]
```
and extracts `[362, 398, 399]`.
It makes the assumption that there is a unique `: [` substring and then retrieves the numbers.

Note that this is the output of `Mathlib.Linter.CommandRanges.commandRangesLinter`
that the script here is parsing.
-/
def parseLine (line : String) : Option (List String.Pos.Raw) :=
  match (line.dropRight 1).splitOn ": [" with
  | [_, rest] =>
    let nums := rest.splitOn ", "
    if nums == [""] then some [] else
    some <| nums.map fun s => ⟨s.toNat?.getD 0⟩
  | _ => none

/--
Takes as input a file path `fname` and an array of pairs `(declName, range of declaration)`.
The `declName` is mostly for printing information, but is not used essentially by the function.

It returns the pair `(temp file name, file without the commands that generated the declarations)`.

In the course of doing so, the function creates a temporary file from `fname`, by
* adding the import `Mathlib.Tactic.Linter.CommandRanges` and
* setting the `linter.commandRanges` option to `true`.

It parses the temporary file, capturing the output and uses the command ranges to remove the
ranges of the *commands* that generated the passed declaration ranges.
-/
def rewriteOneFile (fname : String) (rgs : Array (Name × String.Range)) :
    CommandElabM (String × String) := do
  -- `option` is the extra text that we add to the files that contain deprecations.
  -- We save these modified files with a different name then their originals, so that all their
  -- dependencies still have valid `olean`s and we build them to collect the ranges of the commands
  -- in each one of them.
  let option :=
    s!"\nimport Mathlib.Tactic.Linter.CommandRanges\n\
      set_option linter.commandRanges true\n"
  -- `offset` represents the difference between a position in the modified file and the
  -- corresponding position in the original file.
  -- Since we added the modification right after the imports, the command positions of the old file
  -- are always smaller than the command positions of the new file.
  let offset := option.toSubstring.stopPos
  let fileWithOptionAdded ← addAfterImports fname option
  let fname_with_option := fname.dropRight ".lean".length ++ "_with_option.lean"
  let file ← IO.FS.readFile fname
  let fm := file.toFileMap
  let rgsPos := rgs.map fun (decl, ⟨s, e⟩) =>
    m!"* {.ofConstName decl} {(fm.toPosition s, fm.toPosition e)}"
  let rgsStringPos := rgs.map (m!"{·.2}")
  let combinedRanges := rgsPos.zipWith (· ++ m!" " ++ ·) rgsStringPos |>.toList
  logInfo m!"Adding '{option}' to '{fname}'\nWriting to {indentD fname_with_option}\n\
          Removing the following declarations\n{m!"\n".joinSep combinedRanges}"
  IO.FS.writeFile fname_with_option fileWithOptionAdded
  let ranges := rgs.map (·.2)

  logInfo m!"Retrieving command positions from '{fname_with_option}'"
  let commandPositions ←
    IO.Process.output {cmd := "lake", args := #["build", fname_with_option]}
  -- `stringPositions` consists of lists of the form `[p₁, p₂, p₃]`, where
  -- * `p₁` is the start of a command;
  -- * `p₂` is the end of the command, excluding trailing whitespace and comments;
  -- * `p₁` is the end of the command, including trailing whitespace and comments.
  let stringPositions := (commandPositions.stdout.splitOn "\n").map parseLine |>.reduceOption
  let mut removals : Std.HashSet (List String.Pos.Raw) := ∅
  -- For each range `rg` in `ranges`, we isolate the unique entry of `stringPositions` that
  -- entirely contains `rg`.  This helps catching the full range of `open Nat in @[deprecated] ...`,
  -- rather than just the `@[deprecated] ...` range.
  for rg in ranges do
    let candidate := stringPositions.filterMap (fun arr ↦
      let a := arr.head! - offset
      let b := arr[arr.length - 1]! - offset
      if a ≤ rg.start ∧ rg.stop ≤ b then some (arr.map (· - offset)) else none)
    match candidate with
    | [d@([_, _, _])] => removals := removals.insert d
    | _ => logInfo "Something went wrong!"
  -- We only remember the `start` and `end` of each command, ignoring trailing whitespace and
  -- comments.  This means that we may err on the side of preserving comments that may have to be
  -- manually removed, instead of having to manually add them back later on.
  let rems : Std.HashSet _ := removals.fold (init := ∅) fun tot ↦ fun
    | [a, b, _c] => tot.insert (⟨a, b⟩ : String.Range)
    | _ => tot
  return (fname_with_option, ← removeDeprecations fname (rems.toArray.qsort (·.1 < ·.1)))

/-- The `<` partial order on modules: `importLT env mod₁ mod₂` means that `mod₂` imports `mod₁`. -/
def importLT (env : Environment) (f1 f2 : Name) : Bool :=
  (env.findRedundantImports #[f1, f2]).contains f1

/--
`#clear_deprecations "YYYY₁-MM₁-DD₁" "YYYY₂-MM₂-DD₂" really` computes the declarations that have
the `@[deprecated]` attribute and the `since` field satisfies
`YYYY₁-MM₁-DD₁ ≤ since ≤ YYYY₂-MM₂-DD₂`.
For each one of them, it retrieves the command that generated it and removes it.
It also verbosely logs various steps of the computation.

Running `#clear_deprecations "YYYY₁-MM₁-DD₁" "YYYY₂-MM₂-DD₂"`, without the trailing `really` skips
the removal, but still emits the same verbose output.

This function is intended for automated use by the `remove_deprecations` automation.
-/
elab "#clear_deprecations " oldDate:str ppSpace newDate:str really?:(&" really")? : command => do
  let oldDate := oldDate.getString
  let newDate := newDate.getString
  let fmap ← deprecatedHashMap oldDate newDate
  let mut filesToRemove := #[]
  let env ← getEnv
  let sortedFMap := fmap.toArray.qsort fun ((a, _), _) ((b, _), _) => importLT env b a
  if sortedFMap.isEmpty then
    logInfo m!"No deprecations in the range from {oldDate} to {newDate}"
    return
  for ((modName, fname), noDeprs) in sortedFMap do
    let (toRemove, fileWithoutDeprecations) ← rewriteOneFile fname noDeprs
    let message :=
      m!"Click to see the file with the deprecations in the date range \
        {oldDate} to {newDate} removed"
    let collapsibleMessage := .trace {cls := modName} message #[fileWithoutDeprecations]
    logInfo collapsibleMessage
    if really?.isSome then
      IO.FS.writeFile fname fileWithoutDeprecations
    filesToRemove := filesToRemove.push toRemove
  logInfo
    m!"Removing the temporary files\n* {m!"\n* ".joinSep (filesToRemove.map (m!"{·}")).toList}"
  for tmp in filesToRemove do
    IO.FS.removeFile tmp

end Mathlib.Tactic
