/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command
import Lean.Elab.Import
import Mathlib.Tactic.Linter.Header
/-!
#  The "removeDeprecations" linter

The "removeDeprecations" linter removed deprecated declarations from a file.
-/

open Lean Elab Command Linter

namespace Mathlib.Linter

/-- The "removeDeprecations" linter reports constructs that are considered to be technical debt. -/
register_option linter.removeDeprecations : String := {
  defValue := ""
  descr := "enable the removeDeprecations linter"
}

/--
`RemoveDeprecations` stores the information used to remove deprecated declarations from a file.
* `firstLast` keeps track of which commands have already been elaborated, so that we can detect
  when the last command is being elaborated;
* `removals` keeps track of the ranges of the commands that should be removed.

A convenient way to think of `firstLast` is as follows:
if `firstLast = {aᵢ : i = 1...n}`, with `a₁ < a₂ < ... < aₙ`
then the commands in the ranges `[a₂ᵢ₋₁, a₂ᵢ]` have not yet been elaborated.
Note that `firstLast` always has an even number of elements.

The way `firsLast` works is as follows.

It starts out empty.

When a command is elaborated and `firstLast` is empty, then Lean has finished parsing the first
command of the file.
Note: due to parallel elaboration, this command need not be the first one appearing in the file,
it is simply the one where elaboration finishes first.

At this point, we initialize `firstLast` using `initializeExt` to contain
* the starting position of the first non-import command start of the file and
* the position of the end of the file.

Next, whether or not we initialized `firstLast`, we update `firstLast` on *every* command
using `update`,
toggling the presence of the starting and ending position of the command (via `toggleEntry`).

Since each command ends where the next one starts, once the file has been fully elaborated,
`firstLast` is empty again.
-/
structure RemoveDeprecations where
  /-- The positions of the commands that have not yet been elaborated. -/
  firstLast : Std.HashSet String.Pos
  /--
  The "strict" ranges of the commands that should be removed:
  this does *not* include trailing whitespace and comments.
  -/
  removals : Std.HashSet String.Range
  deriving Inhabited

/--
An `IO.Ref` containing a `RemoveDeprecations`. The `techDebt` linter updates it after
each command is elaborated.
-/
initialize RemoveDeprecationsExt : IO.Ref RemoveDeprecations ← IO.mkRef default

namespace RemoveDeprecations

/--
`toggleEntry h a` toggles the presence of `a` in the `HashSet` `h`: it removes it if it is present
and adds it if it is not.
-/
def toggleEntry {α} [BEq α] [Hashable α] (h : Std.HashSet α) (a : α) : Std.HashSet α :=
  if h.contains a then h.erase a else h.insert a

instance : ToString String.Range where
  toString | ⟨s, e⟩ => s!"({s}, {e})"
--#check Lean.Elab.HeaderSyntax.imports
--run_cmd
--  let a ← withImporting
--#check

/-
run_cmd
  let (imps, pos, msgs) ← parseImports "import Mathlib.GroupTheory.MonoidLocalization.MonoidWithZero_with_option" "test.lean"
  dbg_trace imps
  logInfo m!"{pos}"
  --logInfo msgs.reportedPlusUnreported.toArray

  let (a, b) ← withImportModules imps {} fun e => pure (e.constants.map₁.size, e.find? `Submonoid.LocalizationMap.subsingleton |>.isSome)
  dbg_trace (a, b)
-/

/--
`update rd s` updates `rd` by toggling the presence of the starting and ending
positions of the syntax `s` in `rd.firstLast`.
If `s` is a `deprecated` attribute, then its range is added to `rd.removals`.
If `s` is a terminal command, then `rd.firstLast` is not updated.
-/
def update (oldDate newDate : String) (rd : RemoveDeprecations) (s : Syntax) : RemoveDeprecations :=
  if Parser.isTerminalCommand s then
    --dbg_trace (s.getRangeWithTrailing?, s.getRange?)
    rd
  else
  match s.getRangeWithTrailing? with
  | none => rd
  | some rg =>
    let ans := {rd with
      firstLast :=
        let updateStart := toggleEntry rd.firstLast rg.start
        toggleEntry updateStart rg.stop}
    if let some deprStx := s.find? (·.isOfKind ``deprecated) then
      match deprStx with
      | `(attr| deprecated $[$id?]? $[$text?]? (since := $since)) =>
        let since := since.getString
        if oldDate ≤ since && since ≤ newDate then
          --dbg_trace ""
          --dbg_trace "removing deprecation since {since}"
          {ans with removals := rd.removals.insert (s.getRange?.getD rg)}
        else
          --dbg_trace "NOT removing this"
          ans
      | _ =>
        ans
    else
      ans

/--
`initializeExt fm fileStart` is the `RemoveDeprecations` with
* `rd.firstLast = {fileStart, end-of-file}` and
* `rd.removals = ∅`.
-/
def initializeExt (fm : FileMap) (fileStart : String.Pos) :
    RemoveDeprecations :=
  {firstLast := {fileStart, fm.positions.back?.getD fileStart}, removals := ∅}

/--
`removeDeprecations file rgs` removes from `file` all the ranges in `rgs`.
-/
def removeDeprecations (file : String) (rgs : Array String.Range) : IO String := do
  let mut fileSubstring := file.toSubstring
  let eof := fileSubstring.stopPos
  let mut tot := ""
  for next in rgs.push ⟨eof, eof⟩ do
    let part := {fileSubstring with stopPos := next.start}.toString
    tot := tot ++ part
    fileSubstring := {fileSubstring with startPos := next.stop}.dropWhile (·.isWhitespace)
  return tot.trimRight.push '\n'

@[inherit_doc Mathlib.Linter.linter.removeDeprecations]
def removeDeprecationsLinter : Linter where run stx := do
  let linterBound := linter.removeDeprecations.get (← getOptions)
  if linterBound.isEmpty then
    return
  let [oldDate, newDate] := (linterBound.splitOn " ") | throwError "The expected format is \
    'YYYY-MM-DD YYYY-MM-DD', where the first date is earlier than the second one \
    and all declarations that have been deprecated in between the two will be erased."
  unless oldDate ≤ newDate do
    throwError "The first date should not be later than the second date!"
  if (← get).messages.hasErrors then
    return
  dbg_trace (stx.getRange?, stx.getRangeWithTrailing?.map (·.stop))
  if (← RemoveDeprecationsExt.get).firstLast.isEmpty then
    let fm ← getFileMap
    let (_, fileStartPos, _) ← parseImports fm.source (← getFileName)
    RemoveDeprecationsExt.modify fun _ =>
      initializeExt fm (fm.ofPosition fileStartPos)
  RemoveDeprecationsExt.modify (update oldDate newDate · stx)
  let rd ← RemoveDeprecationsExt.get
  --dbg_trace rd.firstLast.toArray.qsort (·.1 < ·.1)
  -- When `rd.firstLast` is empty, the current command is the last to be elaborated.
  -- Hence, this is where we can reconstruct the file without the deprecations.
  --if rd.firstLast.isEmpty || Parser.isTerminalCommand stx then
  if rd.firstLast.isEmpty then
    --dbg_trace "After checking firstLast"
    let fm ← getFileMap
    let replacements := rd.removals.toArray.qsort (·.start < ·.start)
    if !replacements.isEmpty then
      let cleanUpDeprecations ← removeDeprecations fm.source replacements
      --dbg_trace "{stx.getKind} completed the whole syntax!:\n{replacements}"
      let fname ← getFileName
      let tmpFname := fname.replace "Mathlib" ".lake/build/lib/lean/Mathlib" ++ ".tmp"
      --let tmpFname := fname ++ ".tmp"
      dbg_trace "bash\nmv -f {tmpFname} {fname}"
      --dbg_trace cleanUpDeprecations

      --/-
      IO.FS.writeFile tmpFname cleanUpDeprecations
      let diff ← IO.Process.output {
        cmd := "diff"
        args := #[fname, tmpFname]
      }
      logInfo diff.stdout
      --/

    --else
    --  dbg_trace "This file contains no deprecations!"

initialize addLinter removeDeprecationsLinter

end RemoveDeprecations

end Mathlib.Linter
