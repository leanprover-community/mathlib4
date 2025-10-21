/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Tactic.Linter.Header

/-!
# The "emptyLine" linter

The "emptyLine" linter emits a warning on empty lines inside a command, but outside of a
doc-string/module-doc.
-/

open Lean Elab Linter

/-- Retrieve the `String.Range` of a `Substring`. -/
def Substring.getRange : Substring → String.Range
  | {startPos := st, stopPos := en, ..} => ⟨st, en⟩

namespace Lean.Syntax
/-!
# `Syntax` filters
-/

/--
`filterMapM stx f` takes as input a `Syntax` `stx` and a monadic function `f : Syntax → m α`.
It produces the array of the `some` values that `f` takes while traversing `stx`.

See `filterMap` for a non-monadic version.
-/
partial
def filterMapM {m : Type → Type} [Monad m] {α} (stx : Syntax) (f : Syntax → m (Option α)) :
    m (Array α) := do
  let nargs := (← stx.getArgs.mapM (·.filterMapM f)).flatten
  match ← f stx with
    | some new => return nargs.push new
    | none => return nargs

/--
`filterMap stx f` takes as input a `Syntax` `stx` and a function `f : Syntax → α`.
It produces the array of the `some` values that `f` takes while traversing `stx`.

See `filterMapM` for a non-monadic version.
-/
def filterMap {α} (stx : Syntax) (f : Syntax → Option α) : Array α :=
  Id.run <| stx.filterMapM fun x => pure (f x)

/--
`filter stx f` takes as input a `Syntax` `stx` and a function `f : Syntax → Bool`.
It produces the array of the syntax nodes in `stx` where `f` is `true`.

See also the similar `filterMap` and `filterMapM`.
-/
def filter (stx : Syntax) (f : Syntax → Bool) : Array Syntax :=
  stx.filterMap fun s => if f s then some s else none

end Lean.Syntax

namespace Mathlib.Linter

/--
The "emptyLine" linter emits a warning on empty lines inside a command, but outside of a
doc-string/module-doc.

The linter is only active when there are no other warnings, so as to not add noise when developing
incomplete proofs.
-/
register_option linter.style.emptyLine : Bool := {
  defValue := false
  descr := "enable the emptyLine linter"
}

namespace EmptyLine

/-- The `SyntaxNodeKind`s where the `EmptyLine` linter is not active -/
abbrev AllowEmptyLines : Std.HashSet SyntaxNodeKind := Std.HashSet.emptyWithCapacity
  |>.insert ``Parser.Command.docComment
  |>.insert ``Parser.Command.moduleDoc
  |>.insert ``Parser.Command.mutual
  |>.insert `str

/-- If a file contains one of these names as segments, we disable the `emptyLine` linter. -/
abbrev SkippedFileSegments : Std.HashSet Name := Std.HashSet.emptyWithCapacity
  |>.insert `Tactic
  |>.insert `Util
  |>.insert `Meta

/-- A convenience instance, so that we can add string positions. -/
local instance : Add String.Pos.Raw where
  add := fun | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

@[inherit_doc Mathlib.Linter.linter.style.emptyLine]
def emptyLineLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.style.emptyLine (← getLinterOptions) do
    return
  -- The linter does not report anything on incomplete proofs, e.g. proofs containing `sorry`
  -- or `stop`.
  if (← get).messages.reportedPlusUnreported.any (!·.severity matches .information) then
    return
  if ((← getMainModule).components.find? SkippedFileSegments.contains).isSome then
    return
  -- We ignore empty lines "after" the command finished.
  let stx := stx.unsetTrailing
  let some str := stx.getSubstring? | return
  let allowed := stx.filter (AllowEmptyLines.contains ·.getKind)
  let allowedRanges := allowed.filterMap (·.getRange?)
  let one :: rest@(_ :: _) := str.toString.trimRight.splitOn "\n\n" | return
  -- We extract all trailing ranges of all syntax nodes in `stx`, after we remove
  -- leading and trailing whitespace from them.
  -- These ranges typically represent embedded comments and we ignore line breaks inside them.
  -- We do inspect leading and trailing whitespace though.
  -- We treat `where` specially, since we allow empty lines in `where` fields.
  let trails := stx.filterMap fun s =>
    if let some str := s.getTrailing?
    then
      -- Handle `where` and `where` fields.
      if s.getAtomVal == "where" ||
         s.isOfKind ``Parser.Term.structInstField ||
         s.isOfKind ``Parser.Command.structSimpleBinder then
        s.getTrailing?.map (·.getRange)
      else
        let strim := str.trim
        if strim.toString.toSlice.contains "\n\n" then
          some strim.getRange
        else none
    else none
  let trails : Std.HashSet String.Range := .ofArray trails
  -- The entries of the array `rgs` represent
  -- * the range of the offending line breaks,
  -- * the line preceding an empty line and
  -- * the line following an empty line.
  let mut ranges : Array (String.Range × String × String) := #[]
  let mut currOffset := str.startPos + one.endPos + ⟨1⟩
  let mut prev := one.takeRightWhile (· != '\n')
  for r in rest do
    ranges := ranges.push (⟨currOffset, currOffset⟩, prev, r.takeWhile (· != '\n'))
    currOffset := currOffset + r.endPos + ⟨2⟩
    prev := r.takeRightWhile (· != '\n')
  let allowedRanges := trails.insertMany allowedRanges
  for (rg, before, after) in ranges do
    if allowedRanges.any fun okRg ↦ okRg.start ≤ rg.start && rg.stop ≤ okRg.stop then
      continue
    -- `s` is a string of as many spaces (` `) as the characters of the previous line.
    -- This, followed by the downarrow (`↓`) creates a pointer to an offending line break.
    let s : String := .join <| List.replicate (before.length + 1) " "
    Linter.logLint linter.style.emptyLine (.ofRange rg)
      m!"Please, write a comment here or remove this line, \
        but do not place empty lines within commands!\nContext:\n\
        {indentD s!"{s.push '↓'}"}{indentD s!"⏎{before}⏎⏎{after}⏎"}"

initialize addLinter emptyLineLinter

end EmptyLine

end Mathlib.Linter
