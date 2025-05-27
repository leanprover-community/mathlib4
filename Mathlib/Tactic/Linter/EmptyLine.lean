/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Tactic.Linter.Header

/-!
#  The "emptyLine" linter

The "emptyLine" linter emits a warning on empty lines inside a command, but outside of a
doc-string/module-doc.
-/

open Lean Elab

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
  stx.filterMapM (m := Id) f

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

The linter is only active when there are no other warning, so as to not add noise when developing
incomplete proofs.
-/
register_option linter.style.emptyLine : Bool := {
  defValue := false
  descr := "enable the emptyLine linter"
}

namespace EmptyLine

/-- The `SyntaxNodeKind`s where the `EmptyLine` linter is not active. -/
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

@[inherit_doc Mathlib.Linter.linter.style.emptyLine]
def emptyLineLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.style.emptyLine (← getOptions) do
    return
  -- The linter does not report anything on incomplete proofs.
  if (← get).messages.reportedPlusUnreported.any (!·.severity matches .information) then
    return
  if !((← getMainModule).components.filter SkippedFileSegments.contains).isEmpty then
    return
  -- We ignore empty lines "after" the command finished.
  let stx := stx.unsetTrailing
  let allowed := stx.filter (AllowEmptyLines.contains ·.getKind)
  let allowedRanges := allowed.filterMap (·.getRange?)
  if let some str := stx.getSubstring? then
    if let one::two::twos := str.toString.trimRight.splitOn "\n\n" then
      let rest := two::twos
      let mut rgs : Array String.Range := #[]
      let mut currOffset := str.startPos + one.endPos + ⟨1⟩
      for r in rest do
        rgs := rgs.push ⟨currOffset, currOffset⟩
        currOffset := currOffset + r.endPos + ⟨2⟩
      for r in rgs do
        if allowedRanges.any fun okRg => okRg.start ≤ r.start && r.stop ≤ okRg.stop then
          continue
        Linter.logLint linter.style.emptyLine (.ofRange r)
          m!"Please, write a comment here or remove this line, \
            but do not place empty lines within commands!"

initialize addLinter emptyLineLinter

end EmptyLine

end Mathlib.Linter
