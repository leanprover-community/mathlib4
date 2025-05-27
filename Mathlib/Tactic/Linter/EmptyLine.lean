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

partial
def filterMapM {m : Type → Type} [Monad m] (stx : Syntax) (f : Syntax → m (Option Syntax)) :
    m (Array Syntax) := do
  let nargs := (← stx.getArgs.mapM (·.filterMapM f)).flatten
  match ← f stx with
    | some new => return nargs.push new
    | none => return nargs

def filterMap (stx : Syntax) (f : Syntax → Option Syntax) : Array Syntax :=
  stx.filterMapM (m := Id) f

def filter (stx : Syntax) (f : Syntax → Bool) : Array Syntax :=
  stx.filterMap (fun s => if f s then some s else none)

end Lean.Syntax

namespace Mathlib.Linter

/--
The "emptyLine" linter emits a warning on empty lines inside a command, but outside of a
doc-string/module-doc.
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

/-- If a file contains one of these names as segments, we disable `EmptyLine` linter. -/
abbrev SkippedFileSegments : Std.HashSet Name := Std.HashSet.emptyWithCapacity
  |>.insert `Tactic
  |>.insert `Util
  |>.insert `Meta

@[inherit_doc Mathlib.Linter.linter.style.emptyLine]
def emptyLineLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.style.emptyLine (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  if !((← getMainModule).components.filter (SkippedFileSegments.contains)).isEmpty then
    return
  -- We ignore empty lines "after" the command finished
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
          m!"Please, do not place empty lines within commands!"

initialize addLinter emptyLineLinter

end EmptyLine

end Mathlib.Linter
