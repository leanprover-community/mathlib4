/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public meta import Mathlib.Lean.String
public meta import Lean.Elab.Command

public meta section

/-- Check that each line begins with an even number of spaces. -/
register_option linter.oddIndent : Bool := {
  descr := "Check that each line begins with an even number of spaces."
  defValue := true }

open Lean

@[inherit_doc linter.oddIndent]
def oddIndent : Linter where run stx := do
  unless stx.isOfKind ``Parser.Command.eoi do return
  unless Linter.getLinterValue linter.oddIndent (← Linter.getLinterOptions) do return
  let source := (← getFileMap).source.toSlice
  for pos in (← getFileMap).positions do
    let startPos := source.pos! pos
    let endPos := startPos.skipWhile ' '
    -- We can use `byteIdx` since `' '` is one byte.
    unless (endPos.offset.byteIdx - startPos.offset.byteIdx) % 2 == 0 do
      let range := Syntax.ofRange ⟨startPos.offset, endPos.offset⟩
      logWarningAt range m!"This line begins with an odd number of spaces. \
        Please add or remove a space to make it even."

initialize addLinter oddIndent
