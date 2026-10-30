/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

module

public meta import Lean.Elab.Command
public import Lean.Linter.Init
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public import Mathlib.Tactic.Linter.Header  -- shake: keep

meta import Lean.Linter.Basic

/-!
# A linter for long declarations

The `linter.longDeclaration` linter warns when a declaration contains more than 200
lines of code. The bound is configurable with `linter.longDeclaration.maxLines`.

Blank lines and lines consisting entirely of comments are excluded. Multiline tokens, such as
string literals, contribute all their lines, including blank lines within them. Only original
source ranges are checked, and commands with errors are skipped.

The linter inspects syntax only: theorems, lemmas, definitions, abbreviations, opaque declarations,
axioms, instances and examples are treated alike. The entire written declaration counts, including
its statement, explicit hypotheses, attached `where` definitions and termination hints. Hypotheses
introduced by separate `variable` commands do not count. Nested declarations are not reported
separately. Mutual blocks and custom declaration commands are not handled specially.
-/

meta section

/-- Enable warnings for declarations exceeding the code-line limit. -/
public register_option linter.longDeclaration : Bool := {
  defValue := true
  descr := "enable the `longDeclaration` linter"
}

/-- Maximum number of lines of code allowed in a declaration. -/
public register_option linter.longDeclaration.maxLines : Nat := {
  defValue := 200
  descr := "maximum number of lines of code in a declaration"
}

namespace Mathlib.Linter.LongDeclaration

open Lean Elab Command

/-- Add every source line touched by the half-open range `range` to `lines`. -/
private def addSourceLines (fileMap : FileMap) (range : Syntax.Range)
    (lines : Std.HashSet Nat) : Std.HashSet Nat := Id.run do
  if range.stop ≤ range.start then return lines
  let first := (fileMap.toPosition range.start).line
  let last := fileMap.toPosition range.stop
  -- A range ending at the start of a line does not include that line.
  let stop := last.line + if last.column == 0 then 0 else 1
  let mut lines := lines
  for line in [first:stop] do
    lines := lines.insert line
  return lines

/-- Collect the lines containing original code tokens in `stx`.

Leading and trailing whitespace and comments are outside the token ranges. Multiline tokens,
including string literals, contribute all their lines as code.
-/
private partial def sourceLines (fileMap : FileMap) (stx : Syntax)
    (lines : Std.HashSet Nat) : Std.HashSet Nat := Id.run do
  match stx with
  | .node _ kind args =>
    -- Documentation comments are syntax nodes, so skip them explicitly.
    if kind == ``Parser.Command.docComment || kind == ``Parser.Command.moduleDoc then
      return lines
    let mut lines := lines
    for arg in args do
      lines := sourceLines fileMap arg lines
    return lines
  | .atom (.original _ pos _ endPos) _
  | .ident (.original _ pos _ endPos) .. =>
    return addSourceLines fileMap ⟨pos, endPos⟩ lines
  -- Synthetic and missing tokens do not describe code written in the source file.
  | _ => return lines

/-- Count all source lines touched by `range`, as a cheap upper bound on the code-line count. -/
private def sourceLineCount (fileMap : FileMap) (range : Syntax.Range) : Nat :=
  let first := fileMap.toPosition range.start
  let last := fileMap.toPosition range.stop
  -- Source ranges have exclusive ends, so an end at column zero belongs to the preceding line.
  let stop := last.line + if last.column == 0 then 0 else 1
  stop - first.line

/-- Check declarations using source syntax only, respecting command-local options.
Short declarations return before collecting token lines; no elaboration info trees are needed. -/
private def checkLongDeclarations : Syntax → CommandElabM Unit := withSetOptionIn fun stx => do
  unless Lean.Linter.getLinterValue linter.longDeclaration (← Lean.Linter.getLinterOptions) do return
  if (← get).messages.hasErrors then return
  unless stx.isOfKind ``Parser.Command.declaration || stx.isOfKind `lemma do return
  let fileMap ← getFileMap
  let limit := linter.longDeclaration.maxLines.get (← getOptions)
  -- Raw source length is an upper bound, so most commands need no syntax traversal at all.
  let some range := stx.getRange? true | return
  if sourceLineCount fileMap range ≤ limit then return
  let lines := (sourceLines fileMap stx {}).size
  if lines > limit then
    Lean.Linter.logLint linter.longDeclaration (.ofRange range)
      m!"This declaration contains {lines} lines of code, exceeding the limit of {limit}. \
        Consider extracting helper definitions or lemmas."

-- Register the callback when this module is imported; its option controls whether it runs.
initialize addLinter { name := `Mathlib.Linter.longDeclaration, run := checkLongDeclarations }

end Mathlib.Linter.LongDeclaration
