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
# A linter for long commands

The `linter.longDeclaration` linter warns when a command contains more than 200
lines of code. The bound is configurable with `linter.longDeclaration.maxLines`.

Blank lines and lines consisting entirely of comments are excluded. Multiline tokens, such as
string literals, contribute all their lines, including blank lines within them. Only original
source ranges are checked, and commands with errors are skipped.

The linter inspects the source syntax of every command. For declarations, the entire written
statement and body count, including explicit hypotheses, attached `where` definitions and
termination hints. Hypotheses introduced by separate `variable` commands do not contribute to
subsequent declarations (but the `variable` command itself may raise a warning if it is over the
length limit). Mutual blocks and custom commands are checked in the same way.
-/

meta section

/-- Enable warnings for commands exceeding the code-line limit. -/
public register_option linter.longDeclaration : Bool := {
  defValue := false
  descr := "enable the `longDeclaration` linter"
}

/-- Maximum number of lines of code allowed in a command. -/
public register_option linter.longDeclaration.maxLines : Nat := {
  defValue := 200
  descr := "maximum number of lines of code in a command"
}

namespace Mathlib.Linter.LongDeclaration

open Lean Elab Command

/-- Add every source line touched by the half-open range `range` to `lines`. -/
def addSourceLines (fileMap : FileMap) (range : Syntax.Range)
    (lines : Std.HashSet Nat) : Std.HashSet Nat := Id.run do
  -- Certain syntax nodes, e.g. `hygieneInfo`, have empty ranges; skip these.
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
partial def sourceLines (fileMap : FileMap) (stx : Syntax)
    (lines : Std.HashSet Nat) : Std.HashSet Nat := Id.run do
  match stx with
  | .node _ kind args =>
    -- Documentation comments are syntax nodes, so skip them explicitly.
    if kind == ``Parser.Command.docComment || kind == ``Parser.Command.moduleDoc then
      return lines
    return args.foldl (init := lines) fun lines arg ↦ sourceLines fileMap arg lines
  | .atom (.original _ pos _ endPos) _
  | .ident (.original _ pos _ endPos) .. =>
    return addSourceLines fileMap ⟨pos, endPos⟩ lines
  -- Synthetic and missing tokens do not describe code written in the source file.
  | _ => return lines

/-- Count all source lines touched by `range`, as a cheap upper bound on the code-line count. -/
def sourceLineCount (fileMap : FileMap) (range : Syntax.Range) : Nat :=
  let first := fileMap.toPosition range.start
  let last := fileMap.toPosition range.stop
  -- Source ranges have exclusive ends, so an end at column zero belongs to the preceding line.
  let stop := last.line + if last.column == 0 then 0 else 1
  stop - first.line

/-- Check commands using source syntax only, respecting command-local options.
Short commands return before collecting token lines; no elaboration info trees are needed. -/
def checkLongDeclarations : Linter where
  run := withSetOptionIn fun stx => do
    unless Lean.Linter.getLinterValue linter.longDeclaration (← Lean.Linter.getLinterOptions) do
      return
    if (← get).messages.hasErrors then return
    let fileMap ← getFileMap
    let limit := linter.longDeclaration.maxLines.get (← getOptions)
    -- Raw source length is an upper bound, so most commands need no syntax traversal at all.
    let some range := stx.getRange? true | return
    if sourceLineCount fileMap range ≤ limit then return
    let lines := (sourceLines fileMap stx {}).size
    if lines > limit then
      Lean.Linter.logLint linter.longDeclaration (.ofRange range)
        m!"This command contains {lines} lines of code, exceeding the limit of {limit}. \
          Consider extracting helper definitions or lemmas."

-- Register the callback when this module is imported; its option controls whether it runs.
initialize addLinter checkLongDeclarations

end Mathlib.Linter.LongDeclaration
