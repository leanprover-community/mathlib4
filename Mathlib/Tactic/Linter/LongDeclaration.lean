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
# A linter for long declaration bodies

The `linter.longDeclaration` linter warns when a declaration body contains more than 200
non-comment source lines. The bound is configurable with `linter.longDeclaration.maxLines`.

The linter inspects syntax only: theorem and lemma proofs, definitions, abbreviations, opaque
values, instances and examples are treated alike. Declaration headers and trailing comments are
excluded. For equation-style definitions, the body includes the equations and their patterns;
for `where` instances, it starts at `where`. Attached `where` definitions and termination hints
are included in the enclosing body. Nested bodies are not reported separately. Mutual blocks
and custom declaration commands are not handled specially.

Lines consisting entirely of comments are excluded. Blank lines still count, except inside block
comments. Only original source ranges are checked, and commands with errors are skipped.
-/

meta section

/-- Enable warnings for declaration bodies exceeding the non-comment source-line limit. -/
public register_option linter.longDeclaration : Bool := {
  defValue := true
  descr := "enable the `longDeclaration` linter"
}

/-- Maximum number of non-comment source lines allowed in a declaration body. -/
public register_option linter.longDeclaration.maxLines : Nat := {
  defValue := 200
  descr := "maximum number of non-comment source lines in a declaration body"
}

namespace Mathlib.Linter.LongDeclaration

open Lean Elab Command

/-- Update the nesting depth of block comments after scanning one line of token trivia.

The input must consist only of whitespace and comments, as supplied by a token's leading or
trailing source slice. Comment markers inside strings and quoted identifiers therefore never
reach this scanner. -/
private def commentDepthAfter (depth : Nat) : List Char → Nat
  | '/' :: '-' :: cs => commentDepthAfter (depth + 1) cs
  | '-' :: '/' :: cs => commentDepthAfter (depth - 1) cs
  -- Outside a block comment, `--` consumes the rest of the line. Inside one, consume only
  -- the first hyphen so that `--/` still closes the block at its second hyphen.
  | '-' :: '-' :: cs => if depth == 0 then 0 else commentDepthAfter depth ('-' :: cs)
  | _ :: cs => commentDepthAfter depth cs
  | [] => depth

/-- Add the source lines containing comments in a leading or trailing token slice to `lines`.
Blank lines inside block comments are included; blank lines between comments are not. -/
private def addCommentLines (fileMap : FileMap) (str : Substring.Raw)
    (lines : Std.HashSet Nat) : Std.HashSet Nat := Id.run do
  let mut lines := lines
  let mut depth := 0
  let mut lineNumber := (fileMap.toPosition str.startPos).line
  for line in str.toString.splitOn "\n" do
    -- Every non-whitespace character in this slice belongs to a comment. A line that begins
    -- inside a block comment also belongs to that comment, even if it contains only whitespace.
    if depth > 0 || line.toList.any (!·.isWhitespace) then
      lines := lines.insert lineNumber
    depth := commentDepthAfter depth line.toList
    lineNumber := lineNumber + 1
  return lines

/-- Add every source line touched by the half-open range `range` to `lines`. -/
private def addSourceLines (fileMap : FileMap) (range : Syntax.Range)
    (lines : Std.HashSet Nat) : Std.HashSet Nat := Id.run do
  let first := (fileMap.toPosition range.start).line
  let last := fileMap.toPosition range.stop
  -- A range ending at the start of a line does not include that line.
  let stop := last.line + if last.column == 0 then 0 else 1
  let mut lines := lines
  for line in [first:stop] do
    lines := lines.insert line
  return lines

/-- Collect the lines containing original code tokens and comments in `stx`.

The two sets may overlap: a line containing both code and a comment must still count toward
the body length. Multiline tokens, including string literals, contribute all their lines as code.
-/
private partial def sourceLines (fileMap : FileMap) (stx : Syntax)
    (code comments : Std.HashSet Nat) : Std.HashSet Nat × Std.HashSet Nat := Id.run do
  match stx with
  | .node _ kind args =>
    -- Documentation comments are syntax nodes rather than token trivia. Treat the whole node
    -- as a comment instead of recursively classifying its contents as code.
    if kind == ``Parser.Command.docComment || kind == ``Parser.Command.moduleDoc then
      if let some range := stx.getRange? then
        return (code, addSourceLines fileMap range comments)
    let mut code := code
    let mut comments := comments
    for arg in args do
      (code, comments) := sourceLines fileMap arg code comments
    return (code, comments)
  | .atom (.original leading pos trailing endPos) _
  | .ident (.original leading pos trailing endPos) .. =>
    return (addSourceLines fileMap ⟨pos, endPos⟩ code,
      addCommentLines fileMap trailing (addCommentLines fileMap leading comments))
  -- Synthetic and missing tokens do not describe code written in the source file.
  | _ => return (code, comments)

/-- Count the source lines touched by `range`, excluding those in `commentOnly`. -/
private def bodyLineCount (fileMap : FileMap) (commentOnly : Std.HashSet Nat)
    (range : Syntax.Range) : Nat :=
  let first := fileMap.toPosition range.start
  let last := fileMap.toPosition range.stop
  -- Source ranges have exclusive ends, so an end at column zero belongs to the preceding line.
  let stop := last.line + if last.column == 0 then 0 else 1
  stop - first.line - commentOnly.fold (fun n line ↦
    if first.line ≤ line && line < stop then n + 1 else n) 0

/-- Find the body of an ordinary declaration or `lemma`, excluding `:=` but including any
attached `where` definitions and termination hints. Other command forms are skipped. -/
private def declarationBodyRange? (stx : Syntax) : Option Syntax.Range := do
  guard (stx.isOfKind ``Parser.Command.declaration || stx.isOfKind `lemma)
  let value ← stx[1].find? fun arg ↦
    arg.isOfKind ``Parser.Command.declValSimple || arg.isOfKind ``Parser.Command.declValEqns ||
      arg.isOfKind ``Parser.Command.whereStructInst
  let range ← value.getRange? true
  if value.isOfKind ``Parser.Command.declValSimple then
    return ⟨(← value[1].getRange? true).start, range.stop⟩
  return range

/-- Check declaration bodies using source syntax only, respecting command-local options.
Short commands and bodies return before comment scanning; no elaboration info trees are needed. -/
private def checkLongDeclarations : Syntax → CommandElabM Unit := withSetOptionIn fun stx => do
  unless Lean.Linter.getLinterValue linter.longDeclaration (← Lean.Linter.getLinterOptions) do return
  if (← get).messages.hasErrors then return
  let fileMap ← getFileMap
  let limit := linter.longDeclaration.maxLines.get (← getOptions)
  -- Raw source length is an upper bound, so most commands need no syntax traversal at all.
  if let some range := stx.getRange? true then
    if bodyLineCount fileMap {} range ≤ limit then return
  let some range := declarationBodyRange? stx | return
  if bodyLineCount fileMap {} range ≤ limit then return
  let (code, comments) := sourceLines fileMap stx {} {}
  let commentOnly := comments.filter (!code.contains ·)
  let lines := bodyLineCount fileMap commentOnly range
  if lines > limit then
    Lean.Linter.logLint linter.longDeclaration (.ofRange range)
      m!"This declaration body contains {lines} non-comment lines, exceeding the limit of {limit}. \
        Consider extracting helper definitions or lemmas."

-- Register the callback when this module is imported; its option controls whether it runs.
initialize addLinter { name := `Mathlib.Linter.longDeclaration, run := checkLongDeclarations }

end Mathlib.Linter.LongDeclaration
