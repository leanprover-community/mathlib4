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

/-- Add comment lines from a token's leading or trailing whitespace and comments.
Lean's parser finds each comment's endpoint, handling nested block comments itself. -/
private def addCommentLines (fileMap : FileMap) (pmctx : Parser.ParserModuleContext)
    (str : Substring.Raw) (lines : Std.HashSet Nat) : Std.HashSet Nat := Id.run do
  let input := fileMap.source
  let ictx := Parser.InputContext.mk input "" (fileMap := fileMap)
  let mut pos := str.startPos
  let mut lines := lines
  while pos < str.stopPos do
    let next := pos.next input
    -- These slices contain no strings or identifiers: any non-whitespace text is a comment.
    let parser? :=
      if pos.get input == '/' && next.get input == '-' then
        some (Parser.finishCommentBlock (pushMissingOnError := false) 1)
      else if pos.get input == '-' && next.get input == '-' then
        some (Parser.takeUntilFn (· == '\n'))
      else none
    if let some parser := parser? then
      -- Both parsers start after the two-character opening marker. Parsing a whole block
      -- gives a range including its interior blank lines, without counting gaps between comments.
      let state := (Parser.mkParserState input).setPos (next.next input)
      let state := parser.run ictx pmctx (Parser.getTokenTable pmctx.env) state
      if state.hasError then return lines
      lines := addSourceLines fileMap ⟨pos, state.pos⟩ lines
      pos := state.pos
    else
      pos := next
  return lines

/-- Collect the lines containing original code tokens and comments in `stx`.

The two sets may overlap: a line containing both code and a comment must still count toward
the body length. Multiline tokens, including string literals, contribute all their lines as code.
-/
private partial def sourceLines (fileMap : FileMap) (pmctx : Parser.ParserModuleContext)
    (stx : Syntax)
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
      (code, comments) := sourceLines fileMap pmctx arg code comments
    return (code, comments)
  | .atom (.original leading pos trailing endPos) _
  | .ident (.original leading pos trailing endPos) .. =>
    return (addSourceLines fileMap ⟨pos, endPos⟩ code,
      addCommentLines fileMap pmctx trailing (addCommentLines fileMap pmctx leading comments))
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
  let pmctx : Parser.ParserModuleContext := { env := ← getEnv, options := ← getOptions }
  let (code, comments) := sourceLines fileMap pmctx stx {} {}
  let commentOnly := comments.filter (!code.contains ·)
  let lines := bodyLineCount fileMap commentOnly range
  if lines > limit then
    Lean.Linter.logLint linter.longDeclaration (.ofRange range)
      m!"This declaration body contains {lines} non-comment lines, exceeding the limit of {limit}. \
        Consider extracting helper definitions or lemmas."

-- Register the callback when this module is imported; its option controls whether it runs.
initialize addLinter { name := `Mathlib.Linter.longDeclaration, run := checkLongDeclarations }

end Mathlib.Linter.LongDeclaration
