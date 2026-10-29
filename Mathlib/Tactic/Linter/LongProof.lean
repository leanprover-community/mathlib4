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

meta import Lean.DeclarationRange
meta import Lean.Elab.InfoTree.Util
meta import Lean.Linter.Basic

/-!
# A linter for long proofs

The `linter.longProof` linter warns when a proof term contains more than 200 non-comment source
lines. The bound is configurable with `linter.longProof.maxLines`.

Length is the inclusive span from the proof's first token (usually `by`) to its last token.
Lines consisting entirely of comments are excluded. Blank lines still count, except inside block
comments. Declaration headers and trailing comments do not count.

Both tactic and term proofs are checked, including proofs in definitions, instances and examples.
Elaborated types distinguish proofs from computations returning data. Proofs elaborated outside
declaration contexts, such as standalone `#check` commands, are not checked.

Only original source terms are checked. Nested overlong proofs produce a single warning on the
outermost overlong proof, rather than repeated warnings on its subproofs. Like other info-tree
linters, this requires elaboration information to be enabled. Commands with errors are skipped.
-/

meta section

/-- Enable warnings for proofs exceeding the non-comment source-line limit. -/
public register_option linter.longProof : Bool := {
  defValue := true
  descr := "enable the `longProof` linter"
}

/-- Maximum number of non-comment source lines allowed in a proof. -/
public register_option linter.longProof.maxLines : Nat := {
  defValue := 200
  descr := "maximum number of non-comment source lines in a proof"
}

namespace Mathlib.Linter.LongProof

open Lean Elab Command

/-- Whether an info tree may contain a long proof, using recorded declaration ranges to skip
short declarations without traversing their bodies. Missing ranges are handled conservatively;
terms outside parent-declaration contexts are ignored. -/
private partial def mayContainLongProof (tree : InfoTree) (limit : Nat) : CommandElabM Bool := do
  match tree with
  | .context (.parentDeclCtx name) _ =>
    let some ranges ← findDeclarationRanges? name | return true
    let range := ranges.range
    -- The recorded range includes the statement and comments, so its length is an upper bound
    -- for every proof inside the declaration. An end at column zero excludes that final line.
    return range.endPos.line - range.pos.line + (if range.endPos.column == 0 then 0 else 1) > limit
  | .context _ tree => mayContainLongProof tree limit
  | .node _ children =>
    for child in children do
      if ← mayContainLongProof child limit then return true
    return false
  | .hole _ => return false

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
the proof length. Multiline tokens, including string literals, contribute all their lines as code.
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
private def proofLineCount (fileMap : FileMap) (commentOnly : Std.HashSet Nat)
    (range : Syntax.Range) : Nat :=
  let first := fileMap.toPosition range.start
  let last := fileMap.toPosition range.stop
  -- Source ranges have exclusive ends, so an end at column zero belongs to the preceding line.
  let stop := last.line + if last.column == 0 then 0 else 1
  stop - first.line - commentOnly.fold (fun n line ↦
    if first.line ≤ line && line < stop then n + 1 else n) 0

/-- Whether the half-open source range `inner` is contained in `outer`, including equality. -/
private def containsRange (outer inner : Syntax.Range) : Bool :=
  outer.start ≤ inner.start && inner.stop ≤ outer.stop

/-- Find the outermost original proof ranges exceeding `limit` in an elaboration info tree.
Proofs are identified by their elaborated types, so tactic blocks returning data are excluded. -/
private def longProofs (tree : InfoTree) (fileMap : FileMap) (commentOnly : Std.HashSet Nat)
    (limit : Nat) : CommandElabM (Array Syntax.Range) :=
  tree.foldInfoM (init := #[]) fun context info ranges => do
    let (stx, isProof) ← match info with
      | .ofTermInfo term =>
        -- A bound proof variable is not a proof body supplied by the author.
        if term.isBinder then return ranges
        pure (term.stx, context.runMetaM term.lctx (Meta.isProof term.expr))
      | .ofTacticInfo tactic =>
        -- Inspect a whole `by` block, rather than each individual tactic. Its initial goal
        -- determines whether the block constructs a proof or data.
        unless tactic.stx.isOfKind ``Parser.Term.byTactic do return ranges
        let goal :: _ := tactic.goalsBefore | return ranges
        -- Restore the goal's original metavariable and local contexts before checking its type.
        let context := { context with mctx := tactic.mctxBefore }
        pure (tactic.stx, context.runMetaM {} (goal.withContext (Meta.isProof (.mvar goal))))
      | _ => return ranges
    unless stx.getHeadInfo matches .original .. do return ranges
    let some range := stx.getRange? | return ranges
    -- Delay the semantic proof check until the cheaper source-length and containment tests pass.
    unless proofLineCount fileMap commentOnly range > limit do return ranges
    if ranges.any (containsRange · range) then return ranges
    unless ← isProof do return ranges
    -- Info-tree traversal can discover an enclosing proof after its subproofs. Replace those
    -- smaller ranges, and also deduplicate identical ranges from different info nodes.
    return (ranges.filter fun inner => !containsRange range inner).push range

/-- Run the long-proof linter for a command, respecting command-local option overrides.
Commands with errors or without elaboration information are skipped. -/
private def checkLongProofs : Syntax → CommandElabM Unit := withSetOptionIn fun stx => do
  unless Lean.Linter.getLinterValue linter.longProof (← Lean.Linter.getLinterOptions) do return
  if (← get).messages.hasErrors || !(← getInfoState).enabled then return
  let fileMap ← getFileMap
  let limit := linter.longProof.maxLines.get (← getOptions)
  -- If the entire command fits, so does every proof inside it, even before removing comments.
  -- Check this before traversing info trees or looking up declaration ranges. Without a
  -- canonical source range, fall through to the existing checks.
  if let some range := stx.getRange? true then
    if proofLineCount fileMap {} range ≤ limit then return
  let trees ← getInfoTrees
  -- Most declarations fit under the limit even before removing comments. Avoid the syntax
  -- traversal and proof classification entirely when all their recorded ranges are short.
  unless ← trees.anyM (mayContainLongProof · limit) do return
  let (code, comments) := sourceLines fileMap stx {} {}
  -- Only lines with comments and no code are free; an inline comment does not exempt its line.
  let commentOnly := comments.filter (!code.contains ·)
  let mut ranges : Array Syntax.Range := #[]
  -- A command can produce several info trees. Enforce the same outermost-range policy across
  -- trees as within each tree, so that each long proof produces just one warning.
  for tree in trees do
    for range in ← longProofs tree fileMap commentOnly limit do
      unless ranges.any (containsRange · range) do
        ranges := (ranges.filter fun inner => !containsRange range inner).push range
  for range in ranges do
    Lean.Linter.logLint linter.longProof (.ofRange range)
      m!"This proof contains {proofLineCount fileMap commentOnly range} non-comment lines, \
        exceeding the limit of {limit}. \
        Consider extracting intermediate results into separate lemmas."

-- Register the callback when this module is imported; its option controls whether it runs.
initialize addLinter { name := `Mathlib.Linter.longProof, run := checkLongProofs }

end Mathlib.Linter.LongProof
