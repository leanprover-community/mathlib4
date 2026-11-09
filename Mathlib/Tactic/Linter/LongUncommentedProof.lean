/-
Copyright (c) 2026 Felix Pernegger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Pernegger
-/
module

public meta import Lean.Elab.Command
public import Mathlib.Init
public import Mathlib.Lean.Linter

/-!
# The "longUncommentedProof" linter

The "longUncommentedProof" linter emits a warning on declaration bodies (e.g. proofs) which
contain at least `linter.style.longUncommentedProof.minLines` lines of code (100 by default),
but fewer than `linter.style.longUncommentedProof.minComments` lines containing a comment
(10 by default).

* A *line of code* is a line of the body containing a non-whitespace character of a token:
  blank lines and lines consisting entirely of comments do not count.
* A *commented line* is a line of the body containing a non-whitespace character of a comment,
  possibly after code. Doc-comments, e.g. of auxiliary declarations in a `where` clause, count as
  comments.

The body of a declaration starts at its `:=` (resp. its first `|` or `where`) and ends at the end
of the line containing its last token. Comments outside of the body, e.g. in the doc-string of the
declaration, do not count. The line on which the body starts is only counted as a line of code if
nothing precedes the body on that line.
Declarations in quotations, e.g. on the right-hand side of a `macro`, are not linted.
The linter is purely syntactic and does not inspect info trees.

The linter is not imported in `Mathlib.Init`: to use it, import
`Mathlib.Tactic.Linter.LongUncommentedProof` and set `linter.style.longUncommentedProof` to `true`.
-/

meta section

open Lean Elab Command Linter

namespace Mathlib.Linter

/--
The "longUncommentedProof" linter emits a warning on declaration bodies which contain at least
`linter.style.longUncommentedProof.minLines` lines of code, but fewer than
`linter.style.longUncommentedProof.minComments` lines containing a comment.
-/
public register_option linter.style.longUncommentedProof : Bool := {
  defValue := false
  descr := "enable the longUncommentedProof linter"
}

/-- Declaration bodies with at least this many lines of code are checked by the
`longUncommentedProof` linter. -/
public register_option linter.style.longUncommentedProof.minLines : Nat := {
  defValue := 100
  descr := "minimal number of lines of code of a declaration body linted by longUncommentedProof"
}

/-- The number of commented lines that the `longUncommentedProof` linter expects in long bodies. -/
public register_option linter.style.longUncommentedProof.minComments : Nat := {
  defValue := 10
  descr := "minimal number of commented lines expected by the longUncommentedProof linter"
}

namespace LongUncommentedProof

/-- The `SyntaxNodeKind`s of declaration bodies. -/
def bodyKinds : Array SyntaxNodeKind :=
  #[``Parser.Command.declValSimple, ``Parser.Command.declValEqns,
    ``Parser.Command.whereStructInst]

/-- Add to `res` the declaration bodies in `stx` outside of quotations, each together with the
syntax on which to report: the name of the declaration if it has one, otherwise the first token of
the body. Here `name` is the name of the enclosing declaration, if already known. -/
partial def bodies (stx : Syntax) (name : Option Syntax := none)
    (res : Array (Syntax × Syntax) := #[]) : Array (Syntax × Syntax) := Id.run do
  if stx.isQuot then return res
  let mut name := name
  let mut res := res
  for arg in stx.getArgs do
    if bodyKinds.contains arg.getKind then
      res := res.push ((name <|> arg.getHead?).getD arg, arg)
    else
      -- The name of a declaration precedes its body, possibly inside an `optional` node.
      if arg.isOfKind ``Parser.Command.declId then name := arg
      else if arg[0].isOfKind ``Parser.Command.declId then name := arg[0]
      res := bodies arg name res
  return res

/-- Add the lines containing a non-whitespace character of the source between `start` and
`stop` to `lines`. -/
def addLines (fm : FileMap) (start stop : String.Pos.Raw) (lines : Std.HashSet Nat) :
    Std.HashSet Nat :=
  (Substring.Raw.foldl (init := ((fm.toPosition start).line, lines)) (fun (line, lines) c ↦
    if c == '\n' then (line + 1, lines)
    else if c.isWhitespace then (line, lines)
    else (line, lines.insert line)) ⟨fm.source, start, stop⟩).2

/-- Collect the lines of code and the commented lines of `stx`, ignoring everything from `stop`
on. The flag `inDoc` indicates that `stx` is part of a doc-comment. -/
partial def collectLines (fm : FileMap) (stop : String.Pos.Raw) (inDoc : Bool) (stx : Syntax)
    (acc : Std.HashSet Nat × Std.HashSet Nat) : Std.HashSet Nat × Std.HashSet Nat :=
  let (code, comments) := acc
  match stx with
  | .node _ kind args =>
    let inDoc := inDoc || kind == ``Parser.Command.docComment
    args.foldl (fun acc arg ↦ collectLines fm stop inDoc arg acc) acc
  | .atom (.original _ pos trailing endPos) _
  | .ident (.original _ pos trailing endPos) .. =>
    -- The trailing whitespace of a token consists of whitespace and comments only.
    let comments :=
      addLines fm trailing.startPos (if trailing.stopPos ≤ stop then trailing.stopPos else stop)
        comments
    if inDoc then (code, addLines fm pos endPos comments)
    else (addLines fm pos endPos code, comments)
  | _ => acc

@[inherit_doc Mathlib.Linter.linter.style.longUncommentedProof]
def longUncommentedProofLinter : Linter where
  run := whenLinterActivated linter.style.longUncommentedProof fun stx ↦ do
    let minLines := linter.style.longUncommentedProof.minLines.get (← getOptions)
    let minComments := linter.style.longUncommentedProof.minComments.get (← getOptions)
    let fm ← getFileMap
    -- Most commands are short: skip them without traversing their syntax.
    let some range := stx.getRange? | return
    if (fm.toPosition range.stop).line + 1 - (fm.toPosition range.start).line < minLines then
      return
    for (ref, body) in bodies stx do
      let (some start, some tail) := (body.getPos?, body.getTailPos?) | continue
      let startLine := (fm.toPosition start).line
      let tailLine := (fm.toPosition tail).line
      if tailLine + 1 - startLine < minLines then continue
      -- A comment after the last token of the body still counts if it starts on the same line.
      let (code, comments) := collectLines fm (fm.lineStart (tailLine + 1)) false body ({}, {})
      -- The line on which the body starts belongs to the statement if it contains code before.
      let code :=
        if (Substring.Raw.mk fm.source (fm.lineStart startLine) start).all (·.isWhitespace) then
          code
        else code.erase startLine
      if minLines ≤ code.size && comments.size < minComments then
        logLint linter.style.longUncommentedProof ref
          m!"This declaration body has {code.size} lines of code but only {comments.size} \
            commented lines; at least {minComments} are expected. Consider explaining the \
            argument in comments or splitting off auxiliary lemmas."

initialize addLinter longUncommentedProofLinter

end Mathlib.Linter.LongUncommentedProof
