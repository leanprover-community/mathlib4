/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Tactic.Linter.PPRoundtrip

/-!
#  The `commandStart` linter

The `commandStart` linter emits a warning if
* a command does not start at the beginning of a line;
* the "hypotheses segment" of a declaration does not coincide with its pretty-printed version.
-/

open Lean Elab Command

namespace Mathlib.Linter

/--
The `commandStart` linter emits a warning if
* a command does not start at the beginning of a line;
* the "hypotheses segment" of a declaration does not coincide with its pretty-printed version.

In practice, this makes sure that the spacing in a typical declaration look like
```lean
example (a : Nat) {R : Type} [Add R] : <not linted part>
```
as opposed to
```lean
example (a: Nat) {R:Type}  [Add  R] : <not linted part>
```
-/
register_option linter.style.commandStart : Bool := {
  defValue := true
  descr := "enable the commandStart linter"
}

register_option linter.style.commandStart.verbose : Bool := {
  defValue := false
  descr := "enable the commandStart linter"
}

/-- `lintUpTo stx` returns the position up until the `commandStart` linter checks the formatting.
This is every declaration until the type-specification, if there is one, or the value,
as well as all `variable` commands.
-/
def lintUpTo (stx : Syntax) : Option String.Pos :=
  if let some cmd := stx.find? (·.isOfKind ``Lean.Parser.Command.declaration) then
    match cmd.find? (·.isOfKind ``Lean.Parser.Term.typeSpec) with
      | some s => s.getPos?
      | none => match cmd.find? (·.isOfKind ``Lean.Parser.Command.declValSimple) with
        | some s => s.getPos?
        | none => none
  else if stx.isOfKind ``Lean.Parser.Command.variable then
    stx.getTailPos?
  else none

/--
Returns the pair consisting of
* longest initial segment of `s` that does not contain `pattern` as a substring;
* the rest of the string `s`.

In particular, concatenating the two factors yields `s`.
-/
partial
def findString (s pattern : String) : String × String :=
  if pattern.isEmpty then (s, pattern) else
  if s.length < pattern.length then (s, pattern) else
  let candidatePos := s.find ("".push · == pattern.take 1)
  let notContains := {s.toSubstring with stopPos := candidatePos}.toString
  let rest := {s.toSubstring with startPos := candidatePos}.toString
  --dbg_trace "notContains: '{notContains}' vs '{s.take candidatePos.1}'\nrest: '{rest}'"
  if rest.startsWith pattern then
    (notContains, rest)
  else
    let (init, tail) := findString (rest.drop 1) pattern
    (notContains.push (pattern.get ⟨0⟩) ++ init, tail)

/--
`TrimComments s` eliminates comments from `s`, disregarding nesting.

If `compressDocs` is `true`, then it also compresses doc-strings that might be present in `s`,
by collapsing consecutive sequences of at least one space into a single space.
-/
partial
def trimComments (s : String) (compressDocs : Bool) : String :=
  if s.length ≤ 1 then s else
  let (beforeFirstDash, rest) := findString s "-"
  if rest.length ≤ 1 then s else
  match beforeFirstDash.takeRight 1, (rest.take 2).drop 1 with
  | "/", "-" => -- this is a doc-string
    --dbg_trace "rest before: '{rest}'\n"
    let (takeDocs, rest) := findString (rest.drop 2) "-/"
    --dbg_trace "doc '{beforeFirstDash.back}--{takeDocs}'\n\nrest: {rest}"
    let finalDocs :=
      -- Replace each consecutive group of at least one space in `takeDocs` with a single space.
      -- The begin/end `|`-markers take care of preserving initial and terminal spaces, if there
      -- are any.  We remove them in the next step.
      if compressDocs then
        let intermediate := ("|" ++ takeDocs ++ "|").splitOn " " |>.filter (!·.isEmpty)
        " ".intercalate intermediate |>.drop 1 |>.dropRight 1
      else
        takeDocs
    beforeFirstDash ++ "--" ++ finalDocs ++ trimComments rest compressDocs
  | "/", _ => -- this is a multiline comment
    --dbg_trace "multiline comment '{beforeFirstDash}'"
    let (_comment, rest) := findString (rest.drop 2) "-/"
    --let rest := if rest.startsWith "-/" then rest.drop 2 else rest
    (beforeFirstDash.dropRight 1).trimRight ++ trimComments (rest.drop 2) compressDocs
  | _, "-" => -- this is a single line comment
    --dbg_trace "comment"
    let dropComment := rest.dropWhile (· != '\n')
    beforeFirstDash.trimRight ++ trimComments dropComment compressDocs
  | _, _ => beforeFirstDash ++ "-" ++ trimComments (rest.drop 1) compressDocs

/--
These are some replacements that we do to align the input syntax with the pretty-printed one,
mostly in cases where there is not real rule for what style to use.
-/
def furtherFormatting (s : String) : String :=
  s |>.replace "¬ " "¬"
               -- https://github.com/leanprover-community/aesop/pull/203/files
    |>.replace "aesop (rule_sets" "aesop(rule_sets"
    |>.replace " Prop." " «Prop»."
    |>.replace " Type." " «Type»."

namespace Style.CommandStart

/--
`unlintedNodes` contains the `SyntaxNodeKind`s for which there is no clear formatting preference:
if they appear in surface syntax, the linter will ignore formatting.

Currently, the unlined nodes are mostly related to `Subtype`, `Set` and `Finset` notation and
list notation.
-/
abbrev unlintedNodes := #[``«term_::_», ``«term{_:_//_}», `«term{_}», `Mathlib.Meta.setBuilder,
  `Bundle.termπ__, `Finset.«term_#_»]

@[inherit_doc Mathlib.Linter.linter.style.commandStart]
def commandStartLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.style.commandStart (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  -- If a command does not start on the first column, emit a warning.
  if let some pos := stx.getPos? then
    let colStart := ((← getFileMap).toPosition pos).column
    if colStart ≠ 0 then
      Linter.logLint linter.style.commandStart stx
        m!"'{stx}' starts on column {colStart}, \
          but all commands should start at the beginning of the line."
  -- We only lint up to the position given by `lintUpTo`
  if let some finalLintPos := lintUpTo stx then
    if let some stype := stx.find? (unlintedNodes.contains ·.getKind) then
      Linter.logLintIf linter.style.commandStart.verbose (stx.getHead?.getD stx)
        m!"Found '{stype.getKind}' in '{stype}'"
      if let some pos := stype.getPos? then
        if pos ≤ finalLintPos then
          return
    let stx := capSyntax stx finalLintPos.1
    let origSubstring : Substring := {stx.getSubstring?.getD default with stopPos := finalLintPos}
    let (real, lths) := polishSource origSubstring.toString
    let fmt : Option Format := ←
        try
          liftCoreM <| PrettyPrinter.ppCategory `command stx
        catch _ =>
          Linter.logLintIf linter.style.commandStart.verbose (stx.getHead?.getD stx)
            m!"The `commandStart` linter had some parsing issues: \
              feel free to silence it and report this error!"
          return none
    if let some fmt := fmt then
      let st := polishPP fmt.pretty
      Linter.logLintIf linter.style.commandStart.verbose (stx.getHead?.getD stx)
        m!"slightly polished source:\n'{real}'\n\n\
          actually used source:\n'{furtherFormatting (trimComments real true)}'\n\n\
          reference formatting:\n'{st}'\n\n\
          intermediate reference formatting:\n'{fmt}'\n"
      if ! st.startsWith (furtherFormatting (trimComments real true)) then
        let diff := real.firstDiffPos st
        let pos := posToShiftedPos lths diff.1 + origSubstring.startPos.1
        let f := origSubstring.str.drop (pos)
        let extraLth := (f.takeWhile (· != st.get diff)).length
        let srcCtxt := zoomString real diff.1 5
        let ppCtxt  := zoomString st diff.1 5
        Linter.logLint linter.style.commandStart (.ofRange ⟨⟨pos⟩, ⟨pos + extraLth + 1⟩⟩)
          m!"Current syntax:  '{srcCtxt}'\nExpected syntax: '{ppCtxt}'\n"

initialize addLinter commandStartLinter

end Style.CommandStart

end Mathlib.Linter
