/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Tactic.Linter.PPRoundtrip

/-!
#  The "commandStart" linter

The "commandStart" linter emits a warning if
* a command does not start at the beginning of a line;
* the "hypotheses segment" of a declaration does not coincide with its pretty-printed version.
-/

open Lean Elab Command

namespace Mathlib.Linter

/--
The "commandStart" linter emits a warning if
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

def removeComments (s : String) : String :=
  let lines := s.splitOn "\n"
  let lines := lines.filterMap fun l =>
    -- remove lines that begin with a comment
    if (l.trim.startsWith "--") || (l.trim.startsWith "/-" && l.trim.get ⟨2⟩ != '-') then none
    -- remove the text in a line, starting from the beginning `--`
    else if let st::_ := l.splitOn "--" then
      -- FIXME! make sure that we do not truncate a doc-string!
      --if st.back == '/' then some l else some
       st.trimLeft
    else some l
  "\n".intercalate lines
/-
#eval do
  let s := "Hi\n  -- this is a comment\nthere there is some -- another comment -- with more\ntext"
  IO.println <| removeComments s
-/

def furtherFormatting (s : String) : String :=
  s |>.replace "¬ " "¬"
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
  `termπ__, `«term_#_»]

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
      if let some pos := stype.getPos? then
        if pos.1 ≤ finalLintPos.1 then
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
        m!"real:\n'{real}'\n\n\
          real formatted:\n'{furtherFormatting (removeComments real)}'\n\n\
          comparison:\n'{st}'\n\n\
          format:\n'{fmt}'\n"
      if ! st.startsWith (furtherFormatting (removeComments real)) then
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
