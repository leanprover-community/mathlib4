/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Damiano Testa
-/

import Mathlib.Tactic.Linter.Header

/-!
# The "DocString" style linter

The "DocString" linter validates style conventions regarding doc-string formatting.
-/

open Lean Elab Linter

namespace Mathlib.Linter

/--
The "DocString" linter validates style conventions regarding doc-string formatting.
-/
register_option linter.style.docString : Bool := {
  defValue := false
  descr := "enable the style.docString linter"
}

/--
The "empty doc string" warns on empty doc-strings.
-/
register_option linter.style.docString.empty : Bool := {
  defValue := true
  descr := "enable the style.docString.empty linter"
}

/--
Extract all `declModifiers` from the input syntax. We later extract the `docstring` from it,
but we avoid extracting directly the `docComment` node, to skip `#adaptation_note`s.
-/
def getDeclModifiers : Syntax → Array Syntax
  | s@(.node _ kind args) =>
    (if kind == ``Parser.Command.declModifiers then #[s] else #[]) ++ args.flatMap getDeclModifiers
  | _ => #[]

/--
Currently, this function simply removes `currIndent` spaces after each `\n`
in the input string `docString`.

If/when the `docString` linter expands, it may take on more string processing.
-/
def deindentString (currIndent : Nat) (docString : String) : String :=
  let indent : String := ⟨'\n' :: List.replicate currIndent ' '⟩
  docString.replace indent " "

namespace Style

@[inherit_doc Mathlib.Linter.linter.style.docString]
def docStringLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless getLinterValue linter.style.docString (← getLinterOptions) ||
      getLinterValue linter.style.docString.empty (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let fm ← getFileMap
  for declMods in getDeclModifiers stx do
    -- `docStx` extracts the `Lean.Parser.Command.docComment` node from the declaration modifiers.
    -- In particular, this ignores parsing `#adaptation_note`s.
    let docStx := declMods[0][0]

    let some pos := docStx.getPos? | continue
    let currIndent := fm.toPosition pos |>.column

    if docStx.isMissing then continue -- this is probably superfluous, thanks to `some pos` above.
    -- `docString` contains e.g. trailing spaces before the `-/`, but does not contain
    -- any leading whitespace before the actual string starts.
    let docString ← try getDocStringText ⟨docStx⟩ catch _ => continue
    if docString.trim.isEmpty then
      Linter.logLintIf linter.style.docString.empty docStx m!"warning: this doc-string is empty"
      continue
    -- `startSubstring` is the whitespace between `/--` and the actual doc-string text.
    let startSubstring := match docStx with
      | .node _ _ #[(.atom si ..), _] => si.getTrailing?.getD default
      | _ => default
    -- We replace all line-breaks followed by `currIndent` spaces with a single space.
    let start := deindentString currIndent startSubstring.toString
    if !#["\n", " "].contains start then
      let startRange := {start := startSubstring.startPos, stop := startSubstring.stopPos}
      Linter.logLintIf linter.style.docString (.ofRange startRange)
        s!"error: doc-strings should start with a single space or newline"

    let deIndentedDocString := deindentString currIndent docString

    let docTrim := deIndentedDocString.trimRight
    let tail := docTrim.length
    -- `endRange` creates an 0-wide range `n` characters from the end of `docStx`
    let endRange (n : Nat) : Syntax := .ofRange
      {start := docStx.getTailPos?.get! - ⟨n⟩, stop := docStx.getTailPos?.get! - ⟨n⟩}
    if docTrim.takeRight 1 == "," then
      Linter.logLintIf linter.style.docString (endRange (docString.length - tail + 3))
        s!"error: doc-strings should not end with a comma"
    if tail + 1 != deIndentedDocString.length then
      Linter.logLintIf linter.style.docString (endRange 3)
        s!"error: doc-strings should end with a single space or newline"

initialize addLinter docStringLinter

end Style

end Mathlib.Linter
