/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Damiano Testa
-/

import Mathlib.Tactic.Linter.Header

/-!
#  The "DocString" style linter

The "DocString" linter validates style conventions regarding doc-string formatting.
-/

open Lean Elab

namespace Mathlib.Linter

/--
The "DocString" linter validates style conventions regarding doc-string formatting.
-/
register_option linter.style.docString : Bool := {
  defValue := false
  descr := "enable the style.docString linter"
}

namespace Style

/-- Checks whether a declaration docstring `input` conforms to mathlib's style guidelines
(or, at least the syntactically checkable parts).
If the doc-string is not well-formed, return `some messages` where `messages` describe
what went wrong, otherwise return `none`. -/
def checkDocstring (input : String) : Option (Array String) := do
  let mut errors := #[]
  -- Check the ending of the doc-string: a new line or exactly one space.
  if !(input.endsWith "\n" || input.endsWith " ") then
    errors := errors.push s!"error: doc-strings should end with a space or newline"
  else if (input.endsWith "  ") then
    errors := errors.push s!"error: doc-strings should end with at most a single space"
  -- Catch misleading indentation.
  let lines := (input.split (· == '\n')).drop 0
  if lines.any (·.startsWith " ")
    -- For now, we skip cases where a line starts with "* " or "- " as these are probably markdown
    -- code blocks. (We can later try to re-enable some linting there.)
    && !lines.any (fun l ↦ l.startsWith "* " || l.startsWith "- ") then
      errors := errors.push s!"error: subsequent lines in a doc-string should not be indented"
  if input.trimRight.endsWith "\"" then
    errors := errors.push s!"error: docstring \"{input}\" ends with a single quote"
  else if input.trimRight.endsWith "," then
    errors := errors.push s!"error: docstring \"{input}\" ends with a comma"
  -- This list of checks is not exhaustive, but a good start.
  errors

@[inherit_doc Mathlib.Linter.linter.style.docString]
def docStringLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.style.docString (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let some docStx := stx.find? (·.isOfKind `Lean.Parser.Command.docComment) | return
  -- `docString` contains e.g. trailing spaces before the '-/', but does not contain
  -- any leading whitespace before the actual string starts.
  let docString ← getDocStringText ⟨docStx⟩
  -- `startSubstring` is the whitespace between `/--` and the actual doc-string text
  let startSubstring := match docStx with
    | .node _ _ #[(.atom si ..), _] => si.getTrailing?.getD default
    | _ => default
  let start := startSubstring.toString
  if !#["\n", " "].contains start then
    let startRg := {start := startSubstring.startPos, stop := startSubstring.stopPos}
    Linter.logLint linter.style.docString (.ofRange startRg)
      s!"error: doc-strings should start with a space or newline"
  if let some messages := checkDocstring docString then
    for msg in messages do
      Linter.logLint linter.style.docString docStx msg

initialize addLinter docStringLinter

end Style

end Mathlib.Linter
