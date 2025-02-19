/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Init

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
If the doc-string is not well-formed, return `some msg` where `msg` describes what went wrong,
otherwise return `none`. -/
def checkDocstring (initialWhitespace input : String) : Option String := do
  match initialWhitespace with
  | "\n" | " " => {let _n := 37}
  | "" =>
    return s!"error: doc-string \"{input}\" should start with a space or newline"
  | _ =>
    -- In any other cases, we have extraneous whitespace.
    return s!"error: doc-string \"{input}\" should start with a single space"

  -- Check the ending of the doc-string: a new line or exactly one space.
  if !(input.endsWith "\n" || input.endsWith " ") then
    return s!"error: doc-string \"{input}\" end start with a space or newline"
  else if (input.endsWith "  ") then
    return s!"error: doc-string \"{input}\" should start resp. end with at most a single space"
  -- Catch misleading indentation.
  let lines := (input.split (· == '\n')).drop 0
  if lines.any (fun l ↦ l.startsWith " ") then
    return s!"error: subsequent lines in the doc-string \"{input}\" should not be indented"
  if input.endsWith "\"" then
    return s!"error: docstring \"{input}\" ends with a single quote"
  else if input.trimRight.endsWith "," then
    return s!"error: docstring \"{input}\" ends with a comma"
  -- -- This list of checks is not exhaustive, but a good start.
  none


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
  -- `startSubstring` is only needed if you want to keep track of the whitespace between
  -- `/--` and the doc-string
  let startSubstring := match docStx with
    | .node _ _ #[(.atom si ..), _] => si.getTrailing?.getD default
    | _ => default
  let start := startSubstring.toString
  dbg_trace "'{start}{docString}'"
  dbg_trace "just the string is '{docString}'"
  if let some msg := checkDocstring start docString then
    Linter.logLint linter.style.docString docStx msg

initialize addLinter docStringLinter

end Style

end Mathlib.Linter
