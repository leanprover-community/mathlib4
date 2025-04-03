/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Damiano Testa
-/

import MathlibLinters.Header

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

@[inherit_doc Mathlib.Linter.linter.style.docString]
def docStringLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.style.docString (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let some declMods := stx.find? (·.isOfKind ``Lean.Parser.Command.declModifiers) | return
  -- `docStx` extracts the `Lean.Parser.Command.docComment` node from the declaration modifiers.
  -- In particular, this ignores parsing `#adaptation_note`s.
  let docStx := declMods[0][0]
  if docStx.isMissing then return
  -- `docString` contains e.g. trailing spaces before the `-/`, but does not contain
  -- any leading whitespace before the actual string starts.
  let docString ← try getDocStringText ⟨docStx⟩ catch _ => return
  -- `startSubstring` is the whitespace between `/--` and the actual doc-string text.
  let startSubstring := match docStx with
    | .node _ _ #[(.atom si ..), _] => si.getTrailing?.getD default
    | _ => default
  let start := startSubstring.toString
  if !#["\n", " "].contains start then
    let startRange := {start := startSubstring.startPos, stop := startSubstring.stopPos}
    Linter.logLint linter.style.docString (.ofRange startRange)
      s!"error: doc-strings should start with a single space or newline"
  let docTrim := docString.trimRight
  let tail := docTrim.length
  -- `endRange` creates an 0-wide range `n` characters from the end of `docStx`
  let endRange (n : Nat) : Syntax := .ofRange
    {start := docStx.getTailPos?.get! - ⟨n⟩, stop := docStx.getTailPos?.get! - ⟨n⟩}
  if docTrim.takeRight 1 == "," then
    Linter.logLint linter.style.docString (endRange (docString.length - tail + 3))
      s!"error: doc-strings should not end with a comma"
  if tail + 1 != docString.length then
    Linter.logLint linter.style.docString (endRange 3)
      s!"error: doc-strings should end with a single space or newline"

initialize addLinter docStringLinter

end Style

end Mathlib.Linter
