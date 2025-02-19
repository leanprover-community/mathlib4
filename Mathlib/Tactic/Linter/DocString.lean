import Lean.Elab.Command

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
  let some docStx := stx.find? (·.isOfKind `Lean.Parser.Command.docComment) | return
  let docString ← getDocStringText ⟨docStx⟩
  -- `startSubstring` is only needed if you want to keep track of the whitespace between
  -- `/--` and the doc-string
  let startSubstring := match docStx with
    | .node _ _ #[(.atom si ..), _] => si.getTrailing?.getD default
    | _ => default
  let start := startSubstring.toString
  dbg_trace "'{start}{docString}'"
  --Linter.logLint linter.style.docString docStx m!"Something is unformatted here?"

initialize addLinter docStringLinter

end Style

end Mathlib.Linter
