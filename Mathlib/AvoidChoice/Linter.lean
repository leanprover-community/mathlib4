/-
This file has been written essentially ba Damiano Testa.
-/

import Lean.Util.CollectAxioms
import Mathlib.Tactic.DeclarationNames
import Mathlib.Init

/-!
#  The "detectClassical" linter

The "detectClassical" linter emits a warning on declarations that depend on the `Classical.choice`
and/or `sorryAx`.
-/

open Lean Elab Linter Command

namespace Mathlib.Linter

/--
The "detectClassical" linter emits a warning on declarations that depend on the `Classical.choice`
axiom.
-/
register_option linter.detectClassical : Bool := {
  defValue := true
  descr := "enable the detectClassical linter"
}

namespace DetectClassical

@[inherit_doc Mathlib.Linter.linter.detectClassical]
def detectClassicalLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.detectClassical (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let nms := (← getNamesFrom (stx.getPos?.getD default)).filter (! ·.getId.isInternal)
  for constStx in nms do
    let constName := constStx.getId
    let axioms ← collectAxioms constName
    if !axioms.contains `Classical.choice && !axioms.contains `sorryAx then return
    else
      if !axioms.contains `Classical.choice then
        Linter.logLint linter.detectClassical constStx m!"'{constName}' depends on 'sorry'.\n"
      else
      if !axioms.contains `sorryAx then
        Linter.logLint linter.detectClassical constStx m!"'{constName}' depends on 'choice'.\n"
      else Linter.logLint linter.detectClassical constStx m!"'{constName}' depends on
        'sorry and choice'.\n"

initialize addLinter detectClassicalLinter

end DetectClassical

end Mathlib.Linter
