/-
Copyright (c) 2024 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Adomas Baliuka
-/
import Lean.Elab.Command

/-!
# The "admit" linter

The "admit" linter flags usages of the `admit` tactic.

The tactics `admit` and `sorry` are synonyms.
The use of `sorry` is much more common and should be preferred.

This linter is an incentive to discourage uses of `admit`, without being a ban.
-/

namespace Mathlib.Linter

/-- The admit linter emits a warning on usages of `admit`. -/
register_option linter.admit : Bool := {
  defValue := false
  descr := "enable the admit linter"
}

namespace AdmitLinter

open Lean Elab

/-- `getAdmit t` returns all usages of the `admit` tactic in the input syntax `t`. -/
partial
def getAdmit (stx : Syntax) : Array Syntax :=
  if let `(tactic| admit) := stx then
    #[stx]
  else
    stx.foldArgs (fun arg r => r ++ getAdmit arg) #[]

/-- The "admit" linter flags usages of the `admit` tactic.

The tactics `admit` and `sorry` are synonyms.
The use of `sorry` is much more common and should be preferred.
-/
def admitLinter : Linter where run := withSetOptionIn fun stx => do
  unless Linter.getLinterValue linter.admit (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  for stxAdmit in (getAdmit stx) do
    Linter.logLint linter.admit stxAdmit
      "The `admit` tactic is discouraged: please consider using the synonymous `sorry` instead."

initialize addLinter admitLinter

end AdmitLinter
