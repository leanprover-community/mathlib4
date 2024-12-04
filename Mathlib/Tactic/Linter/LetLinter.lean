/-
Copyright (c) 2024 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Adomas Baliuka
-/
import Lean.Elab.Command

namespace Mathlib.Linter

/-- The admit linter emits a warning on usages of `let`. -/
register_option linter.let : Bool := {
  defValue := true
  descr := "enable the let linter"
}

namespace LetLinter

open Lean Elab

partial
def getLet (stx : Syntax) : Array Syntax :=
  if stx.getKind == ``Lean.Parser.Term.let then
    #[stx]
  else
    stx.foldArgs (fun arg r => r ++ getLet arg) #[]

def letLinter : Linter where run := withSetOptionIn fun stx => do
  unless Linter.getLinterValue linter.let (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  for stxLet in getLet stx do
    Linter.logLint linter.let stxLet
      "Detected a `let` expression."

initialize addLinter letLinter

end LetLinter
end Mathlib.Linter
