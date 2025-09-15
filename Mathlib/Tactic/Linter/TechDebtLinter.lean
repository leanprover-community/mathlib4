import Lean.Elab.Command
import Batteries.Tactic.Alias
import Mathlib.Tactic.AdaptationNote
/-!
#  The "techDebtLinter" linter

The "techDebtLinter" linter reports constructs that are considered to be technical debt.

It is `false` by default, but once a week all of `mathlib` is build with the linter option set to
`true` and the outcome is posted to Zulip.
-/

open Lean Elab Command Linter

namespace Mathlib.Linter

/-- The "techDebtLinter" linter reports constructs that are considered to be technical debt. -/
register_option linter.techDebtLinter : Bool := {
  defValue := true
  descr := "enable the techDebtLinter linter"
}

namespace TechDebtLinter

partial
def getDebts : Syntax → CommandElabM (Array Syntax)
  | s@(.node _ kind args) => do
    let rargs ← args.flatMapM getDebts
    match kind with
    | ``Parser.Command.set_option =>
      let optionName := s[1].getId
      let optionString := s[1].getId.toString
      if 2 ≤ (optionString.splitOn "backward").length ||
        2 ≤ (optionString.splitOn "tactic.skipAssignedInstances").length ||
        2 ≤ (optionString.splitOn "maxHeartbeats").length ||
        2 ≤ (optionString.splitOn "linter.deprecated").length
      then
        return rargs.push s
      else
        return rargs
    | ``«tactic#adaptation_note_» | ``adaptationNoteCmd
    | ``Parser.Tactic.tacticErw___
    -- We accumulate `deprecated` attributes, since setting the `linter.deprecated` to `false` for a
    -- `deprecated` declaration should not be counted as technical debt.
    | ``deprecated =>
      return rargs.push s
    | ``Parser.Command.open =>
      if s.find? (#[`Fin.CommRin, `Fin.NatCast].contains ·.getId) |>.isSome then
        return rargs.push s
      else
        return rargs
    | ``Batteries.Tactic.Lint.nolint =>
      let attrName := s[1][0].getId
      if attrName == `simpNF
      then
        return rargs.push s
      else
        return rargs
    | _ =>
      return rargs
  | .atom .. => pure #[]
  | .ident .. => pure #[]
  | .missing => pure #[]

/-
Count
`set_option linter.deprecated false` outside of `Mathlib/Deprecated`
do not count
`set_option linter.deprecated false in ... @[deprecated ...]` outside of `Mathlib/Deprecated`
-/

open Lean Elab Command in
elab "td " cmd:command : command => do
  elabCommand cmd
  let debt ← getDebts cmd
  logInfo m!"{debt.size}: {debt}"
  --logInfo m!"{cmd}"

@[inherit_doc Mathlib.Linter.linter.techDebtLinter]
def techDebtLinterLinter : Linter where run stx := do
  unless Linter.getLinterValue linter.techDebtLinter (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let debt ← getDebts stx
  if debt.isEmpty then
    return
  Linter.logLint linter.techDebtLinter stx  m!"{debt.size}: {debt}"

initialize addLinter techDebtLinterLinter

end TechDebtLinter

end Mathlib.Linter
