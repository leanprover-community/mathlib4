import Lean.Elab.Command
import CFSG.adomaniLeanUtils.inspect_syntax
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

inspect #adaptation_note /-- comment -/

inspect
example : True := by
  #adaptation_note /-- comment -/
  trivial

inspect
set_option backward.dsimp.proofs false

inspect
@[nolint simpNF]
example : True := by
  trivial

inspect
example : 0 = 0 := by
  erw []
-- Parser.Command.openSimple
-- Parser.Command.open
inspect open _root_.Nat hiding add
inspect open _root_.Nat
inspect open _root_.Nat (add)
inspect
example : True := by
 open _root_.Nat in
 trivial

inspect @[deprecated Nat (since := "")] example := 0
inspect @[deprecated (since := "")] alias XX := Nat
#eval getMainModule
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


/-- info: 1: [deprecated Nat (since := "")] -/
#guard_msgs in
td
@[deprecated Nat (since := "")] example := 0

/-- info: 1: [deprecated (since := "")] -/
#guard_msgs in
td
@[deprecated (since := "")] alias X := Nat


/-- info: 1: [set_option linter.deprecated false] -/
#guard_msgs in
td
set_option linter.deprecated false in /-!-/

/-- info: 1: [set_option linter.deprecated false] -/
#guard_msgs in
td
set_option linter.deprecated false in
@[simp] example : True := trivial

namespace Fin.NatCast
def zero := 0
end Fin.NatCast

/-- info: 1: [open Fin.NatCast hiding zero] -/
#guard_msgs in
td
open Fin.NatCast hiding zero

/-- info: 1: [open Fin.NatCast] -/
#guard_msgs in
td
open Fin.NatCast


/-- info: 1: [erw []] -/
#guard_msgs in
td
example : 0 = 0 := by
  erw []

/-- info: 1: [nolint simpNF] -/
#guard_msgs in
td
@[nolint simpNF]
example : True := by
  trivial


/--
info: 3: [set_option backward.dsimp.proofs false, set_option maxHeartbeats 100, set_option tactic.skipAssignedInstances false]
-/
#guard_msgs in
td
set_option backward.dsimp.proofs false in
set_option pp.proofs false in
set_option maxHeartbeats 100 in -- testing techDebtLinter
set_option tactic.skipAssignedInstances false in /-!-/

/--
info: 1: [#adaptation_note /-- -/
 ]
-/
#guard_msgs in
td
#adaptation_note /---/

/--
info: 1: [#adaptation_note /-- -/
 ]
-/
#guard_msgs in
td
example : True := by
  #adaptation_note /---/
  trivial


@[inherit_doc Mathlib.Linter.linter.techDebtLinter]
def techDebtLinterLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.techDebtLinter (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  Linter.logLint linter.techDebtLinter stx m!"'{stx}' Nat subtraction"

initialize addLinter techDebtLinterLinter

end TechDebtLinter

end Mathlib.Linter
