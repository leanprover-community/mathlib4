import Mathlib.Util.CountHeartbeats

open Lean Elab Command

/-!
#  The "heavyRfl" linter

The "heavyRfl" linter emits a warning somewhere.
-/

open Lean Elab

namespace Mathlib.Linter

/-- The "heavyRfl" linter prints the number of heartbeat that a tactic `rfl` uses, if they exceed
the value of the linter option. -/
register_option linter.heavyRfl : Nat := {
  defValue := 10^5
  descr := "enable the heavyRfl linter"
}

namespace HeavyRfl

@[inherit_doc Mathlib.Linter.linter.heavyRfl]
def heavyRflLinter : Linter where run := withSetOptionIn fun stx ↦ do
  let hbBd ← getNatOption `linter.heavyRfl
  unless hbBd != 0 do
    return
  if (← get).messages.hasErrors then
    return
  unless (stx.find? (·.isOfKind ``Lean.Parser.Tactic.tacticRfl)).isSome do return
  let hbStx := Syntax.mkNumLit s!"{hbBd}"
  let repl ← stx.replaceM fun s => do
    if s.isOfKind ``Lean.Parser.Tactic.tacticRfl then
      return some (← `(tactic| count_heartbeats_over $hbStx ($(⟨s⟩); done)))
    else return none
  withScope (fun sc => {sc with currNamespace := `X ++ sc.currNamespace}) do
    elabCommand repl

initialize addLinter heavyRflLinter

end HeavyRfl

end Mathlib.Linter
