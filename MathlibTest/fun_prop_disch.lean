import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
This file tests that `fun_prop` does not revert state changes made by the discharger to its goal's
context, which are necessary for `(disch := grind)` to work.
-/

open Real Set

example : ContinuousOn (log ∘ sin) (Ioo 0 π) := by
  fun_prop (disch := grind [sin_pos_of_mem_Ioo])


-- In case the behaviour of `grind` changes, here's a more explicit test.
open Lean Elab Tactic Meta in
example : ContinuousOn (log ∘ sin) (Ioo 0 π) := by
  have : ∀ x ∈ Ioo 0 π, sin x ≠ 0 := by grind [sin_pos_of_mem_Ioo]
  fun_prop (disch := run_tac
    let goal ← getMainGoal
    let ty ← goal.getType
    let mvar ← mkFreshExprSyntheticOpaqueMVar ty
    let _ ← mvar.mvarId!.assumption
    goal.assign <| ← mkAuxTheorem ty (← instantiateMVars mvar))
