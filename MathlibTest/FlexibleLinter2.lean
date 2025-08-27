import Batteries.Tactic.PermuteGoals
import Mathlib.Tactic.Linter.FlexibleLinter
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

set_option linter.flexible true
set_option linter.unusedVariables false

/--
warning: 'simp' is a flexible tactic modifying '⊢'…

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: … and 'cfc_tac' uses '⊢'!
-/
#guard_msgs in
example  {A₁ A₂ : Type*} [NonUnitalRing A₁] [Module ℂ A₁] [SMulCommClass ℝ A₁ A₁]
    [IsScalarTower ℝ A₁ A₁] [StarRing A₁]
  [TopologicalSpace A₁] [NonUnitalContinuousFunctionalCalculus ℝ A₁ IsSelfAdjoint]
  [PartialOrder A₁] [StarOrderedRing A₁] [NonUnitalRing A₂] [Module ℂ A₂]
  [StarRing A₂] [PartialOrder A₂] [StarOrderedRing A₂] (f : A₁ →ₚ[ℂ] A₂) (a : A₁)
  (ha : IsSelfAdjoint a) : IsSelfAdjoint (f (a⁺ - a⁻) + 0) := by
  simp
  cfc_tac
