import Batteries.Tactic.PermuteGoals
import Mathlib.Tactic.Linter.FlexibleLinter
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Finiteness
import Mathlib.Data.ENNReal.Basic

set_option linter.flexible true
set_option linter.unusedVariables false

#guard_msgs in
example {A₁ A₂ : Type*} [NonUnitalRing A₁] [Module ℂ A₁] [SMulCommClass ℝ A₁ A₁]
    [IsScalarTower ℝ A₁ A₁] [StarRing A₁]
  [TopologicalSpace A₁] [NonUnitalContinuousFunctionalCalculus ℝ A₁ IsSelfAdjoint]
  [PartialOrder A₁] [StarOrderedRing A₁] [NonUnitalRing A₂] [Module ℂ A₂]
  [StarRing A₂] [PartialOrder A₂] [StarOrderedRing A₂] (f : A₁ →ₚ[ℂ] A₂) (a : A₁)
  (ha : IsSelfAdjoint a) : IsSelfAdjoint (f (a⁺ - a⁻) + 0) := by
  simp
  cfc_tac

#guard_msgs in
example {k l : ℤ} : 0 ≤ k ^ 2 + 4 * l * 0 := by
  simp
  positivity

-- TODO: this should not warn not warn!
open scoped ENNReal
/--
warning: 'simp' is a flexible tactic modifying '⊢'…

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: … and 'finiteness' uses '⊢'!
-/
#guard_msgs in
example {a b c : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) : a * b ≠ ∞ := by
  simp
  finiteness

#guard_msgs in
example {a b : ℝ≥0∞} (ha : a = 0) (hb : b = a) : a + b + 3 < ∞ := by
  simp [hb]
  finiteness_nonterminal; simp [ha]
