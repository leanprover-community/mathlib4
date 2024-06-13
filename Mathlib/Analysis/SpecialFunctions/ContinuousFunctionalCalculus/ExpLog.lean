/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.NormedSpace.Star.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.NormedSpace.Exponential

/-!
# The exp and log functions based on the continuous functional calculus

This file defines the log function via the continuous functional calculus and build its API.
This allows one to take logs of matrices, operators, elements of a C⋆-algebra, etc.

## Main declarations

+ `CFC.log`: the log function based on the CFC

## Implementation notes

Since `cfc Real.exp` and `cfc Complex.exp` are strictly less general than `NormedSpace.exp`
(defined via power series), we only give minimal API for these here in order to relate
`NormedSpace.exp` to functions defined via the CFC.
-/

namespace CFC

section exp

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [StarOrderedRing A]
  [TopologicalSpace A] [Algebra ℝ A]
  [ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
  [UniqueContinuousFunctionalCalculus ℝ A]

noncomputable def real_exp (a : A) : A := cfc Real.exp a

@[simp] lemma real_exp_zero [Nontrivial A] : real_exp (0 : A) = 1 := by
  rw [← cfc_one ℝ 0, real_exp]
  apply cfc_congr
  rw [spectrum.zero_eq]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  simp [hx]

@[simp]
lemma real_exp_algebraMap {r : ℝ} : real_exp (algebraMap ℝ A r) = algebraMap ℝ A (Real.exp r) := by
  sorry

end exp

section NormedSpace

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [StarOrderedRing A]
  [TopologicalSpace A] [TopologicalRing A] [Algebra ℝ A]
  [ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
  [UniqueContinuousFunctionalCalculus ℝ A]

-- Need some way of relating power series to the CFC
lemma real_exp_eq_normedSpace_exp {a : A} (ha : IsSelfAdjoint a) :
    real_exp a = NormedSpace.exp ℝ a := by
  sorry

end NormedSpace



section log

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [StarOrderedRing A]
  [TopologicalSpace A] [Algebra ℝ A]
  [ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
  [UniqueContinuousFunctionalCalculus ℝ A]

noncomputable def log (a : A) : A := cfc Real.log a

@[simp] lemma log_one : log (1 : A) = 0 := by
  sorry

@[simp]
lemma log_algebraMap {r : ℝ} : log (algebraMap ℝ A r) = algebraMap ℝ A (Real.log r) := by
  sorry

end log

end CFC
