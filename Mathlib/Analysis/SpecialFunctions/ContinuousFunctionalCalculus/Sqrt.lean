/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.NormedSpace.Star.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The square root function based on the continuous functional calculus

This file defines the square root function via the non-unital continuous functional calculus and
build its API. This allows one to take square roots of matrices, operators, elements of a
C⋆-algebra, etc.

## Main declarations

+ `CFC.sqrt`: the actual square root function

## Implementation notes

Since the square root is based on `NNReal.sqrt`, it only applies to positive elements of the
algebra, and returns the junk value of zero for all other inputs.
-/

open NNReal PNat

namespace CFC

section NNReal

variable {A : Type*} [PartialOrder A] [NonUnitalRing A] [StarRing A] [StarOrderedRing A]
  [TopologicalSpace A] [Module ℝ≥0 A] [IsScalarTower ℝ≥0 A A] [SMulCommClass ℝ≥0 A A]
  [NonUnitalContinuousFunctionalCalculus ℝ≥0 ((0 : A) ≤ ·)]
  [UniqueNonUnitalContinuousFunctionalCalculus ℝ≥0 A]

noncomputable def sqrt (a : A) : A := cfcₙ NNReal.sqrt a

@[simp] lemma sqrt_nonneg {a : A} : 0 ≤ sqrt a := by
  by_cases h : 0 ≤ a
  · exact cfcₙ_predicate _ _
  · rw [sqrt, cfcₙ_apply_of_not_predicate _ h]

@[simp] lemma isSelfAdjoint_sqrt {a : A} : IsSelfAdjoint (sqrt a) :=
  IsSelfAdjoint.of_nonneg <| by simp

lemma star_sqrt {a : A} : star (sqrt a) = sqrt a := by simp [IsSelfAdjoint.star_eq]

lemma sqrt_mul_self {a : A} (ha : 0 ≤ a) : sqrt (a * a) = a := by
  -- These three `have`s shouldn't be needed, but the autoparams are not firing
  -- even though `cfc_zero_tac` does find the proofs
  have htriv1 : (id : ℝ≥0 → ℝ≥0) 0 = 0 := by cfc_zero_tac
  have htriv2 : NNReal.sqrt 0 = 0 := by cfc_zero_tac
  have htriv3 : (id : ℝ≥0 → ℝ≥0) 0 * (id : ℝ≥0 → ℝ≥0) 0 = 0 := by cfc_zero_tac
  have h₄ : NNReal.sqrt ∘ (fun x => id x * id x) = id := by ext; simp
  have : a = cfcₙ (id : ℝ≥0 → ℝ≥0) a := by
    exact Eq.symm (cfcₙ_id ℝ≥0 a ha)
  conv => enter [1, 1]; rw [this]
  rw [sqrt, ← cfcₙ_mul _ _ a, ← cfcₙ_comp NNReal.sqrt _ a, h₄]
  exact this.symm

lemma mul_self_sqrt {a : A} (ha : 0 ≤ a) : sqrt a * sqrt a = a := by
  have hmain : (fun x => NNReal.sqrt x * NNReal.sqrt x) = id := by ext; simp
  rw [sqrt, ← cfcₙ_mul NNReal.sqrt NNReal.sqrt a, hmain]
  exact cfcₙ_id ℝ≥0 a ha

lemma sqrt_eq_iff_eq_mul_self {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) : sqrt a = b ↔ a = b * b := by
  refine ⟨fun h => ?mp, fun h => ?mpr⟩
  case mp => rw [← h]; exact (mul_self_sqrt ha).symm
  case mpr => rw [h]; exact sqrt_mul_self hb

end NNReal

section Real

variable {A : Type*} [PartialOrder A] [NonUnitalRing A] [StarRing A] [StarOrderedRing A]
  [TopologicalSpace A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
  [NonUnitalContinuousFunctionalCalculus ℝ≥0 ((0 : A) ≤ ·)]
  [UniqueNonUnitalContinuousFunctionalCalculus ℝ≥0 A]

@[simp] lemma sqrt_zero : sqrt (0 : A) = 0 := by
  rw [sqrt]
  exact cfcₙ_apply_zero ℝ≥0 ℝ

@[simp]
lemma sqrt_smul {r : ℝ≥0} {a : A} : sqrt (r • a) = (NNReal.sqrt r) • sqrt a := by
  by_cases ha : 0 ≤ a
  · simp only [sqrt]
    have h₁ : r • a = cfcₙ (fun x : ℝ≥0 => r • x) a := by rw [← cfcₙ_smul_id (R := ℝ≥0) r a]
    have hmain : NNReal.sqrt ∘ (fun x : ℝ≥0 => r • x) = (fun x ↦ NNReal.sqrt r • NNReal.sqrt x) := by
      ext; simp
    rw [← cfcₙ_smul (NNReal.sqrt r) NNReal.sqrt a, h₁,
      ← cfcₙ_comp NNReal.sqrt (fun (x : ℝ≥0) => r • x) (ha := ha)]
    apply cfcₙ_congr
    rw [hmain]
    exact fun ⦃x⦄ ↦ congrFun rfl
  · by_cases hr : r = 0
    · simp [hr]
    · have ha' : ¬ 0 ≤ (r • a) := by
        sorry
      simp [sqrt, cfcₙ_apply_of_not_predicate _ ha', cfcₙ_apply_of_not_predicate _ ha]


end Real

section Ring

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [StarOrderedRing A]
  [TopologicalSpace A] [Algebra ℝ A]
  [NonUnitalContinuousFunctionalCalculus ℝ≥0 ((0 : A) ≤ ·)]
  --[NonUnitalContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
  [UniqueNonUnitalContinuousFunctionalCalculus ℝ≥0 A]

@[simp]
lemma sqrt_algebraMap {r : ℝ≥0} : sqrt (algebraMap ℝ A r) = algebraMap ℝ A (NNReal.sqrt r) := by
  rw [sqrt]
  sorry

lemma sqrt_one : sqrt (1 : A) = 1 := by
  sorry

lemma sq_sqrt {a : A} (ha : 0 ≤ a) : sqrt a ^ 2 = a := by sorry

lemma sqrt_sq {a : A} (ha : 0 ≤ a) : sqrt (a ^ 2) = a := by sorry

end Ring

end CFC
