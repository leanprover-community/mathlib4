/-
Copyright (c) 2026 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Conjugating by the square root of a positive element in a C⋆-algebra

This file defines `conjSqrt c a` as `sqrt c * a * sqrt c`, and develops API for this operation.

## Main declarations

* `conjSqrt c`: the map `fun a => sqrt c * a * sqrt c`, bundled as a continuous linear map,
-/

namespace CFC

open Ring

public section ConjSqrt

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [TopologicalSpace A]
  [StarOrderedRing A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] [SeparatelyContinuousMul A]

/-- Conjugation by the square root of an element, i.e. `sqrt c * a * sqrt c`. -/
@[expose]
noncomputable def conjSqrt (c : A) : A →L[ℝ] A where
  toLinearMap := .mulLeftRight ℝ (sqrt c, sqrt c)
  cont := by
    dsimp [LinearMap.mulLeftRight, LinearMap.mulLeft, LinearMap.mulRight]
    fun_prop

@[simp] lemma toLinearMap_conjSqrt (c : A) :
    (conjSqrt c).toLinearMap = .mulLeftRight ℝ (sqrt c, sqrt c) := rfl

lemma conjSqrt_apply {c a : A} : conjSqrt c a = sqrt c * a * sqrt c := rfl

lemma conjSqrt_of_not_nonneg {c a : A} (hc : ¬0 ≤ c) : conjSqrt c a = 0 := by
  simp [conjSqrt_apply, sqrt_of_not_nonneg hc]

lemma conjSqrt_monotone {c : A} : Monotone (conjSqrt c) := by
  intro a b hab
  by_cases hc : 0 ≤ c
  · exact IsSelfAdjoint.conjugate_le_conjugate hab (by cfc_tac)
  · simp [conjSqrt_of_not_nonneg hc]

@[gcongr]
lemma conjSqrt_le_conjSqrt {c a b : A} (h : a ≤ b) : conjSqrt c a ≤ conjSqrt c b :=
  conjSqrt_monotone h

variable [IsSemitopologicalRing A] [T2Space A]

set_option linter.overlappingInstances false

@[grind =]
lemma isStrictlyPositive_conjSqrt_iff (c a : A) (hc : IsStrictlyPositive c := by cfc_tac) :
    IsStrictlyPositive (conjSqrt c a) ↔ IsStrictlyPositive a := by
  have hc' : IsSelfAdjoint (sqrt c) := by cfc_tac
  rw [conjSqrt_apply]
  by_cases ha : IsSelfAdjoint a <;> grind

@[grind _=_]
lemma ringInverse_conjSqrt (c a : A) (hc : IsStrictlyPositive c := by cfc_tac) :
    (conjSqrt c a)⁻¹ʳ = conjSqrt c⁻¹ʳ a⁻¹ʳ := by
  by_cases ha : IsUnit a
  · grind [conjSqrt_apply]
  · have : ¬IsUnit (conjSqrt c a) := by grind [conjSqrt_apply, IsUnit.mul_left_iff]
    simp [inverse_non_unit a ha, inverse_non_unit _ this]

@[grind =]
lemma conjSqrt_ringInverse_conjSqrt (c a : A) (hc : IsStrictlyPositive c := by cfc_tac) :
    conjSqrt c⁻¹ʳ (conjSqrt c a) = a := by
  grind [IsSelfAdjoint.commute_of_mul_eq_isSelfAdjoint _ (sqrt c) 1, Ring.inverse_mul_cancel,
         conjSqrt_apply] =>
    have : sqrt c⁻¹ʳ * sqrt c = 1
    have : Commute (sqrt c) (sqrt c⁻¹ʳ)
    finish

@[grind =]
lemma conjSqrt_conjSqrt_ringInverse (c a : A) (hc : IsStrictlyPositive c := by cfc_tac) :
    conjSqrt c (conjSqrt c⁻¹ʳ a) = a := by
  grind [conjSqrt_ringInverse_conjSqrt _ _ hc.ringInverse]

@[grind =]
lemma conjSqrt_one (c : A) (hc : 0 ≤ c := by cfc_tac) : conjSqrt c 1 = c := by
  rw [conjSqrt_apply, mul_one, sqrt_mul_sqrt_self _]

@[grind =]
lemma conjSqrt_ringInverse_self (c : A) (hc : IsStrictlyPositive c := by cfc_tac) :
    conjSqrt c⁻¹ʳ c = 1 := by
  grind [conjSqrt_one c]

end ConjSqrt

end CFC
