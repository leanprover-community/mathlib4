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
  [IsTopologicalRing A] [T2Space A]

/-- Conjugation by the square root of an element, i.e. `sqrt c * a * sqrt c`. -/
@[expose]
noncomputable def conjSqrt (c : A) : A →L[ℝ] A where
  toFun a := sqrt c * a * sqrt c
  map_add' a b := by grind
  map_smul' r a := by simp

omit [IsTopologicalRing A] [T2Space A] in
lemma conjSqrt_apply {c a : A} : conjSqrt c a = sqrt c * a * sqrt c := rfl

@[grind =]
lemma isStrictlyPositive_conjSqrt_iff (c a : A) (hc : IsStrictlyPositive c := by cfc_tac) :
    IsStrictlyPositive (conjSqrt c a) ↔ IsStrictlyPositive a := by
  have hc' : IsSelfAdjoint (sqrt c) := by cfc_tac
  rw [conjSqrt_apply]
  by_cases ha : IsSelfAdjoint a <;> grind

@[grind _=_]
lemma inverse_conjSqrt (c a : A) (hc : IsStrictlyPositive c := by cfc_tac) :
    inverse (conjSqrt c a) = conjSqrt (inverse c) (inverse a) := by
  by_cases ha : IsUnit a
  · grind [conjSqrt_apply, sqrt_ringInverse]
  · have : ¬IsUnit (conjSqrt c a) := by grind [conjSqrt_apply]
    rw [inverse_non_unit a ha, inverse_non_unit _ this]
    simp

@[grind =]
lemma conjSqrt_ringInverse_conjSqrt (c a : A) (hc : IsStrictlyPositive c := by cfc_tac) :
    conjSqrt (inverse c) (conjSqrt c a) = a := by
  rw [conjSqrt_apply, conjSqrt_apply]
  have : sqrt (inverse c) * sqrt c = 1 := by
    simp_rw [sqrt_eq_rpow]
    rw [inverse_eq_rpow_neg_one, rpow_rpow _ _ _ (by grind), ← rpow_add (by grind)]
    grind [rpow_zero]
  have : sqrt c * sqrt (inverse c) = 1 := by
    simp_rw [sqrt_eq_rpow]
    rw [inverse_eq_rpow_neg_one, rpow_rpow _ _ _ (by grind), ← rpow_add (by grind)]
    grind [rpow_zero]
  grind only

@[grind =]
lemma conjSqrt_conjSqrt_ringInverse (c a : A) (hc : IsStrictlyPositive c := by cfc_tac) :
    conjSqrt c (conjSqrt (inverse c) a) = a := by
  rw [conjSqrt_apply, conjSqrt_apply]
  have : sqrt (inverse c) * sqrt c = 1 := by
    simp_rw [sqrt_eq_rpow]
    rw [inverse_eq_rpow_neg_one, rpow_rpow _ _ _ (by grind), ← rpow_add (by grind)]
    grind [rpow_zero]
  have : sqrt c * sqrt (inverse c) = 1 := by
    simp_rw [sqrt_eq_rpow]
    rw [inverse_eq_rpow_neg_one, rpow_rpow _ _ _ (by grind), ← rpow_add (by grind)]
    grind [rpow_zero]
  grind only

@[grind =]
lemma conjSqrt_one (c : A) (hc : IsStrictlyPositive c := by cfc_tac) : conjSqrt c 1 = c := by
  rw [conjSqrt_apply, mul_one, sqrt_mul_sqrt_self _]

@[grind =]
lemma conjSqrt_ringInverse_self (c : A) (hc : IsStrictlyPositive c := by cfc_tac) :
    conjSqrt (inverse c) c = 1 := by
  grind =>
    have : conjSqrt c 1 = c
    finish

lemma conjSqrt_of_not_nonneg {c a : A} (hc : ¬0 ≤ c) : conjSqrt c a = 0 := by
  have : sqrt c = 0 := by rw [sqrt_of_not_nonneg hc]
  simp [conjSqrt_apply, this]

lemma conjSqrt_monotone {c : A} : Monotone (conjSqrt c) := by
  intro a b hab
  by_cases hc : 0 ≤ c
  · exact IsSelfAdjoint.conjugate_le_conjugate hab (by cfc_tac)
  · simp [conjSqrt_of_not_nonneg hc]

@[gcongr]
lemma conjSqrt_le_conjSqrt {c a b : A} (h : a ≤ b) : conjSqrt c a ≤ conjSqrt c b :=
  conjSqrt_monotone h

end ConjSqrt

end CFC
