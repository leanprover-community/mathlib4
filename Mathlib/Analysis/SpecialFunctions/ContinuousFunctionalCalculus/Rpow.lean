/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.CstarAlgebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog
import Mathlib.Analysis.CstarAlgebra.ContinuousFunctionalCalculus.NonUnital

/-!
# Real powers defined via the continuous functional calculus

This file defines real powers via the continuous functional calculus (CFC) and builds its API.
This allows one to take real powers of matrices, operators, elements of a C⋆-algebra, etc.

## Main declarations

+ `CFC.rpow`: the real power function based on the CFC, i.e. `cfc Real.rpow`

## Implementation notes

FIXME

## TODO

FIXME
-/

open scoped NNReal

namespace CFC

section NonUnital

variable {A : Type*} [PartialOrder A] [NonUnitalNormedRing A] [StarRing A] [StarOrderedRing A]
  [TopologicalRing A] [Module ℝ≥0 A] [SMulCommClass ℝ≥0 A A] [IsScalarTower ℝ≥0 A A]
  [CompleteSpace A] [NonUnitalContinuousFunctionalCalculus ℝ≥0 (fun (a : A) => 0 ≤ a)]
  [UniqueNonUnitalContinuousFunctionalCalculus ℝ≥0 A]

/-- Real powers of operators, based on the non-unital continuous functional calculus. -/
noncomputable def rpowₙ (a : A) (y : ℝ≥0) : A := cfcₙ (fun x => NNReal.rpow x y) a

/-- Square roots of operators, based on the non-unital continuous functional calculus. -/
noncomputable def sqrt (a : A) : A := cfcₙ NNReal.sqrt a

/- ## `rpowₙ` -/

@[simp]
lemma rpowₙ_nonneg {a : A} {x : ℝ≥0} : 0 ≤ rpowₙ a x := cfcₙ_predicate _ a

lemma rpowₙ_add {a : A} {x y : ℝ≥0} (hx : 0 < x) (hy : 0 < y) :
    rpowₙ a (x + y) = rpowₙ a x * rpowₙ a y := by
  simp only [rpowₙ]
  have hcont : ∀ r : ℝ≥0,
      (hr : 0 < r) → ContinuousOn (fun z => NNReal.rpow z r) (quasispectrum ℝ≥0 a) :=
    fun r hr => (NNReal.continuous_rpow_const (le_of_lt hr)).continuousOn
  rw [← cfcₙ_mul (fun z => NNReal.rpow z x) (fun z => NNReal.rpow z y) a]
  congr
  ext z
  have : (x : ℝ) + (y : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (add_pos hx hy))
  simp [NNReal.rpow_add' _ this]

@[simp]
lemma rpowₙ_zero {a : A} : rpowₙ a 0 = 0 := by
  simp only [rpowₙ, NNReal.coe_zero, NNReal.rpow_eq_pow, NNReal.rpow_zero]
  have : (fun _ : ℝ≥0 => (1 : ℝ≥0)) 0 ≠ 0 := by simp
  simp [cfcₙ_apply_of_not_map_zero]

lemma rpowₙ_one {a : A} (ha : 0 ≤ a := by cfc_tac) : rpowₙ a 1 = a := by
  simp only [rpowₙ, NNReal.coe_one, NNReal.rpow_eq_pow, NNReal.rpow_one]
  change cfcₙ (id : ℝ≥0 → ℝ≥0) a = a
  rw [cfcₙ_id ℝ≥0 a]

lemma rpowₙ_two {a : A} (ha : 0 ≤ a := by cfc_tac) : rpowₙ a 2 = a * a := by
  simp only [rpowₙ, NNReal.coe_ofNat, NNReal.rpow_eq_pow, NNReal.rpow_ofNat, pow_two]
  change cfcₙ (fun z : ℝ≥0 => id z * id z) a = a * a
  rw [cfcₙ_mul id id a, cfcₙ_id ℝ≥0 a]

lemma rpowₙ_three {a : A} (ha : 0 ≤ a := by cfc_tac) : rpowₙ a 3 = a * a * a := by
  simp only [rpowₙ, NNReal.coe_ofNat, NNReal.rpow_eq_pow, NNReal.rpow_ofNat, pow_three]
  change cfcₙ (fun z : ℝ≥0 => id z * (id z * id z)) a = a * a * a
  rw [cfcₙ_mul id _ a, cfcₙ_mul id _ a, ← mul_assoc, cfcₙ_id ℝ≥0 a]

@[simp]
lemma zero_rpowₙ {x : ℝ≥0} : rpowₙ (0 : A) x = 0 := by simp [rpowₙ]

@[simp]
lemma rpowₙ_rpowₙ {a : A} {x y : ℝ≥0} : rpowₙ (rpowₙ a x) y = rpowₙ a (x * y) := by
  by_cases ha : 0 ≤ a
  case pos =>
    by_cases hx : 0 < x
    case neg =>
      replace hx : x = 0 := eq_of_le_of_not_lt (le_of_not_lt hx) not_lt_zero'
      simp [hx]
    case pos =>
      by_cases hy : 0 < y
      case neg =>
        replace hy : y = 0 := eq_of_le_of_not_lt (le_of_not_lt hy) not_lt_zero'
        simp [hy]
      case pos =>
        simp [rpowₙ]
        have h₁ : ContinuousOn (fun z : ℝ≥0 => z ^ (y : ℝ))
            ((fun z : ℝ≥0 => z ^ (x : ℝ)) '' quasispectrum ℝ≥0 a) :=
          Continuous.continuousOn <| NNReal.continuous_rpow_const (le_of_lt hy)
        have h₂ : ContinuousOn (fun z : ℝ≥0 => z ^ (x : ℝ)) (quasispectrum ℝ≥0 a) :=
          Continuous.continuousOn <| NNReal.continuous_rpow_const (le_of_lt hx)
        have h₀₁ : (fun z : ℝ≥0 => z ^ (y : ℝ)) 0 = 0 := by
          ext
          simp only [NNReal.coe_rpow, NNReal.coe_zero, le_refl]
          rw [Real.zero_rpow (by exact_mod_cast ne_of_gt hy)]
        have h₀₂ : (fun z : ℝ≥0 => z ^ (x : ℝ)) 0 = 0 := by
          ext
          simp only [NNReal.coe_rpow, NNReal.coe_zero, le_refl]
          rw [Real.zero_rpow (by exact_mod_cast ne_of_gt hx)]
        rw [← cfcₙ_comp (fun z : ℝ≥0 => z ^ (y : ℝ)) (fun z : ℝ≥0 => z ^ (x : ℝ)) a h₁ h₀₁ h₂ h₀₂]
        have : (fun z : ℝ≥0 => z ^ (y : ℝ)) ∘ (fun z : ℝ≥0 => z ^ (x : ℝ))
            = fun z => z ^ ((x : ℝ) * y) := by ext; simp [Real.rpow_mul]
        simp [this]
  case neg =>
    simp [rpowₙ, cfcₙ_apply_of_not_predicate a ha]

/- ## `sqrt` -/

@[simp]
lemma sqrt_nonneg {a : A} : 0 ≤ sqrt a := cfcₙ_predicate _ a

lemma sqrt_eq_rpowₙ {a : A} : sqrt a = rpowₙ a (1 / 2) := by
  simp only [sqrt, rpowₙ, NNReal.coe_inv, NNReal.coe_ofNat, NNReal.rpow_eq_pow]
  congr
  ext
  exact_mod_cast NNReal.sqrt_eq_rpow _

@[simp]
lemma sqrt_zero : sqrt (0 : A) = 0 := by simp [sqrt]

@[simp]
lemma rpowₙ_sqrt {a : A} {x : ℝ≥0} : rpowₙ (sqrt a) x = rpowₙ a (x / 2) := by
  simp [sqrt_eq_rpowₙ, inv_mul_eq_div]

lemma rpowₙ_sqrt_two {a : A} (ha : 0 ≤ a := by cfc_tac) : rpowₙ (sqrt a) 2 = a := by
  simp only [rpowₙ_sqrt, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]
  rw [rpowₙ_one]

lemma sqrt_mul_sqrt_self {a : A} (ha : 0 ≤ a := by cfc_tac) : sqrt a * sqrt a = a := by
  rw [← rpowₙ_two, rpowₙ_sqrt_two]

@[simp]
lemma sqrt_rpowₙ {a : A} {x : ℝ≥0} : sqrt (rpowₙ a x) = rpowₙ a (x / 2) := by
  simp [sqrt_eq_rpowₙ, div_eq_mul_inv]

lemma sqrt_rpowₙ_two {a : A} (ha : 0 ≤ a := by cfc_tac) : sqrt (rpowₙ a 2) = a := by
  simp only [sqrt_rpowₙ, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]
  rw [rpowₙ_one]

lemma sqrt_mul_self {a : A} (ha : 0 ≤ a := by cfc_tac) : sqrt (a * a) = a := by
  rw [← rpowₙ_two, sqrt_rpowₙ_two]

end NonUnital

section Unital

variable {A : Type*} [PartialOrder A] [NormedRing A] [StarRing A] [StarOrderedRing A]
  [TopologicalRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
  [ContinuousFunctionalCalculus ℝ≥0 (fun (a : A) => 0 ≤ a)]
  --[NonUnitalContinuousFunctionalCalculus ℝ≥0 (fun (a : A) => 0 ≤ a)]
  [UniqueContinuousFunctionalCalculus ℝ≥0 A]
  --[UniqueNonUnitalContinuousFunctionalCalculus ℝ≥0 A]

noncomputable def rpow (a : A) (y : ℝ) : A := cfc (fun x => NNReal.rpow x y) a

@[simp]
lemma rpow_nonneg {a : A} {y : ℝ} : 0 ≤ rpow a y := cfc_predicate _ a

--lemma rpowₙ_eq_rpow {a : A} {y : ℝ≥0} : rpowₙ a y = rpow a y := by
--  sorry

lemma rpow_natCast {a : A} (n : ℕ) : rpow a n = a ^ n := by
  sorry

lemma rpow_algebraMap {x y : ℝ} : rpow (algebraMap ℝ A x) y = algebraMap ℝ A (x ^ y) := by sorry

lemma exp_smul {a : A} {r : ℝ} : NormedSpace.exp ℂ (r • a) = rpow (NormedSpace.exp ℂ a) r := by
  sorry

lemma rpow_add {a : A} {x y : ℝ} : rpow a (x + y) = rpow a x * rpow a y := by sorry

lemma rpow_rpow {a : A} {x y : ℝ} : rpow (rpow a x) y = rpow a (x * y) := by sorry

lemma rpow_one {a : A} : rpow a 1 = a := by sorry

lemma one_rpow {x : ℝ} : rpow (1 : A) x = (1 : A) := by sorry

lemma rpow_zero {a : A} : rpow a 0 = 1 := by sorry

lemma zero_rpow {x : ℝ} (hx : x ≠ 0) : rpow (0 : A) x = 0 := by sorry

lemma log_rpow {a : A} {x : ℝ≥0} : log (rpow a x) = x • log a := by sorry

end Unital

end CFC
