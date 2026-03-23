/-
Copyright (c) 2026 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.ConjSqrt
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Convex.Mul

/-!
# Order properties of `Ring.inverse` in C⋆-algebras

This file shows that `Ring.inverse` is antitone and convex on strictly positive operators.

## Main declarations

* `antitoneOn_ringInverse`: `Ring.inverse` is antitone on strictly positive operators, i.e.
  the inverse is operator antitone.
* `convexOn_ringInverse`: `Ring.inverse` is convex on strictly positive operators, i.e. the inverse
  is operator convex.
-/

namespace CFC

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Ring in
public lemma antitoneOn_ringInverse : AntitoneOn Ring.inverse {a : A | IsStrictlyPositive a} := by
  /- Suppose `a ≤ b`. Then, define `c = a^(-1/2) b a^(-1/2)`, and we have that `1 ≤ c`.
  Now, `b⁻¹ ≤ a⁻¹` is equivalent to `c⁻¹ ≤ 1`, and this can be proven since `1` and `c` commute. -/
  intro a (apos : IsStrictlyPositive a) b (bpos : IsStrictlyPositive b) hab
  let c := conjSqrt (inverse a) b
  have cpos : IsStrictlyPositive c := by grind
  have hcont : ContinuousOn (fun r : ℝ => r⁻¹) (spectrum ℝ c) :=
    ContinuousOn.mono continuousOn_inv₀ (by grind)
  have hc₁ : 1 ≤ c := by
    rw [← conjSqrt_ringInverse_self a]
    unfold c
    gcongr
  have hc₂ : inverse c ≤ 1 := by
    rw [inverse_eq_rpow_neg_one (by grind), CFC.rpow_neg_one_eq_cfc_inv, cfc_nnreal_eq_real _ _]
    simp only [NNReal.coe_inv, Real.coe_toNNReal']
    rw [CFC.one_le_iff c (R := ℝ)] at hc₁
    apply cfc_le_one
    grind [inv_le_one₀]
  have hb₁ : inverse b = conjSqrt (inverse a) (inverse c) := by grind [inverse_conjSqrt]
  rw [hb₁]
  nth_rewrite 2 [← conjSqrt_one a, inverse_conjSqrt _ _]
  gcongr
  simp [hc₂]

open Ring in
@[gcongr]
public lemma ringInverse_le_ringInverse {a b : A} (hab : a ≤ b)
    (ha : IsStrictlyPositive a := by cfc_tac) : inverse b ≤ inverse a :=
  antitoneOn_ringInverse ha (IsStrictlyPositive.of_le ha hab) hab

open Ring in
public lemma convexOn_ringInverse :
    ConvexOn ℝ {a : A | IsStrictlyPositive a} Ring.inverse := by
  /- We need to prove that `(a • x + b • y)⁻¹ ≤ a • x⁻¹ + b • y⁻¹`. To do this, we define
  `z := x^(-1/2) y x^(-1/2)`. This turns the statement to prove into
  `(a • 1 + b • z)⁻¹ ≤ a • 1⁻¹ + b • z⁻¹`, and this can be proven since everything now commutes. -/
  refine ⟨by grind [convex_iff_forall_pos], ?_⟩
  intro x (xpos : IsStrictlyPositive x) y (ypos : IsStrictlyPositive y) a b ha hb hab
  let z := conjSqrt (inverse x) y
  have hz : IsStrictlyPositive z := ypos.conjugate_of_isSelfAdjoint (by grind) (by cfc_tac)
  have zpos : IsStrictlyPositive z := by grind
  have xinvpos : IsStrictlyPositive (inverse x) := by grind
  have hsp : IsStrictlyPositive (a • 1 + b • z) := by
    have : 0 ≤ b • z := by grind [smul_nonneg]
    have : 0 ≤ a • (1 : A) := smul_nonneg ha zero_le_one
    by_cases ha' : 0 < a <;> grind
  have h₁ : (a • 1 + b • z) ^ (-1 : ℝ) = cfc (fun r => (a + b * r) ^ (-1 : ℝ)) z := by
    rw [← cfc_smul_id (R := ℝ) (S := ℝ) b z, ← Algebra.algebraMap_eq_smul_one,
        ← cfc_const_add a (fun r => b • r) z]
    rw [cfc_comp_rpow]
    · congr
    · intro r hr
      by_cases ha' : a = 0
      · have hb' : b = 1 := by grind
        simp [hb', ha']
        grind
      · apply add_pos_of_pos_of_nonneg
        · grind
        · exact smul_nonneg hb (by grind)
  have h₂ : (a • 1 + b • z ^ (-1 : ℝ)) = cfc (fun r => (a + b * r ^ (-1 : ℝ))) z := by
    rw [CFC.rpow_eq_cfc_real hz.nonneg]
    have hcont : ContinuousOn (fun r : ℝ => (r ^ (-1 : ℝ))) (spectrum ℝ z) :=
      ContinuousOn.rpow_const (f := id) (by fun_prop) (by grind)
    rw [← cfc_smul b _ z hcont]
    rw [← Algebra.algebraMap_eq_smul_one, ← cfc_const_add a _ z]
    refine cfc_congr ?_
    intro r hr
    simp
  calc _ = inverse (a • conjSqrt x 1 + b • conjSqrt x z) := by
        rw [conjSqrt_conjSqrt_ringInverse _ _ xpos, conjSqrt_one _ xpos]
      _ = inverse (conjSqrt x (a • 1 + b • z)) := by simp
      _ = conjSqrt (inverse x) (inverse (a • 1 + b • z)) := by rw [inverse_conjSqrt _ _ xpos]
      _ = conjSqrt (inverse x) ((a • 1 + b • z) ^ (-1 : ℝ)) := by
        rw [← inverse_eq_rpow_neg_one]
      _ ≤ conjSqrt (inverse x) (a • 1 + b • z ^ (-1 : ℝ)) := by
        gcongr
        rw [h₁, h₂]
        refine (cfc_le_iff _ _ _ ?_ ?_).mpr ?_
        · apply ContinuousOn.rpow_const (by fun_prop)
          intro r hr
          have := hz.spectrum_pos hr
          obtain hcase|hcase := lt_or_eq_of_le ha
          · have : 0 ≤ b * r := by positivity
            grind
          · grind
        · refine ContinuousOn.const_add (ContinuousOn.const_mul ?_ _) _
          exact ContinuousOn.rpow_const (by fun_prop) (by grind)
        · intro r hr
          suffices (a • 1 + b • r) ^ (-1 : ℤ) ≤ a • 1 ^ (-1 : ℤ) + b • r ^ (-1 : ℤ) by
            simp_rw [← Real.rpow_intCast] at this
            simpa using this
          have : ConvexOn ℝ (Set.Ioi 0) (fun z : ℝ => z ^ (-1 : ℤ)) := convexOn_zpow (-1)
          grind [ConvexOn, IsStrictlyPositive.spectrum_pos]
      _ = conjSqrt (inverse x) (a • 1 + b • (inverse z)) := by rw [← inverse_eq_rpow_neg_one]
      _ = a • inverse x + b • conjSqrt (inverse x) (inverse z) := by
        simp [conjSqrt_one _ xinvpos]
      _ = _ := by
        rw [← inverse_conjSqrt _ _ xpos, conjSqrt_conjSqrt_ringInverse _ _ xpos]

end CFC
