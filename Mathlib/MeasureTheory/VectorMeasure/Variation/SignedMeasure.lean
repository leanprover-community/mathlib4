/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
/-!
# Equivalence of variation definitions for signed measures

For a `SignedMeasure`, two notions of variation are available:
* the supremum-based `VectorMeasure.variation`,
* the Hahn–Jordan-based `SignedMeasure.totalVariation`.

This file shows that they coincide.

## Main results

* `SignedMeasure.totalVariation_eq_variation`: `μ.totalVariation = μ.variation`.

-/

public section

open scoped ENNReal NNReal

namespace MeasureTheory.SignedMeasure

variable {X : Type*} {mX : MeasurableSpace X} (μ : SignedMeasure X)

/-- The pointwise bound `‖s i‖ ≤ s.totalVariation.real i` for any signed measure. -/
theorem norm_le_totalVariation (s : SignedMeasure X) (i : Set X) :
    ‖s i‖ ≤ s.totalVariation.real i := by
  by_cases hi : MeasurableSet i
  · rw [s.apply_eq_posPart_real_sub_negPart_real hi, totalVariation, measureReal_add_apply]
    grind [measureReal_nonneg, Real.norm_eq_abs]
  · simp [hi]

/-- The pointwise bound `‖s i‖ₑ ≤ s.totalVariation i` for any signed measure. -/
theorem enorm_le_totalVariation (s : SignedMeasure X) (i : Set X) :
    ‖s i‖ₑ ≤ s.totalVariation i := calc
  _ = ENNReal.ofReal ‖s i‖ := (ofReal_norm _).symm
  _ ≤ ENNReal.ofReal (s.totalVariation.real i) :=
    ENNReal.ofReal_le_ofReal (s.norm_le_totalVariation i)
  _ = _ := by rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma toMeasureOfZeroLE_apply_eq_enorm {i j : Set X} (him : MeasurableSet i) (hi : 0 ≤[i] μ)
    (hjm : MeasurableSet j) : μ.toMeasureOfZeroLE i him hi j = ‖μ (i ∩ j)‖ₑ := by
  have : 0 ≤ μ (i ∩ j) :=
    μ.nonneg_of_zero_le_restrict (μ.zero_le_restrict_subset ‹_› Set.inter_subset_left ‹_›)
  rw [Real.enorm_of_nonneg this, μ.toMeasureOfZeroLE_apply hi him hjm, ENNReal.ofReal_eq_coe_nnreal]

lemma toMeasureOfLEZero_apply_eq_enorm {i j : Set X} (him : MeasurableSet i)
    (hi : μ ≤[i] 0) (hjm : MeasurableSet j) :
    μ.toMeasureOfLEZero i him hi j = ‖μ (i ∩ j)‖ₑ := by
  have : μ (i ∩ j) ≤ 0 :=
    μ.nonpos_of_restrict_le_zero (μ.restrict_le_zero_subset ‹_› Set.inter_subset_left ‹_›)
  rw [← enorm_neg, Real.enorm_of_nonneg (neg_nonneg.mpr this), μ.toMeasureOfLEZero_apply hi him hjm,
    ENNReal.ofReal_eq_coe_nnreal]

open VectorMeasure in
/-- The Hahn–Jordan-based `totalVariation` agrees with the supremum-based `variation`. -/
theorem totalVariation_eq_variation (μ : SignedMeasure X) : μ.totalVariation = μ.variation := by
  ext r hr
  apply le_antisymm
  · obtain ⟨s, hsm, _, _, _, _⟩ := μ.toJordanDecomposition_spec
    calc μ.totalVariation r
      _ = ‖μ (s ∩ r)‖ₑ + ‖μ (sᶜ ∩ r)‖ₑ := by
        grind [totalVariation, Measure.add_apply, μ.toMeasureOfZeroLE_apply_eq_enorm,
          μ.toMeasureOfLEZero_apply_eq_enorm]
      _ ≤ μ.variation (s ∩ r) + μ.variation (sᶜ ∩ r) :=
        add_le_add (μ.enorm_measure_le_variation _) (μ.enorm_measure_le_variation _)
      _ = μ.variation ((s ∩ r) ∪ (sᶜ ∩ r)) :=
        (measure_union (by grind) (hsm.compl.inter hr)).symm
      _ = μ.variation r := by
        rw [← Set.union_inter_distrib_right, Set.union_compl_self, Set.univ_inter]
  · suffices ∀ (P : Finpartition (⟨r, hr⟩ : Subtype MeasurableSet)),
        ∑ x ∈ P.parts, ‖μ x‖ₑ ≤ μ.totalVariation r by
      simp only [variation_apply, preVariation_apply, ennrealToMeasure_apply hr,
        ennrealPreVariation_apply, preVariationFun]
      grind [iSup_le]
    intro P
    calc ∑ p ∈ P.parts, ‖μ p.val‖ₑ
      _ ≤ ∑ p ∈ P.parts, μ.totalVariation p.val :=
        Finset.sum_le_sum fun p _ => SignedMeasure.enorm_le_totalVariation μ p.val
      _ = μ.totalVariation (⋃ p ∈ P.parts, p.val) := by
        refine (measure_biUnion_finset ?_ fun p _ => p.prop).symm
        exact P.pairwiseDisjoint_apply (fun _ _ => rfl) rfl
      _ = μ.totalVariation r := by
        simp [← Finset.sup_set_eq_biUnion, P.sup_parts_apply]

end MeasureTheory.SignedMeasure
