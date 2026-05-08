/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic






-- TODO: tidy this entire file and then push to the PR branch.






/-!
# Equivalence of variation definitions for signed measures

For a `SignedMeasure`, two notions of variation are available:
* the supremum-based `VectorMeasure.variation`, defined in
  `Mathlib/MeasureTheory/VectorMeasure/Variation/Basic.lean`;
* the Hahn–Jordan-based `SignedMeasure.totalVariation`, defined in
  `Mathlib/MeasureTheory/VectorMeasure/Decomposition/Jordan.lean`.

This file shows that they coincide.

## Main results

* `SignedMeasure.enorm_le_totalVariation`: `‖μ s‖ₑ ≤ μ.totalVariation s`.
* `SignedMeasure.totalVariation_eq_variation`: `μ.totalVariation = μ.variation`.

-/

@[expose] public section

open scoped ENNReal NNReal

-- TODO(mathlib4#26165): the next two `Finpartition` lemmas are scheduled to be added in mathlib
-- PR https://github.com/leanprover-community/mathlib4/pull/26165 . When that PR lands, delete
-- them here and use them directly from `Mathlib/Order/Partition/Finpartition.lean`.
namespace Finpartition

variable {α : Type*} [Lattice α] [OrderBot α] {a : α} (P : Finpartition a)

theorem sup_parts_apply {β : Type*} [SemilatticeSup β] [OrderBot β] {f : α → β}
    (hsup : ∀ x y, f (x ⊔ y) = f x ⊔ f y) (hbot : f ⊥ = ⊥) : P.parts.sup f = f a :=
  (Finset.comp_sup_eq_sup_comp f hsup hbot).symm.trans (congrArg f P.sup_parts)

theorem pairwiseDisjoint_apply {β : Type*} [SemilatticeInf β] [OrderBot β] {f : α → β}
    (hinf : ∀ x y, f (x ⊓ y) = f x ⊓ f y) (hbot : f ⊥ = ⊥) :
    (P.parts : Set α).PairwiseDisjoint f := fun _ hx _ hy hxy => by
  have h := (P.disjoint hx hy hxy).eq_bot
  simp only [id_eq] at h
  rw [Function.onFun, disjoint_iff, ← hinf, h, hbot]

end Finpartition

namespace MeasureTheory.SignedMeasure

variable {X : Type*} {mX : MeasurableSpace X} (μ : SignedMeasure X)

/-- For a positive measurable set `i` (i.e. `0 ≤ μ.restrict i`),
`μ.toMeasureOfZeroLE i _ _ j = ‖μ (i ∩ j)‖ₑ`. -/
lemma toMeasureOfZeroLE_apply_eq_enorm {i j : Set X} (him : MeasurableSet i)
    (hi : 0 ≤[i] μ) (hjm : MeasurableSet j) :
    μ.toMeasureOfZeroLE i him hi j = ‖μ (i ∩ j)‖ₑ := by
  rw [μ.toMeasureOfZeroLE_apply hi him hjm, Real.enorm_of_nonneg
    (μ.nonneg_of_zero_le_restrict (μ.zero_le_restrict_subset him Set.inter_subset_left hi))]
  exact (ENNReal.ofReal_eq_coe_nnreal _).symm

/-- For a negative measurable set `i` (i.e. `μ.restrict i ≤ 0`),
`μ.toMeasureOfLEZero i _ _ j = ‖μ (i ∩ j)‖ₑ`. -/
lemma toMeasureOfLEZero_apply_eq_enorm {i j : Set X} (him : MeasurableSet i)
    (hi : μ ≤[i] 0) (hjm : MeasurableSet j) :
    μ.toMeasureOfLEZero i him hi j = ‖μ (i ∩ j)‖ₑ := by
  rw [μ.toMeasureOfLEZero_apply hi him hjm, ← enorm_neg, Real.enorm_of_nonneg]
  · exact (ENNReal.ofReal_eq_coe_nnreal _).symm
  · refine neg_nonneg.mpr <| μ.nonpos_of_restrict_le_zero ?_
    exact μ.restrict_le_zero_subset him Set.inter_subset_left hi

open VectorMeasure in
/-- For signed measures, the Hahn–Jordan-based `totalVariation` agrees with the supremum-based
`variation`. -/
theorem totalVariation_eq_variation (μ : SignedMeasure X) :
    μ.totalVariation = μ.variation := by
  ext r hr
  obtain ⟨s, hsm, hs, hsc, hpos, hneg⟩ := μ.toJordanDecomposition_spec
  have hd : Disjoint (s ∩ r) (sᶜ ∩ r) := by
    rw [Set.disjoint_iff_inter_eq_empty]; ext x; simp; tauto
  have hcov : (s ∩ r) ∪ (sᶜ ∩ r) = r := by
    rw [← Set.union_inter_distrib_right, Set.union_compl_self, Set.univ_inter]
  have htotal : μ.totalVariation r = ‖μ (s ∩ r)‖ₑ + ‖μ (sᶜ ∩ r)‖ₑ := by
    rw [totalVariation, Measure.add_apply, hpos, hneg,
      μ.toMeasureOfZeroLE_apply_eq_enorm hsm hs hr,
      μ.toMeasureOfLEZero_apply_eq_enorm hsm.compl hsc hr]
  refine le_antisymm ?_ ?_
  · -- (≤): bound each enorm by the corresponding `μ.variation`, then use additivity of
    -- `μ.variation` as a measure on the disjoint pair `(s ∩ r), (sᶜ ∩ r)`.
    calc μ.totalVariation r
        = ‖μ (s ∩ r)‖ₑ + ‖μ (sᶜ ∩ r)‖ₑ := htotal
      _ ≤ μ.variation (s ∩ r) + μ.variation (sᶜ ∩ r) :=
          add_le_add (μ.enorm_measure_le_variation _) (μ.enorm_measure_le_variation _)
      _ = μ.variation ((s ∩ r) ∪ (sᶜ ∩ r)) := (measure_union hd (hsm.compl.inter hr)).symm
      _ = μ.variation r := by rw [hcov]
  · -- (≥): for each `Finpartition` of `⟨r, hr⟩ : Subtype MeasurableSet`, sum termwise via
    -- `enorm_le_totalVariation`, then use additivity of `μ.totalVariation` on the partition.
    simp only [variation_apply, preVariation_apply, ennrealToMeasure_apply hr,
      ennrealPreVariation_apply, preVariationFun, hr, ↓reduceDIte]
    refine iSup_le fun P => ?_
    have hcov' : ⋃ p ∈ P.parts, p.val = r := by
      rw [← Finset.sup_set_eq_biUnion]; exact P.sup_parts_apply (fun _ _ => rfl) rfl
    have hdisj : (P.parts : Set (Subtype MeasurableSet)).PairwiseDisjoint
        (Subtype.val : Subtype MeasurableSet → Set X) :=
      P.pairwiseDisjoint_apply (fun _ _ => rfl) rfl
    calc ∑ p ∈ P.parts, ‖μ p.val‖ₑ
        ≤ ∑ p ∈ P.parts, μ.totalVariation p.val :=
          Finset.sum_le_sum fun p _ => SignedMeasure.enorm_le_totalVariation μ p.val
      _ = μ.totalVariation (⋃ p ∈ P.parts, p.val) :=
          (measure_biUnion_finset hdisj fun p _ => p.prop).symm
      _ = μ.totalVariation r := by rw [hcov']

end MeasureTheory.SignedMeasure
