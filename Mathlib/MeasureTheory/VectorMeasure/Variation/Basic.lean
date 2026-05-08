/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Variation.Defs

/-!
# Properties of variation

We prove basic properties of `variation` for `μ : VectorMeasure X V` in `ENormedAddCommMonoid V` on
`MeasurableSpace X`. It is defined as the supremum over partitions `{Eᵢ}` of `E`, of the quantity
`∑ᵢ, ‖μ(Eᵢ)‖`. This definition allows one to define the integral against
such vector-valued measures.

## Main results

* `enorm_measure_le_variation`: `‖μ E‖ₑ ≤ variation μ E`.
* `variation_zero`: `(0 : VectorMeasure X V).variation = 0`.
* `variation_neg`: `(-μ).variation = μ.variation`.
* `absolutelyContinuous`: `μ ≪ᵥ μ.variation`.
* `ennrealVariation_eq`: if `μ : VectorMeasure X ℝ≥0∞` then `μ.ennrealVariation = μ`.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

public section

open Finset
open scoped ENNReal

namespace MeasureTheory.VectorMeasure

variable {X V : Type*} {mX : MeasurableSpace X}

-- TODO: relocate the next three lemmas — `Finpartition.iUnion_parts_val` and
-- `Finpartition.pairwiseDisjoint_val` belong with the other Subtype-MeasurableSet /
-- Finpartition machinery (e.g. `Mathlib/MeasureTheory/Measure/PreVariation.lean`);
-- `sum_finpartition_parts` belongs near the other `VectorMeasure.of_biUnion_finset` lemmas.

/-- The bUnion of the parts (as sets) of a `Finpartition` of `⟨s, hs⟩ : Subtype MeasurableSet`
is `s` itself. -/
lemma _root_.Finpartition.iUnion_parts_val {s : Set X} {hs : MeasurableSet s}
    (P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet)) :
    ⋃ p ∈ P.parts, p.val = s := by
  have h := congrArg Subtype.val P.sup_parts
  rwa [Finset.sup_coe (Pbot := MeasurableSet.empty) (Psup := by measurability),
    Finset.sup_set_eq_biUnion] at h

/-- The parts (as sets) of a `Finpartition` of `⟨s, hs⟩ : Subtype MeasurableSet` are pairwise
disjoint. -/
lemma _root_.Finpartition.pairwiseDisjoint_val {s : Set X} {hs : MeasurableSet s}
    (P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet)) :
    (P.parts : Set (Subtype MeasurableSet)).PairwiseDisjoint
      (Subtype.val : _ → Set X) := fun a ha b hb hab => by
  have h := P.disjoint ha hb hab
  simp only [Function.onFun, disjoint_iff, id_eq, ← Subtype.coe_inj,
    MeasurableSet.coe_bot] at h
  rwa [Function.onFun, Set.disjoint_iff_inter_eq_empty]

/-- For `μ : VectorMeasure X V`, summing `μ` over the parts of a `Finpartition` of
`⟨s, hs⟩ : Subtype MeasurableSet` gives `μ s`. -/
lemma sum_finpartition_parts [AddCommMonoid V] [TopologicalSpace V] [T2Space V]
    (μ : VectorMeasure X V) {s : Set X} {hs : MeasurableSet s}
    (P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet)) :
    ∑ p ∈ P.parts, μ p.val = μ s := by
  rw [← μ.of_biUnion_finset P.pairwiseDisjoint_val (fun p _ => p.prop), P.iUnion_parts_val]

section Basic

variable [TopologicalSpace V] [ENormedAddCommMonoid V] [T2Space V]

@[simp]
lemma variation_apply (μ : VectorMeasure X V) (s : Set X) :
    μ.variation s = preVariation (‖μ ·‖ₑ) (isSigmaSubadditiveSetFun_enorm μ) (by simp) s := rfl

@[simp]
lemma ennrealVariation_apply (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s) :
    μ.ennrealVariation s = μ.variation s := Measure.toENNRealVectorMeasure_apply_measurable hs

/-- Measure version of `sum_le_preVariationFun_of_subset`. -/
lemma le_variation (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s) {P : Finset (Set X)}
    (hP₁ : ∀ t ∈ P, t ⊆ s) (hP₂ : (P : Set (Set X)).PairwiseDisjoint id) :
    ∑ p ∈ P, ‖μ p‖ₑ ≤ μ.variation s := by
  classical
  set Q := Finpartition.ofPairwiseDisjoint P hP₂ with defQ
  set Q' := Q.ofSubset (filter_subset MeasurableSet Q.parts) rfl with defQ'
  have hQ' : ∀ t ∈ Q'.parts, t ⊆ s := by simp [Q', Q]; grind
  calc
    ∑ p ∈ P, ‖μ p‖ₑ = ∑ p ∈ Q.parts, ‖μ p‖ₑ :=
      (Finpartition.sum_ofPairwiseDisjoint_eq_sum hP₂ (by simp)).symm
    _ = ∑ p ∈ Q'.parts, ‖μ p‖ₑ := (Q.sum_ofSubset_eq_sum _ _ _ (by simp_all)).symm
    _ ≤ ∑ p ∈ (Q'.extendOfLE (Finset.sup_le hQ')).parts, ‖μ p‖ₑ :=
      sum_le_sum_of_subset (Q'.parts_subset_extendOfLE (Finset.sup_le hQ'))
    _ ≤ μ.variation s := by
      simp only [variation_apply, preVariation_apply, ennrealToMeasure_apply hs,
        ennrealPreVariation_apply]
      apply preVariation.sum_le' (fun p => ‖μ p‖ₑ) hs
      intro p hp
      rcases Q'.mem_parts_or_eq_sdiff_of_mem_extendOfLE _ hp with h | rfl
      · simp_all
      simp only [sup_set_eq_biUnion, id_eq]
      exact hs.diff <| .biUnion (Finset.countable_toSet _) (by simp)

theorem enorm_measure_le_variation (μ : VectorMeasure X V) (E : Set X) :
    ‖μ E‖ₑ ≤ variation μ E := by
  by_cases hE : MeasurableSet E
  swap; · simp [μ.not_measurable' hE]
  by_cases hE' : (⟨E, hE⟩ : Subtype MeasurableSet) = ⊥
  · simp_all
  simp only [variation_apply, preVariation, ennrealToMeasure_apply hE, ennrealPreVariation_apply]
  calc
    ‖μ E‖ₑ = ∑ p ∈ (Finpartition.indiscrete hE').parts, ‖μ p‖ₑ := by simp
    _ ≤ preVariationFun (‖μ ·‖ₑ) E := by apply preVariation.sum_le

@[simp]
lemma variation_zero : (0 : VectorMeasure X V).variation = 0 := by
  simp only [variation, coe_zero, Pi.zero_apply, enorm_zero]
  exact preVariation_zero

lemma absolutelyContinuous (μ : VectorMeasure X V) : μ ≪ᵥ μ.ennrealVariation := by
  intro s hs
  by_cases hsm : MeasurableSet s
  · suffices ‖μ s‖ₑ ≤ 0 by simp_all
    grw [enorm_measure_le_variation, ← ennrealVariation_apply _ hsm, hs]
  · exact μ.not_measurable' hsm

end Basic

section NormedAddCommGroup

variable [NormedAddCommGroup V] {μ : VectorMeasure X V}

theorem norm_measure_le_variation {E : Set X} (hE : μ.variation E ≠ ∞ := by finiteness) :
    ‖μ E‖ ≤ μ.variation.real E := by
  rw [measureReal_def, ← toReal_enorm, ENNReal.toReal_le_toReal (enorm_ne_top) hE]
  exact enorm_measure_le_variation μ E

variable (μ) in
@[simp]
lemma variation_neg : (-μ).variation = μ.variation := by simp [variation]

end NormedAddCommGroup

section ENNReal

variable (μ : VectorMeasure X ℝ≥0∞)

/-- For `μ : VectorMeasure X ℝ≥0∞` and measurable `s`, the supremum over Finpartitions of
`⟨s, hs⟩ : Subtype MeasurableSet` of the sum of `μ` over parts equals `μ s`. -/
lemma iSup_sum_finpartition_parts (μ : VectorMeasure X ℝ≥0∞) {s : Set X} (hs : MeasurableSet s) :
    ⨆ (P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet)), ∑ p ∈ P.parts, μ p.val = μ s := by
  refine le_antisymm (iSup_le fun P => (μ.sum_finpartition_parts P).le) ?_
  obtain ⟨P⟩ := (inferInstance : Nonempty (Finpartition (⟨s, hs⟩ : Subtype MeasurableSet)))
  exact le_iSup_of_le P (μ.sum_finpartition_parts P).symm.le

/-- For `μ : VectorMeasure X ℝ≥0∞`, `preVariationFun μ s = μ s` for any `s`. -/
@[simp]
lemma preVariationFun_apply_of_ENNReal (s : Set X) : preVariationFun μ s = μ s := by
  unfold preVariationFun
  split_ifs with hs
  · exact iSup_sum_finpartition_parts μ hs
  · exact (μ.not_measurable' hs).symm

@[simp]
theorem variation_eq_ennrealToMeasure : μ.variation = μ.ennrealToMeasure := by
  ext _ hs
  simp [variation_apply, preVariation_apply, ennrealPreVariation_apply, ennrealToMeasure_apply hs]

@[simp]
theorem ennrealVariation_eq : μ.ennrealVariation = μ := by simp [ennrealVariation]

end ENNReal

end MeasureTheory.VectorMeasure
