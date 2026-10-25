/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Etienne Marion
-/
module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Covering numbers and measure

We bound the covering and packing numbers of sets in a normed additive group `E` in terms of an
additive Haar measure `μ` on `E`. In a finite dimensional real normed space of dimension `d`, this
gives bounds of order `(r / ε) ^ d` on the covering numbers of a ball of radius `r` at scale `ε`.

## Main statements

* `Metric.measure_le_externalCoveringNumber_mul`: the measure of `A` is at most the external
  covering number of `A` at scale `ε` times the measure of a ball of radius `ε`.
* `Metric.packingNumber_mul_le_measure`: the packing number of `A` at scale `ε` times the measure of
  a ball of radius `ε / 2` is at most the measure of `A + closedEBall 0 (ε / 2)`.
* `Metric.measure_div_le_externalCoveringNumber`, `Metric.measure_div_le_coveringNumber`,
  `Metric.coveringNumber_le_measure_div`: the resulting lower bounds on the external and internal
  covering numbers of `A`, and upper bound on its covering number.
* `Metric.coveringNumber_closedEBall_ge`, `Metric.coveringNumber_closedEBall_le`: in a real normed
  space of dimension `d`, the covering number at scale `ε` of a ball of radius `r` is at least
  `(r / ε) ^ d` and at most `(2 * r / ε + 1) ^ d`.

## References

* [R. Vershynin, *High-dimensional probability*, Section 4.2][vershynin2018high]
-/

@[expose] public section

open MeasureTheory Measure Module Set
open scoped ENNReal NNReal

namespace Metric

section Measure

open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure] {ε : ℝ≥0} {A C : Set E}

/-- If `C` is an `ε`-cover of `A`, the measure of `A` is at most the cardinality of `C` times the
measure of a ball of radius `ε`. -/
lemma measure_le_of_isCover (hC : IsCover ε A C) (hε : ε ≠ 0) :
    μ A ≤ C.encard * μ (closedEBall (0 : E) ε) := by
  rcases C.finite_or_infinite with hC_fin | hC_inf
  · calc μ A
    _ ≤ μ (⋃ x ∈ C, closedEBall x ε) := measure_mono (isCover_iff_subset_iUnion_closedEBall.mp hC)
    _ ≤ ∑' x : C, μ (closedEBall (x : E) ε) := measure_biUnion_le _ hC_fin.countable _
    _ = C.encard * μ (closedEBall (0 : E) ε) := by
      simp_rw [addHaar_closedEBall_center μ _ (ε : ℝ≥0∞), ENNReal.tsum_const]
      simp
  · have h_pos : μ (closedEBall (0 : E) ε) ≠ 0 :=
      (measure_closedEBall_pos μ _ (mod_cast hε)).ne'
    rw [hC_inf.encard_eq, ENat.toENNReal_top, ENNReal.top_mul h_pos]
    exact le_top

/-- The measure of `A` is at most the external covering number of `A` at scale `ε` times the
measure of a ball of radius `ε`. -/
lemma measure_le_externalCoveringNumber_mul (A : Set E) (hε : ε ≠ 0) :
    μ A ≤ externalCoveringNumber ε A * μ (closedEBall (0 : E) ε) := by
  rw [externalCoveringNumber]
  let X := {C : Set E | IsCover ε A C}
  change _ ≤ (⨅ C ∈ X, C.encard).toENNReal * _
  rw [← iInf_subtype'']
  have hX_nonempty : Nonempty X := ⟨A, by simp [X]⟩
  obtain ⟨C, hC⟩ := ENat.exists_eq_iInf (fun C : X ↦ (C : Set E).encard)
  grw [← hC, measure_le_of_isCover μ C.2 hε]

private lemma le_measure_of_isSeparated_of_countable (hC_count : C.Countable) (hC : IsSeparated ε C)
    (h_subset : C ⊆ A) :
    C.encard * μ (closedEBall (0 : E) (ε / 2)) ≤ μ (A + closedEBall (0 : E) (ε / 2)) := by
  calc C.encard * μ (closedEBall (0 : E) (ε / 2))
  _ = ∑' x : C, μ (closedEBall (x : E) (ε / 2)) := by
    simp_rw [addHaar_closedEBall_center μ _ (ε / 2 : ℝ≥0∞), ENNReal.tsum_const]
    simp
  _ = μ (⋃ x ∈ C, closedEBall x (ε / 2)) :=
    (measure_biUnion hC_count hC.pairwiseDisjoint_closedEBall
      fun _ _ ↦ isClosed_closedEBall.measurableSet).symm
  _ ≤ μ (A + closedEBall (0 : E) (ε / 2)) := by
    refine measure_mono fun x hx ↦ ?_
    obtain ⟨y, hy, hx⟩ := Set.mem_iUnion₂.mp hx
    refine ⟨y, h_subset hy, x - y, ?_, by simp⟩
    rwa [mem_closedEBall, edist_zero_right, ← edist_eq_enorm_sub]

/-- If `C ⊆ A` is `ε`-separated, the cardinality of `C` times the measure of a ball of radius
`ε / 2` is at most the measure of the `ε / 2`-thickening of `A`. -/
lemma le_measure_of_isSeparated (hC : IsSeparated ε C) (h_subset : C ⊆ A) :
    C.encard * μ (closedEBall (0 : E) (ε / 2))
      ≤ μ (A + closedEBall (0 : E) (ε / 2)) := by
  by_cases hC_fin : C.Finite
  · exact le_measure_of_isSeparated_of_countable μ hC_fin.countable hC h_subset
  -- an infinite set contains a countable infinite subset
  let C' := Set.range (Subtype.val ∘ (Set.Infinite.natEmbedding C hC_fin))
  have hC'C : C' ⊆ C := by
    rintro _ ⟨n, rfl⟩
    exact (Set.Infinite.natEmbedding C hC_fin n).2
  have hC'_inf : C'.Infinite := Set.infinite_range_of_injective
    (Subtype.val_injective.comp (Set.Infinite.natEmbedding C hC_fin).injective)
  calc C.encard * μ (closedEBall (0 : E) (ε / 2))
  _ = C'.encard * μ (closedEBall (0 : E) (ε / 2)) := by
    rw [Set.Infinite.encard_eq hC_fin, hC'_inf.encard_eq]
  _ ≤ μ (A + closedEBall (0 : E) (ε / 2)) :=
    le_measure_of_isSeparated_of_countable μ (Set.countable_range _) (hC.subset hC'C)
      (hC'C.trans h_subset)

/-- The packing number of `A` at scale `ε` times the measure of a ball of radius `ε / 2` is at
most the measure of the `ε / 2`-thickening of `A`. -/
lemma packingNumber_mul_le_measure (A : Set E) (ε : ℝ≥0) :
    packingNumber ε A * μ (closedEBall (0 : E) (ε / 2))
      ≤ μ (A + closedEBall (0 : E) (ε / 2)) := by
  simp_rw [packingNumber, ENat.toENNReal_iSup, ENNReal.iSup_mul]
  exact iSup_le fun C ↦ iSup₂_le fun hC₁ hC₂ ↦ le_measure_of_isSeparated μ hC₂ hC₁

/-- The measure of `A` divided by the measure of a ball of radius `ε` is a lower bound for the
external covering number of `A` at scale `ε`. -/
lemma measure_div_le_externalCoveringNumber (A : Set E) (hε : ε ≠ 0) :
    μ A / μ (closedEBall (0 : E) ε) ≤ externalCoveringNumber ε A :=
  ENNReal.div_le_of_le_mul (measure_le_externalCoveringNumber_mul μ A hε)

/-- The measure of `A` divided by the measure of a ball of radius `ε` is a lower bound for the
covering number of `A` at scale `ε`. -/
lemma measure_div_le_coveringNumber (A : Set E) (hε : ε ≠ 0) :
    μ A / μ (closedEBall (0 : E) ε) ≤ coveringNumber ε A :=
  (measure_div_le_externalCoveringNumber μ A hε).trans
    (ENat.toENNReal_le.mpr (externalCoveringNumber_le_coveringNumber ε A))

/-- The measure of the `ε / 2`-thickening of `A` divided by the measure of a ball of radius
`ε / 2` is an upper bound for the covering number of `A` at scale `ε`. -/
lemma coveringNumber_le_measure_div [ProperSpace E] (A : Set E) (hε : ε ≠ 0) :
    coveringNumber ε A
      ≤ μ (A + closedEBall (0 : E) (ε / 2)) / μ (closedEBall (0 : E) (ε / 2)) := by
  have h_pos : μ (closedEBall (0 : E) (ε / 2)) ≠ 0 :=
    (measure_closedEBall_pos μ _ (ENNReal.div_ne_zero.2 ⟨mod_cast hε, by norm_num⟩)).ne'
  have h_top : μ (closedEBall (0 : E) (ε / 2)) ≠ ⊤ := by
    rw [show (ε : ℝ≥0∞) / 2 = ↑(ε / 2) by simp, closedEBall_coe]
    exact (isCompact_closedBall _ _).measure_ne_top
  rw [ENNReal.le_div_iff_mul_le (.inl h_pos) (.inl h_top)]
  grw [coveringNumber_le_packingNumber]
  exact packingNumber_mul_le_measure μ A ε

end Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ε : ℝ≥0}

/-- A ball of radius `r` in dimension `d` has covering number at least `(r / ε) ^ d` at
scale `ε`. -/
lemma coveringNumber_closedEBall_ge (ε : ℝ≥0) (x : E) {r : ℝ≥0} (hr : r ≠ 0) :
    ((r / ε) ^ finrank ℝ E : ℝ≥0∞) ≤ coveringNumber ε (closedEBall x r) := by
  borelize E
  obtain _ | _ := subsingleton_or_nontrivial E
  · simp only [Module.finrank_zero_of_subsingleton, pow_zero]
    norm_cast
    simp [Order.one_le_iff_pos]
  obtain rfl | hε := eq_or_ne ε 0
  · simp only [coveringNumber_zero]
    rw [Set.encard_eq_top]
    · simp
    · exact infinite_of_mem_nhds x (closedEBall_mem_nhds x (mod_cast hr.bot_lt))
  refine le_of_eq_of_le ?_ (measure_div_le_coveringNumber addHaar (closedEBall x r) hε)
  rw [addHaar_closedEBall_div]

/-- A ball of radius `r` in dimension `d` has covering number at most `(2 * r / ε + 1) ^ d` at
scale `ε`. -/
lemma coveringNumber_closedEBall_le (ε : ℝ≥0) (x : E) (r : ℝ≥0) :
    (coveringNumber ε (closedEBall x r) : ℝ≥0∞)
      ≤ (2 * r / (ε : ℝ≥0∞) + 1) ^ finrank ℝ E := by
  borelize E
  obtain _ | _ := subsingleton_or_nontrivial E
  · simp only [Module.finrank_zero_of_subsingleton, pow_zero]
    norm_cast
    grw [coveringNumber_le_encard_self, Set.encard_le_one_iff]
    exact fun a b _ _ ↦ Subsingleton.allEq a b
  obtain rfl | hr := eq_zero_or_pos r
  · simp
  obtain rfl | hε' := eq_zero_or_pos ε
  · simp only [ENNReal.coe_zero]
    rw [ENNReal.div_zero (by simp [hr.ne'])]
    simp [ENNReal.top_pow Module.finrank_pos.ne']
  grw [coveringNumber_le_measure_div addHaar (closedEBall x r) hε'.ne',
    closedEBall_add_closedEBall, addHaar_closedEBall_div,
    ← ENNReal.div_mul, ENNReal.add_div, ← mul_one_div (ε / 2 : ℝ≥0∞), ← ENNReal.mul_div_mul_comm,
    mul_comm (ε : ℝ≥0∞) 1, ENNReal.mul_div_mul_right, add_mul, ENNReal.div_mul_cancel,
    ENNReal.mul_comm_div, mul_comm (2 : ℝ≥0∞), mul_div_assoc]
  all_goals simp_all [hε'.ne']

/-- If `ε ≤ r`, a ball of radius `r` in dimension `d` has covering number at most
`(3 * r / ε) ^ d` at scale `ε`. -/
lemma coveringNumber_closedEBall_le_three_mul [Nontrivial E]
    {x : E} {r : ℝ≥0} (hr_zero : r ≠ 0) (hε : ε ≤ r) :
    (coveringNumber ε (closedEBall x r) : ℝ≥0∞)
      ≤ (3 * r / (ε : ℝ≥0∞)) ^ finrank ℝ E := by
  by_cases hε_zero : ε = 0
  · simp only [hε_zero, coveringNumber_zero, closedEBall_coe, ENNReal.coe_zero]
    rw [ENNReal.div_zero, ENNReal.top_pow]
    · exact le_top
    · exact Module.finrank_pos.ne'
    · simp [hr_zero]
  refine (coveringNumber_closedEBall_le _ _ _).trans ?_
  let d := finrank ℝ E
  calc (2 * r / (ε : ℝ≥0∞) + 1) ^ d
  _ ≤ (2 * r / (ε : ℝ≥0∞) + r / (ε : ℝ≥0∞)) ^ d := by
    gcongr
    rw [ENNReal.le_div_iff_mul_le (.inl <| mod_cast hε_zero) (.inr (by simp)), one_mul]
    exact mod_cast hε
  _ = (3 * r / (ε : ℝ≥0∞)) ^ d := by
    congr
    rw [← two_add_one_eq_three, add_mul, one_mul, ENNReal.add_div]

end Metric
