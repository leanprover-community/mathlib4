/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# The semivariation of a vector measure

The semivariation of a vector measure is the supremum of the variations of its push-forwards
to `ℝ` through all linear forms of norm at most `1`. The interest of this notion is that, in the
reals, any set has nonnegative or nonpositive measure, so that the variation is realized by
a subset (up to a factor of at most `2`). This property is inherited by the semivariation in
general: one has the inequalities
```
‖μ s‖ₑ ≤ μ.semivariation s ≤ 2 sup_{t ⊆ s} ‖μ t‖ₑ
```

The notion of semivariation can in particular be used to show that any vector measure is bounded:
there exists `C < ∞` such that `‖μ s‖ ≤ C` for all `s`.

## Main results

* `μ.semivariation`: the semivariation of the vector measure `μ`.
* `exists_subset_lt_enorm_apply_of_lt_semivariation`: given `s`, there exists `t ⊆ s` such that
  `μ.semivariation s ≤ 2 ‖μ t‖ₑ` up to an arbitrarily small error.
* `μ.bound`: the semivariation of `univ`, in `ℝ≥0`. It is finite by definition.
* `enorm_apply_le_bound`: the inequality `‖μ s‖ₑ ≤ μ.bound`, uniformly in `s`.

## References

* [J. Diestel and J.J. Uhl, Vector Measures][DiestelUhl1977]

-/

public section

open scoped ENNReal Function Topology NNReal
open Set Filter

namespace MeasureTheory.VectorMeasure

variable {X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {mX : MeasurableSpace X}
  {μ : VectorMeasure X E} {s t : Set X}

/-- The semivariation of a vector measure, defined as the supremum of the variations
of the images of the vector measures under continuous linear forms of norm at most `1`. -/
noncomputable def semivariation (μ : VectorMeasure X E) (s : Set X) : ℝ≥0∞ :=
  ⨆ ℓ ∈ {ℓ : StrongDual ℝ E | ‖ℓ‖ₑ ≤ 1}, (μ.mapRange (ℓ : E →+ ℝ) ℓ.continuous).variation s

lemma semivariation_union_le :
    μ.semivariation (s ∪ t) ≤ μ.semivariation s + μ.semivariation t := by
  simp only [semivariation, iSup_le_iff]
  intro ℓ hℓ
  apply (measure_union_le _ _).trans
  gcongr <;> apply le_biSup _ hℓ

lemma semivariation_mono (hst : s ⊆ t) : μ.semivariation s ≤ μ.semivariation t := by
  simp only [semivariation, iSup_le_iff]
  intro ℓ hℓ
  apply (measure_mono hst).trans
  apply le_biSup _ hℓ

lemma semivariation_le_variation : μ.semivariation s ≤ μ.variation s := by
  simp only [semivariation, iSup_le_iff]
  intro ℓ hℓ
  suffices (μ.mapRange (ℓ : E →+ ℝ) ℓ.continuous).variation ≤ μ.variation from this s
  apply variation_le_of_forall_enorm_le (fun t ht ↦ ?_)
  simp only [mapRange_apply, AddMonoidHom.coe_coe]
  apply le_trans ?_ (enorm_measure_le_variation _ _)
  exact (ContinuousLinearMap.le_opNorm_enorm _ _).trans (mul_le_of_le_one_left (by positivity) hℓ)

lemma enorm_apply_le_semivariation : ‖μ s‖ₑ ≤ μ.semivariation s := by
  by_cases hs : MeasurableSet s; swap
  · simp [not_measurable, hs]
  obtain ⟨ℓ, ℓ_norm, hℓ⟩ : ∃ ℓ : StrongDual ℝ E, ‖ℓ‖ ≤ 1 ∧ ℓ (μ s) = ‖μ s‖ :=
    exists_dual_vector'' _ _
  have h'ℓ : ℓ ∈ {ℓ : StrongDual ℝ E | ‖ℓ‖ₑ ≤ 1} := by
    simp [enorm_eq_nnnorm, ← NNReal.coe_le_one, ℓ_norm]
  calc ‖μ s‖ₑ
  _ = ‖(μ.mapRange (ℓ : E →+ ℝ) ℓ.continuous) s‖ₑ := by simp [← ofReal_norm, hℓ]
  _ ≤ (μ.mapRange (ℓ : E →+ ℝ) ℓ.continuous).variation s := enorm_measure_le_variation _ _
  _ ≤ μ.semivariation s := by apply le_biSup _ h'ℓ

lemma enorm_apply_le_semivariation_of_subset (hst : s ⊆ t) :
    ‖μ s‖ₑ ≤ μ.semivariation t :=
  enorm_apply_le_semivariation.trans (semivariation_mono hst)

lemma exists_subset_lt_enorm_apply_of_lt_semivariation (hs : MeasurableSet s)
    {a : ℝ≥0∞} (ha : a < μ.semivariation s) :
    ∃ t ⊆ s, MeasurableSet t ∧ a < 2 * ‖μ t‖ₑ := by
  obtain ⟨ℓ, hℓ, h'ℓ⟩ : ∃ ℓ ∈ {ℓ : StrongDual ℝ E | ‖ℓ‖ₑ ≤ 1},
    a < (μ.mapRange (ℓ : E →+ ℝ) ℓ.continuous).variation s := lt_biSup_iff.1 ha
  obtain ⟨t, ts, t_meas, ht⟩ :
      ∃ t ⊆ s, MeasurableSet t ∧ a < 2 * ‖μ.mapRange (ℓ : E →+ ℝ) ℓ.continuous t‖ₑ :=
    SignedMeasure.exists_subset_lt_enorm_apply_of_lt_variation _ hs h'ℓ
  refine ⟨t, ts, t_meas, ht.trans_le ?_⟩
  gcongr
  exact (ContinuousLinearMap.le_opNorm_enorm _ _).trans (mul_le_of_le_one_left (by positivity) hℓ)

private lemma exists_one_le_enorm_apply_of_semivariation_eq_top
    (hs : MeasurableSet s) (h's : μ.semivariation s = ∞) :
    ∃ t, MeasurableSet t ∧ t ⊆ s ∧ μ.semivariation t = ∞ ∧ 1 ≤ ‖μ (s \ t)‖ₑ := by
  obtain ⟨t, ts, t_meas, ht⟩ : ∃ t ⊆ s, MeasurableSet t ∧ 2 * ‖μ s‖ₑ + 2 < 2 * ‖μ t‖ₑ := by
    apply exists_subset_lt_enorm_apply_of_lt_semivariation hs
    rw [h's]
    finiteness
  have h't : 1 + ‖μ s‖ₑ ≤ ‖μ t‖ₑ := by
    apply (ENNReal.mul_le_mul_iff_right (a := 2) (by simp) (by simp)).1
    rw [mul_add, add_comm, mul_one]
    exact ht.le
  have I : ∞ ≤ μ.semivariation t + μ.semivariation (s \ t) := by
    rw [← h's]
    apply le_trans (semivariation_mono (by simp)) semivariation_union_le
  simp only [top_le_iff, ENNReal.add_eq_top] at I
  rcases I with hI | hI
  · refine ⟨t, t_meas, ts, hI, ?_⟩
    have : 1 + ‖μ s‖ₑ ≤ ‖μ (s \ t)‖ₑ + ‖μ s‖ₑ := by
      apply h't.trans
      have : μ t = μ s - μ (s \ t) := by rw [← of_add_of_sdiff t_meas hs ts]; abel
      rw [this, add_comm]
      exact enorm_sub_le
    rwa [ENNReal.add_le_add_iff_right (by simp)] at this
  · refine ⟨s \ t, hs.diff t_meas, sdiff_subset, hI, ?_⟩
    simp only [_root_.sdiff_sdiff_right_self, le_eq_subset, ts, inf_of_le_right]
    exact le_trans (by simp) h't

private lemma semivariation_univ_lt_top : μ.semivariation univ < ∞ := by
  apply Ne.lt_top (fun h ↦ ?_)
  have A (s : Set X) (hs : MeasurableSet s) (h's : μ.semivariation s = ∞) :
      ∃ t, MeasurableSet t ∧ t ⊆ s ∧ μ.semivariation t = ∞ ∧ 1 ≤ ‖μ (s \ t)‖ₑ :=
    exists_one_le_enorm_apply_of_semivariation_eq_top hs h's
  choose! t t_meas t_subs t_var ht using A
  let s n := t^[n] univ
  have hs n : MeasurableSet (s n) ∧ μ.semivariation (s n) = ∞ := by
    induction n with
    | zero => simp [s, h]
    | succ n ih =>
      simp only [Function.iterate_succ', Function.comp_apply, s]
      exact ⟨t_meas _ ih.1 ih.2, t_var _ ih.1 ih.2⟩
  let u n := s n \ s (n + 1)
  have hu n : 1 ≤ ‖μ (u n)‖ₑ := by
    simp only [Function.iterate_succ', Function.comp_apply, u, s]
    exact ht _ (hs n).1 (hs n).2
  have s_anti : Antitone s := by
    apply antitone_nat_of_succ_le (fun n ↦ ?_)
    simp only [Function.iterate_succ', Function.comp_apply, s]
    apply t_subs _ (hs n).1 (hs n).2
  have u_disj : Pairwise (Disjoint on u) := by
    apply (pairwise_disjoint_on _).2 (fun m n hmn ↦ ?_)
    have : Disjoint (u m) (s (m + 1)) := by simp [u, disjoint_sdiff_left]
    apply this.mono_right
    simp only [sdiff_le_iff, sup_eq_union, le_eq_subset, u]
    exact Subset.trans (s_anti (by grind)) subset_union_right
  have : HasSum (fun i => μ (u i)) (μ (⋃ i, u i)) :=
    hasSum_of_disjoint_iUnion (fun n ↦ (hs n).1.diff (hs (n + 1)).1) u_disj
  have : Tendsto (fun x ↦ ‖μ (u x)‖ₑ) atTop (𝓝 0) :=
    tendsto_zero_iff_enorm_tendsto_zero.1 this.summable.tendsto_atTop_zero
  obtain ⟨n, hn⟩ : ∃ n, ‖μ (u n)‖ₑ < 1 := ((tendsto_order.1 this).2 _ zero_lt_one).exists
  order [hu n]

variable (μ) in
/-- A constant bounding the norm of `μ s` for any set `s`. -/
protected noncomputable def bound : ℝ≥0 := (μ.semivariation univ).toNNReal

lemma semivariation_apply_le_bound : μ.semivariation s ≤ μ.bound := by
  apply (semivariation_mono (subset_univ _)).trans_eq
  simp only [VectorMeasure.bound]
  rw [ENNReal.coe_toNNReal semivariation_univ_lt_top.ne]

lemma enorm_apply_le_bound : ‖μ s‖ₑ ≤ μ.bound :=
  (enorm_apply_le_semivariation).trans semivariation_apply_le_bound

lemma nnnorm_apply_le_bound : ‖μ s‖₊ ≤ μ.bound := by
  rw [← ENNReal.coe_le_coe, ← enorm_eq_nnnorm]
  exact enorm_apply_le_bound

lemma norm_apply_le_bound : ‖μ s‖ ≤ μ.bound := by
  simpa [← coe_nnnorm] using nnnorm_apply_le_bound

end MeasureTheory.VectorMeasure
