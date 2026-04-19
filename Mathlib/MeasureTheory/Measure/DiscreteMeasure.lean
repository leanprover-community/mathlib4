/-
Copyright (c) 2026 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Discrete Measures
This is about discrete measures as given by a weight function `α → ℝ≥0∞`.

Given `μ : DiscreteMeasure α`, `DiscreteMeasure.toMeasure` constructs a `Measure α` as a sum of
`dirac`s.

## Main definitions
* `DiscreteMeasure`: A discrete Measure, given by its weight function `α → ℝ≥0∞`.

## Tags
mass function, weight function, discrete measure

-/

@[expose] public section

open MeasureTheory Measure Function

open scoped ENNReal

universe u

variable {α β γ δ : Type*}

open ENNReal MeasureTheory

namespace MeasureTheory

/-- A `DiscreteMeasure α` is given by its weight function `α → ℝ≥0∞`. -/
structure DiscreteMeasure (α : Type*) : Type _ where
  /-- The weight function of the discrete measure. -/
  weight : α → ℝ≥0∞

namespace DiscreteMeasure

/-- The `Measure α` as defined through a `DiscreteMeasure α` (mass function) through a weighted sum
of diracs, using a given `MeasurableSpace α`. -/
noncomputable def toMeasure [MeasurableSpace α] (μ : DiscreteMeasure α) : Measure α :=
  Measure.sum (fun x ↦ μ.weight x • .dirac x)

noncomputable instance [MeasurableSpace α] : Coe (DiscreteMeasure α) (Measure α) where
  coe μ := μ.toMeasure

instance instFunLike : FunLike (DiscreteMeasure α) α ℝ≥0∞ where
  coe p a := p.weight a
  coe_injective' p q h := by
    cases p
    cases q
    simp_all

@[simp]
lemma weight_eq (μ : DiscreteMeasure α) (x : α) : μ.weight x = μ x := by rfl

@[ext]
protected theorem ext {v w : DiscreteMeasure α} (h : ∀ x, v x = w x) : v = w :=
  DFunLike.ext v w h

theorem mem_support_iff (w : DiscreteMeasure α) (a : α) : a ∈ w.weight.support ↔ w a ≠ 0 := Iff.rfl

theorem apply_eq_zero_iff (w : DiscreteMeasure α) (a : α) : w a = 0 ↔ a ∉ w.weight.support := by
  rw [mem_support_iff, Classical.not_not]

theorem apply_pos_iff (w : DiscreteMeasure α) (a : α) : 0 < w a ↔ a ∈ w.weight.support :=
  pos_iff_ne_zero.trans (w.mem_support_iff a).symm

lemma toMeasure_apply' [MeasurableSpace α] (μ : DiscreteMeasure α) {s : Set α}
    (hs : MeasurableSet s) : μ.toMeasure s = ∑' (a : α), (μ.weight a) • dirac a s := by
  rw [toMeasure, sum_apply (hs := hs)]
  simp_rw [smul_apply]

lemma toMeasure_apply_eq_tsum_mul [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : DiscreteMeasure α) {s : Set α} (hs : MeasurableSet s) :
    μ.toMeasure s = ∑' (i : α), μ i * s.indicator 1 i := by
  rw [μ.toMeasure_apply' hs]
  simp

lemma toMeasure_apply [MeasurableSpace α] [MeasurableSingletonClass α] (μ : DiscreteMeasure α)
    {s : Set α} (hs : MeasurableSet s) : μ.toMeasure s = ∑' (i : α), s.indicator μ i := by
  simp [μ.toMeasure_apply_eq_tsum_mul hs]

lemma toMeasure_apply_tsum_subtype [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : DiscreteMeasure α) {s : Set α} (hs : MeasurableSet s) :
    μ.toMeasure s = ∑' (a : s), (μ a) := by
  simp [μ.toMeasure_apply_eq_tsum_mul hs, _root_.tsum_subtype]

@[simp]
lemma toMeasure_apply_singleton [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : DiscreteMeasure α) (a : α) : μ.toMeasure {a} = μ a := by
  simp only [μ.toMeasure_apply_eq_tsum_mul (measurableSet_singleton a), Set.indicator.mul_indicator_eq,
    ←tsum_subtype, tsum_singleton]

theorem toMeasure_apply_eq_zero_iff [MeasurableSpace α] [MeasurableSingletonClass α]
    {μ : DiscreteMeasure α} {s : Set α} (hs : MeasurableSet s) :
    μ.toMeasure s = 0 ↔ Disjoint μ.weight.support s := by
  rw [toMeasure_apply (hs := hs), ENNReal.tsum_eq_zero]
  exact funext_iff.symm.trans Set.indicator_eq_zero'

@[simp]
theorem toMeasure_apply_inter_support [MeasurableSpace α] [MeasurableSingletonClass α]
    {μ : DiscreteMeasure α} {s u : Set α} (hs : MeasurableSet s) (hu : MeasurableSet u)
    (h : μ.weight.support ⊆ u) : μ.toMeasure (s ∩ u) = μ.toMeasure s := by
  simp only [toMeasure_apply_eq_tsum_mul (hs := hs), toMeasure_apply_eq_tsum_mul (hs := MeasurableSet.inter hs hu)]
  apply tsum_congr (fun a ↦ ?_)
  repeat rw [Set.indicator.mul_indicator_eq, Set.indicator]
  simp only [support_subset_iff, weight_eq, ne_eq] at h
  specialize h a
  aesop

theorem toMeasure_apply_eq_of_inter_support_eq [MeasurableSpace α] [MeasurableSingletonClass α]
    {μ : DiscreteMeasure α} {s t u : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hu : MeasurableSet u) (h_support : μ.weight.support ⊆ u)
    (h : s ∩ u = t ∩ u) : μ.toMeasure s = μ.toMeasure t := by
  rw [← toMeasure_apply_inter_support hs hu h_support,
    ← toMeasure_apply_inter_support ht hu h_support, h]

/- Additivity for `μ.toMeasure` for a `μ : DiscreteMeasure` not only applies to countable unions,
but to arbitrary ones. -/
lemma toMeasure_additive [MeasurableSpace α] [MeasurableSingletonClass α] (μ : DiscreteMeasure α)
    {s : δ → Set α} (h₀ : ∀ d, MeasurableSet (s d)) (h₁ : MeasurableSet (⋃ d, s d))
    (hs : Pairwise (Disjoint on s)) : μ.toMeasure (⋃ d, s d) = ∑' (d : δ), μ.toMeasure (s d) := by
  simp only [toMeasure_apply_eq_tsum_mul (hs := h₁), Set.indicator.mul_indicator_eq]
  conv => right; left; intro d; rw [toMeasure_apply_eq_tsum_mul (hs := h₀ _)]
  simp_rw [Set.indicator.mul_indicator_eq]
  rw [ENNReal.tsum_comm]
  apply tsum_congr <| fun b ↦ by rw [indicator_iUnion_of_pairwise_disjoint s hs μ]

theorem toMeasure_apply_finset [MeasurableSpace α] [MeasurableSingletonClass α]
    {μ : DiscreteMeasure α} {s : Finset α} : μ.toMeasure s = ∑ x ∈ s, μ x := by
  rw [toMeasure_apply (hs := by measurability), tsum_eq_sum (s := s)]
  · exact Finset.sum_indicator_subset μ fun ⦃a⦄ a_1 => a_1
  · exact fun b a => Set.indicator_of_notMem a μ

@[simp]
theorem toMeasure_apply_fintype [MeasurableSpace α] [MeasurableSingletonClass α]
    {μ : DiscreteMeasure α} {s : Set α} [Fintype α] : μ.toMeasure s = ∑ x, s.indicator μ x := by
  rw [μ.toMeasure_apply (by measurability)]
  exact tsum_fintype (s.indicator μ)

lemma toMeasure_apply_univ [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : DiscreteMeasure α) : μ.toMeasure Set.univ = ∑' (a : α), μ a := by
  simp [toMeasure_apply]

lemma toMeasure_apply_univ' [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : DiscreteMeasure α) {s : δ → Set α} (h : ∀ d, MeasurableSet (s d))
    (hs₀ : Pairwise (Disjoint on s)) (hs₁ : Set.univ = ⋃ d, s d) :
    μ.toMeasure Set.univ = ∑' (d : δ), μ.toMeasure (s d) := by
  rw [hs₁]
  exact toMeasure_additive μ h (Eq.symm hs₁ ▸ MeasurableSet.univ) hs₀

theorem toMeasure_injective [MeasurableSpace α] [MeasurableSingletonClass α] :
    (@toMeasure α _).Injective := by
  intro μ ν h
  ext x
  rw [← toMeasure_apply_singleton μ, ← toMeasure_apply_singleton ν, h]

@[simp]
theorem toMeasure_inj [MeasurableSpace α] [MeasurableSingletonClass α] {μ ν : DiscreteMeasure α} :
    μ.toMeasure = ν.toMeasure ↔ μ = ν :=
  toMeasure_injective.eq_iff

theorem toMeasure_ext [MeasurableSpace α] [MeasurableSingletonClass α] {μ ν : DiscreteMeasure α}
    (h : μ.toMeasure = ν.toMeasure) : μ = ν :=
  toMeasure_inj.mp h

theorem toMeasure_mono [MeasurableSpace α] [MeasurableSingletonClass α] {s t u : Set α}
    (hs : MeasurableSet s) (hu : MeasurableSet u) {μ : DiscreteMeasure α} (h : s ∩ u ⊆ t)
    (h_support : μ.weight.support ⊆ u) :
    μ.toMeasure s ≤ μ.toMeasure t := by
  rw [← μ.toMeasure_apply_inter_support hs hu h_support]
  exact OuterMeasureClass.measure_mono μ.toMeasure h

@[simp]
theorem restrict_toMeasure_support [MeasurableSpace α] [MeasurableSingletonClass α]
    {μ : DiscreteMeasure α} {u : Set α} (hu : MeasurableSet u) (h : μ.weight.support ⊆ u) :
    μ.toMeasure.restrict u = μ.toMeasure := by
  apply Measure.ext
  intro s hs
  rw [Measure.restrict_apply hs, μ.toMeasure_apply_inter_support hs hu h]

end DiscreteMeasure

end MeasureTheory
