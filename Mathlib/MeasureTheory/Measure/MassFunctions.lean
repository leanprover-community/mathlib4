/-
Copyright (c) 2026 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/

import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Order.BourbakiWitt

/-!
# Mass functions
This file is about discrete measures as given by a (mass/weight) function `α → ℝ≥0∞`.
We define `MassFunction α := α → ℝ≥0∞`.

Given `μ : MassFunction α`, `MassFunction.toMeasure` constructs a `Measure α ⊤`,
by assigning each set the sum of the weights of each of its elements.
For this measure, every set is measurable.

## Main definitions
* `MassFunction`: A mass function (giving rise to a discrete measure) is a function `α → ℝ≥0∞`.

## Tags

weight function, discrete measure

-/

open MeasureTheory Measure Function

open scoped ENNReal

universe u

variable {α β γ δ : Type*}

lemma Set.PairwiseDisjoint.singleton_subtype (s : Set α) :
    Pairwise (Disjoint on fun (x : s) => ({x.val} : Set α)) := by
  intro a b hab
  simp_rw [Set.disjoint_singleton_left, Set.mem_singleton_iff, Subtype.coe_ne_coe.mpr hab,
    not_false_eq_true]

lemma Set.PairwiseDisjoint.fiber_subtype {g : α → β} (s : Set β) :
    Pairwise (Disjoint on fun (x : s) => (g⁻¹' {x.val} : Set α)) :=
  fun _ _ hab ↦ pairwise_disjoint_fiber g (Subtype.coe_ne_coe.mpr hab)

open ENNReal MeasureTheory

namespace MeasureTheory

/-- A mass function (giving rise to a discrete measure) is a function `α → ℝ≥0∞`. -/
def MassFunction (α : Type u) : Type u := α → ℝ≥0∞

namespace MassFunction

instance instFunLike : FunLike (MassFunction α) α ℝ≥0∞ where
  coe p a := p a
  coe_injective' _ _ h := h

@[ext]
protected theorem ext {v w : MassFunction α} (h : ∀ x, v x = w x) : v = w :=
  DFunLike.ext v w h

/-- The support of a `MassFunction` is the set where it is nonzero. -/
def support (w : MassFunction α) : Set α := Function.support w

@[simp]
theorem mem_support_iff (w : MassFunction α) (a : α) : a ∈ w.support ↔ w a ≠ 0 := Iff.rfl

theorem apply_eq_zero_iff (w : MassFunction α) (a : α) : w a = 0 ↔ a ∉ w.support := by
  rw [mem_support_iff, Classical.not_not]

theorem apply_pos_iff (w : MassFunction α) (a : α) : 0 < w a ↔ a ∈ w.support :=
  pos_iff_ne_zero.trans (w.mem_support_iff a).symm

/-- The `@Measure α ⊤` as defined through a `MassFunction α` (mass function) through a sum of
diracs. -/
noncomputable def toMeasure (w : MassFunction α) : @Measure α ⊤ :=
  Measure.sum (fun a ↦ (w a) • @Measure.dirac α ⊤ a)

lemma toMeasure_apply (μ : MassFunction α) (s : Set α) :
    μ.toMeasure s = ∑' (i : α), μ i * s.indicator 1 i := by
  simp [toMeasure]

lemma toMeasure_apply₁ (μ : MassFunction α) (s : Set α) :
    μ.toMeasure s = ∑' (i : α), s.indicator μ i := by
  simp [toMeasure_apply]

lemma toMeasure_apply₂ (μ : MassFunction α) (s : Set α) : μ.toMeasure s = ∑' (a : s), (μ a) := by
  simp [toMeasure_apply, tsum_subtype]

@[simp]
lemma toMeasure_apply_singleton (μ : MassFunction α) (a : α) :
    ∑' (i : α), ({a} : Set α).indicator μ i = μ a := by
  rw [← tsum_subtype, tsum_singleton]

@[simp]
lemma toMeasure_apply_singleton' (μ : MassFunction α) (a : α) : μ.toMeasure {a} = μ a := by
  simp [toMeasure_apply]

lemma toMeasure_singleton_eq (μ : MassFunction α) : (fun (a : α) ↦ μ.toMeasure {a}) = μ := by
  simp [toMeasure_apply]

theorem toMeasure_apply_eq_zero_iff {μ : MassFunction α} {s : Set α} :
    μ.toMeasure s = 0 ↔ Disjoint μ.support s := by
  rw [toMeasure_apply₁, ENNReal.tsum_eq_zero]
  exact funext_iff.symm.trans Set.indicator_eq_zero'

@[simp]
theorem toMeasure_apply_inter_support {μ : MassFunction α} {s : Set α} :
    μ.toMeasure (s ∩ μ.support) = μ.toMeasure s := by
  simp only [toMeasure_apply, support]
  apply tsum_congr (fun a ↦ ?_)
  aesop

theorem toMeasure_apply_eq_of_inter_support_eq {μ : MassFunction α} {s t : Set α}
    (h : s ∩ μ.support = t ∩ μ.support) : μ.toMeasure s = μ.toMeasure t := by
  rw [← toMeasure_apply_inter_support (s := s), ← toMeasure_apply_inter_support (s := t), h]

/- Additivity for `μ.toMeasure` for a `μ : MassFunction` not only applies to countable unions, but
to arbitrary ones. -/
lemma toMeasure_additive (μ : MassFunction α) (s : δ → Set α) (hs : Pairwise (Disjoint on s)) :
    μ.toMeasure (⋃ d, s d) = ∑' (d : δ), μ.toMeasure (s d) := by
  simp only [toMeasure_apply]
  rw [ENNReal.tsum_comm]
  apply tsum_congr (fun b ↦ ?_)
  simp only [Set.indicator, Set.mem_iUnion]
  by_cases h₀ : ∃ i, b ∈ s i <;> simp only [Set.mem_iUnion, h₀, ↓reduceIte, Pi.one_apply,
    mul_one, mul_ite, mul_zero]
  · obtain ⟨i, hi⟩ := h₀
    rw [ENNReal.tsum_eq_add_tsum_ite i]
    simp only [hi, ↓reduceIte]
    nth_rw 1 [← add_zero (μ b)] ; congr
    apply (ENNReal.tsum_eq_zero.mpr ?_).symm
    simp only [ite_eq_left_iff, ite_eq_right_iff]
    exact fun j hj hb ↦ False.elim <| Disjoint.notMem_of_mem_left (hs (id (Ne.symm hj))) hi hb
  · refine (ENNReal.tsum_eq_zero.mpr (fun j ↦ ?_)).symm
    push_neg at h₀
    simp [h₀ j]

@[simp]
theorem toMeasure_apply_finset {μ : MassFunction α} (s : Finset α) : μ.toMeasure s = ∑ x ∈ s, μ x
    := by

  rw [toMeasure_apply₁, tsum_eq_sum (s := s)]
  · exact Finset.sum_indicator_subset μ fun ⦃a⦄ a_1 => a_1
  · exact fun b a => Set.indicator_of_notMem a μ

@[simp]
theorem toMeasure_apply_fintype {μ : MassFunction α} (s : Set α) [Fintype α] :
    μ.toMeasure s = ∑ x, s.indicator μ x := by
  rw [toMeasure_apply₁]
  exact tsum_fintype (s.indicator μ)

lemma toMeasure_apply_univ (μ : MassFunction α) : μ.toMeasure Set.univ = ∑' (a : α), μ a := by
  simp [toMeasure_apply]

lemma toMeasure_apply_univ' (μ : MassFunction α) (s : δ → Set α) (hs₀ : Pairwise (Disjoint on s))
    (hs₁ : Set.univ = ⋃ d, s d) : μ.toMeasure Set.univ = ∑' (d : δ), μ.toMeasure (s d) := by
  rw [hs₁]
  exact toMeasure_additive μ s hs₀

theorem toMeasure_injective : (toMeasure : MassFunction α → @Measure α ⊤).Injective := by
  intro μ ν h
  ext x
  rw [← toMeasure_apply_singleton' μ, ← toMeasure_apply_singleton' ν, h]

@[simp]
theorem toMeasure_inj {μ ν : MassFunction α} : μ.toMeasure = ν.toMeasure ↔ μ = ν :=
  toMeasure_injective.eq_iff

theorem toMeasure_ext {μ ν : MassFunction α} (h : μ.toMeasure = ν.toMeasure) : μ = ν :=
  toMeasure_inj.mp h

theorem toMeasure_mono {s t : Set α} {μ : MassFunction α} (h : s ∩ μ.support ⊆ t) :
    μ.toMeasure s ≤ μ.toMeasure t := by
  rw [← μ.toMeasure_apply_inter_support]
  exact OuterMeasureClass.measure_mono μ.toMeasure h

@[simp]
theorem restrict_toMeasure_support {μ : MassFunction α} :
    μ.toMeasure.restrict μ.support = μ.toMeasure := by
  apply @Measure.ext α ⊤
  intro s hs
  rw [Measure.restrict_apply hs, μ.toMeasure_apply_inter_support]

end MassFunction

end MeasureTheory
