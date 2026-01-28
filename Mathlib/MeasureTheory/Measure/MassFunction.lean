/-
Copyright (c) 2026 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Mass functions
This is about discrete measures as given by a (mass/weight) function `α → ℝ≥0∞`.
We define `MassFunction α := α → ℝ≥0∞`.

Given `μ : MassFunction α`, `MassFunction.toMeasure` constructs a `Measure α ⊤`,
by assigning each set the sum of the weights of each of its elements.
For this measure, every set is measurable.

## Main definitions
* `MassFunction`: A mass function (giving rise to a discrete measure) is a function `α → ℝ≥0∞`.

## Tags

mass function, weight function, discrete measure

-/

@[expose] public section

open MeasureTheory Measure Function

open scoped ENNReal

universe u

variable {α β γ δ : Type*}

open Classical in
lemma Function.support_subsingleton_of_disjoint [Zero β] {s : δ → Set α} (f : α → β)
    (hs : Pairwise (Disjoint on s)) (i : α) (j : δ) (hj : i ∈ s j) :
    Function.support (fun d ↦ if i ∈ s d then f i else 0) ⊆ {j} := by
  intro d
  simp_rw [Set.mem_singleton_iff, Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp]
  rw [← not_imp_not]
  intro hd e
  obtain r := Set.disjoint_iff_inter_eq_empty.mp (hs hd)
  revert r
  change s d ∩ s j ≠ ∅
  rw [← Set.nonempty_iff_ne_empty, Set.nonempty_def]
  exact ⟨i, ⟨e.1, hj⟩⟩

lemma Set.indicator_iUnion_of_disjoint [AddCommMonoid β] [TopologicalSpace β]
    (s : δ → Set α) (hs : Pairwise (Disjoint on s)) (f : α → β) (i : α) :
    (⋃ d, s d).indicator f i = ∑' d, (s d).indicator f i := by
  classical
  simp only [Set.indicator, Set.mem_iUnion]
  by_cases h₀ : ∃ d, i ∈ s d <;> simp only [h₀, ↓reduceIte]
  · obtain ⟨j, hj⟩ := h₀
    rw [← tsum_subtype_eq_of_support_subset (s := {j})]
    · simp only [tsum_fintype, Finset.univ_unique, Set.default_coe_singleton, Finset.sum_singleton,
      left_eq_ite_iff]
      exact fun h ↦ False.elim (h hj)
    · apply (support_subsingleton_of_disjoint f hs i j hj)
  · push_neg at h₀
    simp_rw [if_neg (h₀ _), tsum_zero]

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
lemma toMeasure_apply_singleton (μ : MassFunction α) (a : α) : μ.toMeasure {a} = μ a := by
  simp only [toMeasure_apply, Set.indicator.mul_indicator_eq]
  rw [← tsum_subtype, tsum_singleton]

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
  simp only [toMeasure_apply, Set.indicator.mul_indicator_eq]
  rw [ENNReal.tsum_comm]
  exact tsum_congr (fun b ↦ Set.indicator_iUnion_of_disjoint s hs μ b)

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
  rw [← toMeasure_apply_singleton μ, ← toMeasure_apply_singleton ν, h]

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
