/-
Copyright (c) 2025 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.TwoSidedIdeal.BigOperators
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Span as a Sum

In this file, we show that any element in the span of a set `s` is a finite sum of the form
`∑ i, rᵢ * sᵢ * rᵢ'` where `rᵢ, rᵢ' ∈ R, sᵢ ∈ s` .

## Main Results

* `TwoSidedIdeal.mem_span_iff_exists_fin`: `x ∈ span s` iff there exists a linear combination
  `∑ i, rᵢ * sᵢ * rᵢ' = x` where only finite terms are non-zero.
* `TwoSidedIdeal.mem_span_ideal_iff_exists_fin`: elements in the two-sided ideal closure of an
  (left) ideal `I` is in the form of `∑ i, xᵢ * rᵢ`(`rᵢ ∈ R` and `xᵢ ∈ I`) where only
  finite terms are non-zero.

-/
variable {R : Type*} [Ring R]

namespace TwoSidedIdeal

private def span' (s : Set R) : TwoSidedIdeal R := .mk'
  {x | ∃ (ι : Type) (fin : Fintype ι) (xL : ι → R) (xR : ι → R) (y : ι → s),
    x = ∑ i : ι, xL i * y i * xR i}
  ⟨Empty, Fintype.instEmpty, Empty.elim, Empty.elim, Empty.elim, by simp⟩
  (by
    rintro _ _ ⟨na, fina, xLa, xRa, ya, rfl⟩ ⟨nb, finb, xLb, xRb, yb, rfl⟩
    refine ⟨na ⊕ nb, inferInstance, Sum.elim xLa xLb, Sum.elim xRa xRb, Sum.elim ya yb, by
      simp⟩)
  (by
    rintro _ ⟨n, finn, xL, xR, y, rfl⟩
    exact ⟨n, finn, -xL, xR, y, by simp⟩)
  (by
    rintro a _ ⟨n, finn, xL, xR, y, rfl⟩
    exact ⟨n, finn, a • xL, xR, y, by
      rw [Finset.mul_sum]; simp only [mul_assoc, Pi.smul_apply, smul_eq_mul]⟩)
  (by
    rintro _ b ⟨n, finn, xL, xR, y, rfl⟩
    exact ⟨n, finn, xL, fun x ↦ xR x * b, y, by simp [Finset.sum_mul, mul_assoc]⟩)

private lemma mem_span'_iff_exists_fin (s : Set R) (x : R) :
    x ∈ span' s ↔
    ∃ (ι : Type) (_ : Fintype ι) (xL : ι → R) (xR : ι → R) (y : ι → s),
    x = ∑ i : ι, xL i * (y i : R) * xR i := by
  simp only [span', mem_mk', Set.mem_setOf_eq]

lemma mem_span_iff_exists_fin (s : Set R) (x : R) :
    x ∈ span s ↔
    ∃ (ι : Type) (_ : Fintype ι) (xL : ι → R) (xR : ι → R) (y : ι → s),
    x = ∑ i : ι, xL i * (y i : R) * xR i := by
  suffices eq1 : span s = span' s by
    rw [eq1]
    simp only [span', Set.mem_setOf_eq]
    generalize_proofs h1 h2 h3 h4 h5
    simp_all only [mem_mk', Set.mem_setOf_eq]

  rw [span, RingCon.ringConGen_eq]
  apply ringCon_injective
  refine sInf_eq_of_forall_ge_of_forall_gt_exists_lt ?_ ?_
  · rintro I (hI : ∀ a b, _ → _)
    suffices span' s ≤ .mk I by
      rw [ringCon_le_iff] at this
      exact this
    intro x h
    rw [mem_span'_iff_exists_fin] at h
    obtain ⟨n, finn, xL, xR, y, rfl⟩ := h
    rw [mem_iff]
    refine TwoSidedIdeal.finsetSum_mem _ _ _ fun i _ ↦ TwoSidedIdeal.mul_mem_right _ _ _
      (TwoSidedIdeal.mul_mem_left _ _ _ <| hI (y i) 0 (by simp))
  · rintro I hI
    exact ⟨(span' s).ringCon, fun a b H ↦ ⟨PUnit, inferInstance, fun _ ↦ 1, fun _ ↦ 1,
      fun _ ↦ ⟨a - b, by simp [H]⟩, by simp⟩, hI⟩

lemma mem_span_ideal_iff_exists_fin (s : Ideal R) (x : R) :
    x ∈ span s ↔
    ∃ (ι : Type) (_ : Fintype ι) (xR : ι → R) (y : ι → s),
    x = ∑ i : ι, (y i : R) * xR i := by
  rw [mem_span_iff_exists_fin]
  exact ⟨fun ⟨n, fin, xL, xR, y, _⟩ ↦ ⟨n, fin, xR, fun i ↦ ⟨xL i * y i, s.mul_mem_left _ (y i).2⟩,
    by simp_all⟩, fun ⟨n, fin, xR, y, hy⟩ ↦ ⟨n, fin, 1, xR, y, by simp_all⟩⟩

end TwoSidedIdeal
