/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Yury Kudryashov
-/
import Mathlib.MeasureTheory.OuterMeasure.AE

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory

variable {α ι F : Type*} [FunLike F (Set α) ℝ≥0∞] [OuterMeasureClass F α] [Countable ι] {μ : F}

/-- One direction of the **Borel-Cantelli lemma**
(sometimes called the "*first* Borel-Cantelli lemma"):
if `(s i)` is a countable family of sets such that `∑' i, μ (s i)` is finite,
then the limit superior of the `s i` along the cofinite filter is a null set.

Note: for the *second* Borel-Cantelli lemma (applying to independent sets in a probability space),
see `ProbabilityTheory.measure_limsup_eq_one`. -/
theorem measure_limsup_cofinite_eq_zero {s : ι → Set α} (hs : ∑' i, μ (s i) ≠ ∞) :
    μ (limsup s cofinite) = 0 := by
  refine bot_unique <| ge_of_tendsto' (ENNReal.tendsto_tsum_compl_atTop_zero hs) fun t ↦ ?_
  calc
    μ (limsup s cofinite) ≤ μ (⋃ i : {i // i ∉ t}, s i) := by
      gcongr
      rw [hasBasis_cofinite.limsup_eq_iInf_iSup, iUnion_subtype]
      exact iInter₂_subset _ t.finite_toSet
    _ ≤ ∑' i : {i // i ∉ t}, μ (s i) := measure_iUnion_le _

/-- One direction of the **Borel-Cantelli lemma**
(sometimes called the "*first* Borel-Cantelli lemma"):
if `(s i)` is a sequence of sets such that `∑' i, μ (s i)` is finite,
then the limit superior of the `s i` along the `atTop` filter is a null set.

Note: for the *second* Borel-Cantelli lemma (applying to independent sets in a probability space),
see `ProbabilityTheory.measure_limsup_eq_one`. -/
theorem measure_limsup_atTop_eq_zero {s : ℕ → Set α} (hs : ∑' i, μ (s i) ≠ ∞) :
    μ (limsup s atTop) = 0 := by
  rw [← Nat.cofinite_eq_atTop, measure_limsup_cofinite_eq_zero hs]

@[deprecated (since := "2024-09-01")]
alias measure_limsup_eq_zero := measure_limsup_atTop_eq_zero

/-- One direction of the **Borel-Cantelli lemma**
(sometimes called the "*first* Borel-Cantelli lemma"):
if `(s i)` is a countable family of sets such that `∑' i, μ (s i)` is finite,
then a.e. all points belong to finitely sets of the family. -/
theorem ae_finite_setOf_mem {s : ι → Set α} (h : ∑' i, μ (s i) ≠ ∞) :
    ∀ᵐ x ∂μ, {i | x ∈ s i}.Finite := by
  rw [ae_iff, ← measure_limsup_cofinite_eq_zero h]
  congr 1 with x
  simp [mem_limsup_iff_frequently_mem, Filter.Frequently]

theorem measure_liminf_cofinite_eq_zero [Infinite ι]  {s : ι → Set α} (h : ∑' i, μ (s i) ≠ ∞) :
    μ (liminf s cofinite) = 0 := by
  rw [← le_zero_iff, ← measure_limsup_cofinite_eq_zero h]
  exact measure_mono liminf_le_limsup

theorem measure_liminf_atTop_eq_zero {s : ℕ → Set α} (h : (∑' i, μ (s i)) ≠ ∞) :
    μ (liminf s atTop) = 0 := by
  rw [← Nat.cofinite_eq_atTop, measure_liminf_cofinite_eq_zero h]

-- Need to specify `α := Set α` below because of diamond; see #19041
theorem limsup_ae_eq_of_forall_ae_eq (s : ℕ → Set α) {t : Set α}
    (h : ∀ n, s n =ᵐ[μ] t) : limsup (α := Set α) s atTop =ᵐ[μ] t := by
  simp_rw [ae_eq_set] at h ⊢
  constructor
  · rw [atTop.limsup_sdiff s t]
    apply measure_limsup_atTop_eq_zero
    simp [h]
  · rw [atTop.sdiff_limsup s t]
    apply measure_liminf_atTop_eq_zero
    simp [h]

-- Need to specify `α := Set α` above because of diamond; see #19041
theorem liminf_ae_eq_of_forall_ae_eq (s : ℕ → Set α) {t : Set α}
    (h : ∀ n, s n =ᵐ[μ] t) : liminf (α := Set α) s atTop =ᵐ[μ] t := by
  simp_rw [ae_eq_set] at h ⊢
  constructor
  · rw [atTop.liminf_sdiff s t]
    apply measure_liminf_atTop_eq_zero
    simp [h]
  · rw [atTop.sdiff_liminf s t]
    apply measure_limsup_atTop_eq_zero
    simp [h]

end MeasureTheory
