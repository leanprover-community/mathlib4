/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.OuterMeasure.AE

/-!
# Borel-Cantelli lemma, part 1

In this file we show one implication of the **Borel-Cantelli lemma**:
if `s i` is a countable family of sets such that `∑' i, μ (s i)` is finite,
then a.e. all points belong to finitely many sets of the family.

We prove several versions of this lemma:

- `MeasureTheory.ae_finite_setOf_mem`: as stated above;
- `MeasureTheory.measure_limsup_cofinite_eq_zero`:
  in terms of `Filter.limsup` along `Filter.cofinite`;
- `MeasureTheory.measure_limsup_atTop_eq_zero`:
  in terms of `Filter.limsup` along `(Filter.atTop : Filter ℕ)`.

For the *second* Borel-Cantelli lemma (applying to independent sets in a probability space),
see `ProbabilityTheory.measure_limsup_eq_one`.
-/

public section

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

/-- One direction of the **Borel-Cantelli lemma**
(sometimes called the "*first* Borel-Cantelli lemma"):
if `(s i)` is a countable family of sets such that `∑' i, μ (s i)` is finite,
then a.e. all points belong to finitely many sets of the family. -/
theorem ae_finite_setOf_mem {s : ι → Set α} (h : ∑' i, μ (s i) ≠ ∞) :
    ∀ᵐ x ∂μ, {i | x ∈ s i}.Finite := by
  rw [ae_iff, ← measure_limsup_cofinite_eq_zero h]
  congr 1 with x
  simp [mem_limsup_iff_frequently_mem, Filter.Frequently]

/-- A version of the **Borel-Cantelli lemma**: if `pᵢ` is a sequence of predicates such that
`∑' i, μ {x | pᵢ x}` is finite, then the measure of `x` such that `pᵢ x` holds frequently as `i → ∞`
(or equivalently, `pᵢ x` holds for infinitely many `i`) is equal to zero. -/
theorem measure_setOf_frequently_eq_zero {p : ℕ → α → Prop} (hp : ∑' i, μ { x | p i x } ≠ ∞) :
    μ { x | ∃ᶠ n in atTop, p n x } = 0 := by
  simpa only [limsup_eq_iInf_iSup_of_nat, frequently_atTop, ← bex_def, setOf_forall,
    setOf_exists] using measure_limsup_atTop_eq_zero hp

/-- A version of the **Borel-Cantelli lemma**: if `sᵢ` is a sequence of sets such that
`∑' i, μ sᵢ` is finite, then for almost all `x`, `x` does not belong to `sᵢ` for large `i`. -/
theorem ae_eventually_notMem {s : ℕ → Set α} (hs : (∑' i, μ (s i)) ≠ ∞) :
    ∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∉ s n :=
  measure_setOf_frequently_eq_zero hs

theorem measure_liminf_cofinite_eq_zero [Infinite ι] {s : ι → Set α} (h : ∑' i, μ (s i) ≠ ∞) :
    μ (liminf s cofinite) = 0 := by
  rw [← nonpos_iff_eq_zero, ← measure_limsup_cofinite_eq_zero h]
  exact measure_mono liminf_le_limsup

theorem measure_liminf_atTop_eq_zero {s : ℕ → Set α} (h : (∑' i, μ (s i)) ≠ ∞) :
    μ (liminf s atTop) = 0 := by
  rw [← Nat.cofinite_eq_atTop, measure_liminf_cofinite_eq_zero h]

-- TODO: the next 2 lemmas are true for any filter with countable intersections, not only `ae`.
-- Need to specify `α := Set α` below because of diamond; see https://github.com/leanprover-community/mathlib4/pull/19041
theorem limsup_ae_eq_of_forall_ae_eq (s : ℕ → Set α) {t : Set α}
    (h : ∀ n, s n =ᵐˢ[μ] t) : limsup s atTop =ᵐˢ[μ] t := by
  simp only [eventuallyEqSet_iff, ← eventually_countable_forall] at h
  refine eventuallyEqSet_iff.2 <| h.mono fun x hx ↦ ?_
  simp [mem_limsup_iff_frequently_mem, hx]

-- Need to specify `α := Set α` above because of diamond; see https://github.com/leanprover-community/mathlib4/pull/19041
theorem liminf_ae_eq_of_forall_ae_eq (s : ℕ → Set α) {t : Set α}
    (h : ∀ n, s n =ᵐˢ[μ] t) : liminf (α := Set α) s atTop =ᵐˢ[μ] t := by
  simp only [eventuallyEqSet_iff, ← eventually_countable_forall] at h
  refine eventuallyEqSet_iff.2 <| h.mono fun x hx ↦ ?_
  simp only [mem_liminf_iff_eventually_mem, hx, eventually_const]

end MeasureTheory
