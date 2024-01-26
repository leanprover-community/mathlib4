/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Abel's limit theorem

## References

* https://planetmath.org/proofofabelslimittheorem
* https://en.wikipedia.org/wiki/Abel%27s_theorem
-/


open Finset Filter

open scoped BigOperators Topology

namespace Complex

section StolzSet

/-- The Stolz set for a given `M`, roughly teardrop-shaped with the tip at 1 but tending to the
open unit disc as `M` tends to infinity. -/
def stolzSet (M : ℝ) : Set ℂ := {z | ‖z‖ < 1 ∧ ‖1 - z‖ < M * (1 - ‖z‖)}

theorem stolzSet_empty {M : ℝ} (hM : M ≤ 1) : stolzSet M = ∅ := by
  ext z
  rw [stolzSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt, ← sub_pos]
  intro zn
  calc
    _ ≤ 1 * (1 - ‖z‖) := mul_le_mul_of_nonneg_right hM zn.le
    _ = ‖(1 : ℂ)‖ - ‖z‖ := by rw [one_mul, norm_one]
    _ ≤ _ := norm_sub_norm_le _ _

end StolzSet

variable {f : ℕ → ℂ} {l : ℂ} (h : Tendsto (fun n ↦ ∑ i in range n, f i) atTop (𝓝 l))

/-- Auxiliary lemma for Abel's limit theorem. The difference between the sum `l` at 1 and the
power series's value at a point `z` away from 1 can be rewritten as `1 - z` times a power series
whose coefficients are tail sums of `l`. -/
lemma abel_aux {z : ℂ} (hz : ‖z‖ < 1) :
    Tendsto (fun n ↦ (1 - z) * ∑ i in range n, (l - ∑ j in range (i + 1), f j) * z ^ i)
      atTop (𝓝 (l - ∑' n, f n * z ^ n)) := by
  let s := fun n ↦ ∑ i in range n, f i
  have k := h.sub (summable_power_of_norm_lt_one h.cauchySeq hz).hasSum.tendsto_sum_nat
  simp_rw [← sum_sub_distrib, ← mul_one_sub, ← geom_sum_mul_neg, ← mul_assoc, ← sum_mul,
    mul_comm, mul_sum _ _ (f _), range_eq_Ico, ← sum_Ico_Ico_comm', ← range_eq_Ico,
    ← sum_mul] at k
  conv at k =>
    enter [1, n]
    rw [sum_congr (g := fun j ↦ (∑ k in range n, f k - ∑ k in range (j + 1), f k) * z ^ j)
      rfl (fun j hj ↦ by congr 1; exact sum_Ico_eq_sub _ (mem_range.mp hj))]
  suffices : Tendsto (fun n ↦ (l - s n) * ∑ i in range n, z ^ i) atTop (𝓝 0)
  · simp_rw [mul_sum] at this
    replace this := (this.const_mul (1 - z)).add k
    conv at this =>
      enter [1, n]
      rw [← mul_add, ← sum_add_distrib]
      enter [2, 2, i]
      rw [← add_mul, sub_add_sub_cancel]
    rwa [mul_zero, zero_add] at this
  refine' squeeze_zero_norm (a := fun n ↦ ‖l - s n‖ * 2 / ‖1 - z‖) (fun n ↦ _) _
  · dsimp only
    rw [geom_sum_eq (by contrapose! hz; simp [hz]), ← mul_div_assoc, norm_div, norm_mul,
      norm_sub_rev _ 1, norm_sub_rev _ 1]
    gcongr
    calc
      ‖1 - z ^ n‖ ≤ ‖1‖ + ‖z ^ n‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by
        rw [norm_one, norm_pow, add_le_add_iff_left]
        exact pow_le_one _ (norm_nonneg _) hz.le
      _ = 2 := by norm_num
  · simp_rw [mul_div_assoc]
    convert (h.const_sub _).norm.mul_const _
    simp

/-- **Abel's limit theorem**. Given a power series converging at 1, the corresponding function
is continuous at 1 when approaching 1 within a fixed Stolz set. -/
theorem tendsto_tsum_power_nhdsWithin_stolzSet {M : ℝ} :
    Tendsto (fun z ↦ ∑' n, f n * z ^ n) (𝓝[stolzSet M] 1) (𝓝 l) := by
  -- If `1 ≤ M` the Stolz set is empty and the statement is trivial
  cases' le_or_lt M 1 with hM hM
  · simp_rw [stolzSet_empty hM, nhdsWithin_empty, tendsto_bot]
  -- Abbreviations
  let s := fun n ↦ ∑ i in range n, f i
  let g := fun z ↦ ∑' n, f n * z ^ n
  have hm := Metric.tendsto_atTop.mp h
  rw [Metric.tendsto_nhdsWithin_nhds]
  simp only [dist_eq_norm] at hm ⊢
  -- Introduce the "challenge" `ε`
  intro ε εpos
  -- First bound, handles the tail
  obtain ⟨B₁, hB₁⟩ := hm (ε / 4 / M) (by positivity)
  -- Second bound, handles the head
  let F := ∑ i in range B₁, ‖l - s (i + 1)‖
  have Fnonneg : 0 ≤ F := sum_nonneg (fun _ _ ↦ by positivity)
  use ε / 4 / (F + 1), by positivity
  intro z ⟨zn, zm⟩ zd
  have p := abel_aux h zn
  simp_rw [Metric.tendsto_atTop, dist_eq_norm, norm_sub_rev] at p
  -- Third bound, regarding the distance between `l - g z` and the rearranged sum
  obtain ⟨B₂, hB₂⟩ := p (ε / 2) (by positivity)
  clear hm p
  replace hB₂ := hB₂ (max B₁ B₂) (by simp)
  suffices : ‖(1 - z) * ∑ i in range (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ < ε / 2
  · calc
      _ = ‖l - g z‖ := by rw [norm_sub_rev]
      _ = ‖l - g z - (1 - z) * ∑ i in range (max B₁ B₂), (l - s (i + 1)) * z ^ i +
          (1 - z) * ∑ i in range (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := by rw [sub_add_cancel _]
      _ ≤ ‖l - g z - (1 - z) * ∑ i in range (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ +
          ‖(1 - z) * ∑ i in range (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hB₂ this
      _ = _ := add_halves ε
  -- We break the rearranged sum along `B₁`
  calc
    _ = ‖(1 - z) * ∑ i in range B₁, (l - s (i + 1)) * z ^ i +
        (1 - z) * ∑ i in Ico B₁ (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := by
      rw [← mul_add, sum_range_add_sum_Ico _ (le_max_left B₁ B₂)]
    _ ≤ ‖(1 - z) * ∑ i in range B₁, (l - s (i + 1)) * z ^ i‖ +
        ‖(1 - z) * ∑ i in Ico B₁ (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := norm_add_le _ _
    _ = ‖1 - z‖ * ‖∑ i in range B₁, (l - s (i + 1)) * z ^ i‖ +
        ‖1 - z‖ * ‖∑ i in Ico B₁ (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ ‖1 - z‖ * ∑ i in range B₁, ‖l - s (i + 1)‖ * ‖z‖ ^ i +
        ‖1 - z‖ * ∑ i in Ico B₁ (max B₁ B₂), ‖l - s (i + 1)‖ * ‖z‖ ^ i := by
      gcongr <;> simp_rw [← norm_pow, ← norm_mul, norm_sum_le]
  -- then prove that the two pieces are each less than `ε / 4`
  have S₁ : ‖1 - z‖ * ∑ i in range B₁, ‖l - s (i + 1)‖ * ‖z‖ ^ i < ε / 4 :=
    calc
      _ ≤ ‖1 - z‖ * ∑ i in range B₁, ‖l - s (i + 1)‖ := by
        gcongr; nth_rw 2 [← mul_one ‖_‖]
        gcongr; exact pow_le_one _ (norm_nonneg _) zn.le
      _ ≤ ‖1 - z‖ * (F + 1) := by gcongr; linarith only
      _ < _ := by rwa [norm_sub_rev, lt_div_iff (by positivity)] at zd
  have S₂ : ‖1 - z‖ * ∑ i in Ico B₁ (max B₁ B₂), ‖l - s (i + 1)‖ * ‖z‖ ^ i < ε / 4 :=
    calc
      _ ≤ ‖1 - z‖ * ∑ i in Ico B₁ (max B₁ B₂), ε / 4 / M * ‖z‖ ^ i := by
        gcongr with i hi
        have := hB₁ (i + 1) (by linarith only [(mem_Ico.mp hi).1])
        rw [norm_sub_rev] at this
        exact this.le
      _ = ‖1 - z‖ * (ε / 4 / M) * ∑ i in Ico B₁ (max B₁ B₂), ‖z‖ ^ i := by
        rw [← mul_sum, ← mul_assoc]
      _ ≤ ‖1 - z‖ * (ε / 4 / M) * ∑' i, ‖z‖ ^ i := by
        gcongr
        exact sum_le_tsum _ (fun _ _ ↦ by positivity)
          (summable_geometric_of_lt_1 (by positivity) zn)
      _ = ‖1 - z‖ * (ε / 4 / M) / (1 - ‖z‖) := by
        rw [tsum_geometric_of_lt_1 (by positivity) zn, ← div_eq_mul_inv]
      _ < M * (1 - ‖z‖) * (ε / 4 / M) / (1 - ‖z‖) := by gcongr; linarith only [zn]
      _ = _ := by
        rw [← mul_rotate, mul_div_cancel _ (by linarith only [zn]),
          div_mul_cancel _ (by linarith only [hM])]
  convert add_lt_add S₁ S₂ using 1
  linarith only

end Complex
