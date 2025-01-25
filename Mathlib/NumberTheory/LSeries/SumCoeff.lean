/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.Basic

/-!
# Partial sums of coefficients of L-series

We prove several results involving partial sums of coefficients (or norm of coefficients) of
L-series.

## Main results

* `LSeriesSummable_of_sum_norm_bigO`: for `f : ℕ → ℂ`, if the partial sums
  `∑ k ∈ Icc 1 n, ‖f k‖` are `O(n ^ r)` for some real `0 ≤ r`, then the L-series `LSeries f`
  converges at `s : ℂ` for all `s` such that `r < s.re`.

* `LSeries_eq_mul_integral` : for `f : ℕ → ℂ`, if the partial sums `∑ k ∈ Icc 1 n, f k` are
  `O(n ^ r)` for some real `0 ≤ r` and the L-series `LSeries f` converges at `s : ℂ` with
  `r < s.re`, then `LSeries f s = s * ∫ t in Set.Ioi 1, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (- (s + 1))`.

-/

open Finset Filter MeasureTheory Topology Complex Asymptotics

section summable

variable {f : ℕ → ℂ} {r : ℝ} {s : ℂ}

private theorem LSeriesSummable_of_sum_norm_bigO_aux (hf : f 0 = 0)
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] fun n ↦ (n : ℝ) ^ r)
    (hr : 0 ≤ r) (hs : r < s.re) :
     LSeriesSummable f s := by
  have h₁ : -s ≠ 0 := neg_ne_zero.mpr <| ne_zero_of_re_pos (hr.trans_lt hs)
  have h₂ : (-s).re + r ≤ 0 := by
    rw [neg_re, neg_add_nonpos_iff]
    exact hs.le
  have h₃ : ∀ t ∈ Set.Ici (1 : ℝ), DifferentiableAt ℝ (fun x : ℝ ↦ ‖(x : ℂ) ^ (-s)‖) t := by
    intro t ht
    have ht' : t ≠ 0 := (zero_lt_one.trans_le ht).ne'
    exact (differentiableAt_id.ofReal_cpow_const ht' h₁).norm ℝ <|
      (cpow_ne_zero_iff_of_exponent_ne_zero h₁).mpr <| ofReal_ne_zero.mpr ht'
  have h₄ : (deriv fun t : ℝ ↦ ‖(t : ℂ) ^ (- s)‖) =ᶠ[atTop] fun t ↦ - s.re * t ^ (- (s.re +1)) := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [deriv_norm_ofReal_cpow _ ht, neg_re, neg_add']
  change Summable (fun n ↦ LSeries.term f s n)
  simp_rw [LSeries.term_def₀ hf, mul_comm (f _)]
  refine summable_mul_of_bigO_atTop' (f := fun t ↦ (t : ℂ) ^ (-s))
    (g := fun t ↦ t ^ (- (s.re + 1) + r)) _ h₃ ?_ ?_ ?_ ?_
  · refine integrableOn_Ici_iff_integrableOn_Ioi.mpr
      (integrableOn_Ioi_deriv_norm_ofReal_cpow zero_lt_one ?_)
    exact neg_re _ ▸ neg_nonpos.mpr  <| hr.trans hs.le
  · refine (IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow ((- s).re) r 0 ?_ hO h₂).congr_right
      (by simp)
    exact (norm_ofReal_cpow_eventually_eq_atTop _).isBigO.natCast_atTop
  · refine IsBigO.mul_atTop_rpow_of_isBigO_rpow (- (s.re + 1)) r _ ?_ ?_ le_rfl
    · exact (EventuallyEq.isBigO h₄).of_const_mul_right
    · exact (hO.comp_tendsto tendsto_nat_floor_atTop).trans <|
        isEquivalent_nat_floor.isBigO.rpow hr (eventually_ge_atTop 0)
  · exact integrableAtFilter_rpow_atTop_iff.mpr
      (by rwa [neg_add_lt_iff_lt_add, add_neg_cancel_right])

/-- If the partial sums `∑ k ∈ Icc 1 n, ‖f k‖` are `O(n ^ r)` for some real `0 ≤ r`, then the
L-series `LSeries f` converges at `s : ℂ` for all `s` such that `r < s.re`. -/
theorem LSeriesSummable_of_sum_norm_bigO
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] fun n ↦ (n : ℝ) ^ r)
    (hr : 0 ≤ r) (hs : r < s.re) :
    LSeriesSummable f s := by
  have h₁ : (fun n ↦ if n = 0 then 0 else f n) =ᶠ[atTop] f := by
    filter_upwards [eventually_ne_atTop 0] with n hn using by simp_rw [if_neg hn]
  refine LSeriesSummable.congr' _ h₁ ?_
  refine LSeriesSummable_of_sum_norm_bigO_aux (by rw [if_pos rfl]) ?_ hr hs
  refine hO.congr' (Eventually.of_forall fun _ ↦ Finset.sum_congr rfl fun _ h ↦ ?_) EventuallyEq.rfl
  rw [if_neg (zero_lt_one.trans_le (mem_Icc.mp h).1).ne']

/-- If `f` takes nonnegative real values and the partial sums `∑ k ∈ Icc 1 n, f k` are `O(n ^ r)`
for some real `0 ≤ r`, then the L-series `LSeries f` converges at `s : ℂ` for all `s`
such that `r < s.re`. -/
theorem LSeriesSummable_of_sum_norm_bigO_and_nonneg
    {f : ℕ → ℝ} (hO : (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r)
    (hf : ∀ n, 0 ≤ f n) (hr : 0 ≤ r) (hs : r < s.re) :
    LSeriesSummable (fun n ↦ f n) s := by
  refine LSeriesSummable_of_sum_norm_bigO ?_ hr hs
  simp_rw [norm_real, Real.norm_of_nonneg (hf _)]
  exact hO

end summable

section integralrepresentation

private theorem LSeries_eq_mul_integral_aux {f : ℕ → ℂ} (hf : f 0 = 0) {r : ℝ} (hr : 0 ≤ r) {s : ℂ}
    (hs : r < s.re) (hS : LSeriesSummable f s)
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    LSeries f s = s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (- (s + 1)) := by
  have h₁ : (-s - 1).re + r < -1 := by
    rwa [sub_re, one_re, neg_re, neg_sub_left, neg_add_lt_iff_lt_add, add_neg_cancel_comm]
  have h₂ : s ≠ 0 := ne_zero_of_re_pos (hr.trans_lt hs)
  have h₃ : ∀ t ∈ Set.Ici (1 : ℝ), DifferentiableAt ℝ (fun x : ℝ ↦ (x : ℂ) ^ (-s)) t :=
    fun t ht ↦ differentiableAt_id.ofReal_cpow_const (zero_lt_one.trans_le ht).ne'
      (neg_ne_zero.mpr h₂)
  have h₄ : ∀ n, ∑ k ∈ Icc 0 n, f k = ∑ k ∈ Icc 1 n, f k := fun n ↦ by
    rw [← Nat.Icc_insert_succ_left n.zero_le, sum_insert (by aesop), hf, zero_add, zero_add]
  simp_rw [← h₄] at hO
  rw [← integral_mul_left]
  refine tendsto_nhds_unique ((tendsto_add_atTop_iff_nat 1).mpr hS.hasSum.tendsto_sum_nat) ?_
  simp_rw [Nat.range_succ_eq_Icc_zero, LSeries.term_def₀ hf, mul_comm (f _)]
  convert tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (f := fun x ↦ (x : ℂ) ^ (-s)) (l := 0)
    ?_ hf h₃ ?_ ?_ ?_ (integrableAtFilter_rpow_atTop_iff.mpr h₁)
  · rw [zero_sub, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    rw [deriv_ofReal_cpow_const (zero_lt_one.trans ht).ne', h₄]
    · ring_nf
    · exact neg_ne_zero.mpr <| ne_zero_of_re_pos (hr.trans_lt hs)
  · refine integrableOn_Ici_iff_integrableOn_Ioi.mpr <|
      integrableOn_Ioi_deriv_ofReal_cpow zero_lt_one ?_
    rw [neg_re, neg_lt_zero]
    exact hr.trans_lt hs
  · have hlim : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (- (s.re - r))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by rwa [sub_pos])).comp tendsto_natCast_atTop_atTop
    refine IsBigO.trans_tendsto ?_ hlim
    refine IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow (- s.re) _ _ ?_ hO ?_
    · exact isBigO_norm_left.mp <| (norm_ofReal_cpow_eventually_eq_atTop _).isBigO.natCast_atTop
    · rw [neg_sub', sub_neg_eq_add]
  · refine IsBigO.mul_atTop_rpow_of_isBigO_rpow (- (s + 1).re) r _ ?_ ?_
      (by rw [← neg_re, neg_add'])
    · rw [add_re, one_re, neg_add']
      exact isBigO_deriv_ofReal_cpow_const_atTop _
    · exact (hO.comp_tendsto tendsto_nat_floor_atTop).trans <|
        isEquivalent_nat_floor.isBigO.rpow hr (eventually_ge_atTop 0)

/-- If the partial sums `∑ k ∈ Icc 1 n, f k` are `O(n ^ r)` for some real `0 ≤ r` and the
L-series `LSeries f` converges at `s : ℂ` with `r < s.re`, then
`LSeries f s = s * ∫ t in Set.Ioi 1, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (- (s + 1))`. -/
theorem LSeries_eq_mul_integral (f : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r) {s : ℂ} (hs : r < s.re)
    (hS : LSeriesSummable f s)
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    LSeries f s = s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (- (s + 1)) := by
  have h₁ : (fun n ↦ if n = 0 then 0 else f n) =ᶠ[atTop] f := by
    filter_upwards [eventually_ne_atTop 0] with n hn using by simp_rw [if_neg hn]
  have h₂ := (LSeriesSummable_congr' s h₁).mpr hS
  have h₃ : ∀ {n}, n ≠ 0 → (fun n ↦ if n = 0 then 0 else f n) n = f n :=
    fun hn ↦ by simp_rw [if_neg hn]
  have h₄ : ∀ n, ∑ k ∈ Icc 1 n, (if k = 0 then 0 else f k) = ∑ k ∈ Icc 1 n, f k := fun n ↦
    Finset.sum_congr rfl fun k hk ↦ by rw [if_neg (zero_lt_one.trans_le (mem_Icc.mp hk).1).ne']
  rw [← LSeries_congr _ h₃, LSeries_eq_mul_integral_aux (by rw [if_pos rfl]) hr hs h₂ ?_]
  · simp_rw [h₄]
  · simpa [h₄] using hO

/-- A version of `LSeries_eq_mul_integral` where we use the stronger condition that the partial sums
`∑ k ∈ Icc 1 n, ‖f k‖` are `O(n ^ r)` to deduce the integral representation. -/
theorem LSeries_eq_mul_integral' (f : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r) {s : ℂ} (hs : r < s.re)
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    LSeries f s = s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (- (s + 1)) := by
  refine LSeries_eq_mul_integral _ hr hs (LSeriesSummable_of_sum_norm_bigO hO hr hs) ?_
  exact IsBigO.trans (isBigO_of_le _ fun _ ↦ (norm_sum_le _ _).trans <| Real.le_norm_self _) hO

/-- If `f` takes nonnegative real values and the partial sums `∑ k ∈ Icc 1 n, f k` are `O(n ^ r)`
for some real `0 ≤ r`, then for `s : ℂ` with `r < s.re`, we have
`LSeries f s = s * ∫ t in Set.Ioi 1, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (- (s + 1))`. -/
theorem LSeries_eq_mul_integral_of_nonneg (f : ℕ → ℝ) {r : ℝ} (hr : 0 ≤ r) {s : ℂ} (hs : r < s.re)
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) (hf : ∀ n, 0 ≤ f n) :
    LSeries (fun n ↦ f n) s =
      s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, (f k : ℂ)) * t ^ (- (s + 1)) :=
  LSeries_eq_mul_integral' _ hr hs <| hO.congr_left fun _ ↦ by
    simp_rw [norm_real, Real.norm_of_nonneg (hf _)]

end integralrepresentation
