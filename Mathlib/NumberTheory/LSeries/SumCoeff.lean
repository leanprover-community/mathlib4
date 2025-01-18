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
  `∑ k ∈ Icc 1 n, ‖f k‖` are `O(n ^ r)` for some real `0 ≤ r`, then L-series `Lseries f`
  converges at `s : ℂ` for all `s` such that `r < s.re`.

  * `LSeries_eq_mul_integral` : for `f : ℕ → ℂ`, if the partial sums `∑ k ∈ Icc 1 n, f k` are
  `O(n ^ r)` for some real `0 ≤ r` and the L-series `LSeries f` converges at `s : ℂ` with
  `r < s.re`, then `LSeries f s = s * ∫ t in Set.Ioi 1, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (- (s + 1))`.

-/

open Finset Filter MeasureTheory Topology Complex Asymptotics


section lemmas
-- In this section we prove auxiliary results that will be useful later

-- First, results relating the function `f` and the function `f₀` obtained by setting the value
-- of `f` at `0` to be `0`.

private theorem f₀_of_ne_zero {𝕜 : Type*} [RCLike 𝕜] (f : ℕ → 𝕜) {n : ℕ} (hn : n ≠ 0) :
    (fun n ↦ if n = 0 then 0 else f n) n = f n := by
  simp_rw [if_neg hn]

private theorem f₀_atTop {𝕜 : Type*} [RCLike 𝕜] (f : ℕ → 𝕜) :
    (fun n ↦ if n = 0 then 0 else f n) =ᶠ[atTop] f := by
  filter_upwards [eventually_ne_atTop 0] with n hn using f₀_of_ne_zero f hn

private theorem sum_f₀_eq {𝕜 : Type*} [RCLike 𝕜] (f : ℕ → 𝕜) (n : ℕ) :
    ∑ k ∈ Icc 1 n, (if k = 0 then 0 else f k) = ∑ k ∈ Icc 1 n, f k := by
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [if_neg (zero_lt_one.trans_le (mem_Icc.mp hk).1).ne']

private theorem sum_norm_f₀_eq {𝕜 : Type*} [RCLike 𝕜] (f : ℕ → 𝕜) (n : ℕ) :
    ∑ k ∈ Icc 1 n, ‖if k = 0 then 0 else f k‖ = ∑ k ∈ Icc 1 n, ‖f k‖ := by
  simp_rw [apply_ite, norm_zero]
  exact sum_f₀_eq _ _

private theorem sum₀_f₀_eq {𝕜 : Type*} [RCLike 𝕜] {f : ℕ → 𝕜} (hf : f 0 = 0) (n : ℕ) :
    ∑ k ∈ Icc 0 n, f k = ∑ k ∈ Icc 1 n, f k := by
  rw [← Nat.Icc_insert_succ_left n.zero_le, sum_insert (mem_Icc.not.mpr (by omega)),
    hf, zero_add, zero_add]

private theorem term_def₀ {f : ℕ → ℂ} (hf : f 0 = 0) (s : ℂ) (n : ℕ) :
    LSeries.term f s n = (n : ℂ) ^ (- s) * f n := by
  cases n with
  | zero => rw [LSeries.term_zero, hf, mul_zero]
  | succ n =>
      rw [LSeries.term_of_ne_zero (Nat.add_one_ne_zero _), div_eq_mul_inv, cpow_neg, mul_comm]

-- Results about `cpow` and its derivative

private theorem eqOn_norm_cpow {c : ℂ} :
    Set.EqOn (fun t : ℝ ↦ ‖(t : ℂ) ^ (- c)‖) (fun t ↦ t ^ (- c.re)) (Set.Ioi 0):= by
  intro t ht
  simp_rw [Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_pos ht, neg_re]

private theorem eqOn_deriv_cpow {c : ℂ} (hc : c ≠ 0) :
    Set.EqOn (fun t : ℝ ↦ - c * (t : ℂ) ^ (- (c + 1)))
      (deriv fun t : ℝ ↦ (t : ℂ) ^ (- c)) (Set.Ioi 1) := by
  intro t ht
  rw [(deriv_ofReal_cpow_const (zero_lt_one.trans ht).ne' (neg_ne_zero.mpr hc)), neg_add']

private theorem eqOn_deriv_norm_cpow {c : ℂ} :
    Set.EqOn (fun t : ℝ ↦ - c.re * t ^ (- (c.re + 1)))
    (deriv fun t : ℝ ↦ ‖(t : ℂ) ^ (- c)‖) (Set.Ioi 1) := by
  intro t ht
  rw [EventuallyEq.deriv_eq (f := fun x ↦ x ^ (- c.re))]
  · rw [Real.deriv_rpow_const (Or.inl (zero_lt_one.trans ht).ne'), neg_add']
  · filter_upwards [eventually_gt_nhds (zero_lt_one.trans ht)] with x hx using eqOn_norm_cpow hx

-- Results about `bigO` asymptotics `atTop`

private theorem norm_cpow_atTop {c : ℂ} :
    (fun t : ℝ ↦ ‖(t : ℂ) ^ (- c)‖) =O[atTop] fun t ↦ t ^ (- c.re) := by
  refine EventuallyEq.isBigO ?_
  filter_upwards [eventually_gt_atTop 0] with t ht using eqOn_norm_cpow ht

private theorem cpow_atTop (c : ℂ) :
    (fun t : ℝ ↦ (t : ℂ) ^ (- c)) =O[atTop] fun t ↦ t ^ (- c.re) :=
  isBigO_norm_left.mp norm_cpow_atTop

private theorem deriv_cpow_atTop {c : ℂ} (hc : c ≠ 0) :
    (deriv fun t : ℝ ↦ (t : ℂ) ^ (- c)) =O[atTop] fun t ↦ t ^ (- (c + 1).re) := by
  refine ((cpow_atTop (c + 1)).const_mul_left (- c)).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 1] with t ht using by rw [← eqOn_deriv_cpow hc ht]

private theorem mul_atTop_of_le {𝕜 : Type*} [RCLike 𝕜] {f g : ℝ → 𝕜} (a b c : ℝ)
    (hf : f =O[atTop] fun t ↦ (t : ℝ) ^ a)
    (hg : g =O[atTop] fun t ↦ (t : ℝ) ^ b) (h : a + b ≤ c) :
    (f * g) =O[atTop] fun t ↦ (t : ℝ) ^ c := by
  refine (hf.mul hg).trans (Eventually.isBigO ?_)
  filter_upwards [eventually_ge_atTop 1] with t ht
  rw [← Real.rpow_add (zero_lt_one.trans_le ht), Real.norm_of_nonneg (Real.rpow_nonneg
    (zero_le_one.trans ht) (a + b))]
  exact Real.rpow_le_rpow_of_exponent_le ht h

private theorem mul_atTop_of_le' {𝕜 : Type*} [RCLike 𝕜] {f g : ℕ → 𝕜} (a b c : ℝ)
    (hf : f =O[atTop] fun n ↦ (n : ℝ) ^ a)
    (hg : g =O[atTop] fun n ↦ (n : ℝ) ^ b) (h : a + b ≤ c) :
    (f * g) =O[atTop] fun n ↦ (n : ℝ) ^ c := by
  refine (hf.mul hg).trans (Eventually.isBigO ?_)
  filter_upwards [eventually_ge_atTop 1] with t ht
  replace ht : 1 ≤ (t : ℝ) := Nat.one_le_cast.mpr ht
  rw [← Real.rpow_add (zero_lt_one.trans_le ht), Real.norm_of_nonneg (Real.rpow_nonneg
    (zero_le_one.trans ht) (a + b))]
  exact Real.rpow_le_rpow_of_exponent_le ht h

private theorem floor_atTop {𝕜 : Type*} [RCLike 𝕜] {f : ℕ → 𝕜} {r : ℝ} (hr : 0 ≤ r)
    (hf : f =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    (fun t : ℝ ↦ f ⌊t⌋₊) =O[atTop] fun t ↦ t ^ r :=
  (hf.comp_tendsto tendsto_nat_floor_atTop).trans <|
    isEquivalent_nat_floor.isBigO.rpow hr (eventually_ge_atTop 0)

-- Results about integrability of `cpow` and its derivative on `Ioi 1`

private theorem intOn_mul_cpow₀ {a s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun t : ℝ ↦ a * t ^ (- s)) (Set.Ioi 1) :=
  ((integrableOn_Ioi_rpow_iff zero_lt_one).mpr (by rwa [neg_lt_neg_iff])).const_mul _

theorem intO_cpow {a : ℝ} {c : ℂ} (ha : 0 < a) (hc : 1 < c.re):
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (- c)) (Set.Ioi a) :=
  integrableOn_Ioi_cpow_of_lt (by rwa [neg_re, neg_lt_neg_iff]) ha

private theorem intOn_mul_cpow {a c : ℂ} (hc : 1 < c.re) :
    IntegrableOn (fun t : ℝ ↦ a * t ^ (- c)) (Set.Ioi 1) :=
  (intO_cpow zero_lt_one hc).const_mul _

private theorem intOn_deriv_norm_cpow {c : ℂ} (hc : 0 < c.re) :
    IntegrableOn (deriv fun t : ℝ ↦ ‖(t : ℂ) ^ (- c)‖) (Set.Ioi 1) :=
  (intOn_mul_cpow₀ (by rwa [lt_add_iff_pos_left])).congr_fun eqOn_deriv_norm_cpow measurableSet_Ioi

private theorem intOn_deriv_cpow {c : ℂ} (hc : 0 < c.re) :
    IntegrableOn (deriv fun x : ℝ ↦ (x : ℂ) ^ (- c)) (Set.Ioi 1) := by
  refine IntegrableOn.congr_fun ?_ (eqOn_deriv_cpow (ne_zero_of_re_pos hc)) measurableSet_Ioi
  exact intOn_mul_cpow (by rwa [add_re, one_re, lt_add_iff_pos_left])

end lemmas

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
      (cpow_ne_zero_iff h₁).mpr <| ofReal_ne_zero.mpr ht'
  have h₄ : (deriv fun t : ℝ ↦ ‖(t : ℂ) ^ (- s)‖) =ᶠ[atTop] fun t ↦ - s.re * t ^ (- (s.re +1)) := by
    filter_upwards [eventually_gt_atTop 1] with t ht using (eqOn_deriv_norm_cpow ht).symm
  change Summable (fun n ↦ LSeries.term f s n)
  simp_rw [term_def₀ hf]
  refine summable_mul_of_bigO_atTop' (f := fun t ↦ (t : ℂ) ^ (-s))
    (g := fun t ↦ t ^ (- (s.re + 1) + r)) _ h₃ ?_ ?_ ?_ ?_
  · exact integrableOn_Ici_iff_integrableOn_Ioi.mpr (intOn_deriv_norm_cpow (hr.trans_lt hs))
  · refine (mul_atTop_of_le' ((- s).re) r 0 ?_ hO h₂).congr_right (by simp)
    exact norm_cpow_atTop.natCast_atTop
  · refine mul_atTop_of_le (- (s.re + 1)) r _ ?_ ?_ le_rfl
    · exact (EventuallyEq.isBigO h₄).of_const_mul_right
    · exact floor_atTop hr hO
  · exact integrableAtFilter_rpow_atTop (by rwa [neg_add_lt_iff_lt_add, add_neg_cancel_right])

theorem LSeriesSummable_of_sum_norm_bigO
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] fun n ↦ (n : ℝ) ^ r)
    (hr : 0 ≤ r) (hs : r < s.re) :
    LSeriesSummable f s := by
  refine LSeriesSummable.congr' _ (f₀_atTop f) ?_
  refine LSeriesSummable_of_sum_norm_bigO_aux (by rw [if_pos rfl]) ?_ hr hs
  simpa only [sum_norm_f₀_eq] using hO

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
  simp_rw [← sum₀_f₀_eq hf] at hO
  rw [← integral_mul_left]
  refine tendsto_nhds_unique ((tendsto_add_atTop_iff_nat 1).mpr hS.hasSum.tendsto_sum_nat) ?_
  simp_rw [Nat.range_succ_eq_Icc_zero, term_def₀ hf]
  convert tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (f := fun x ↦ (x : ℂ) ^ (-s)) (l := 0)
    ?_ hf h₃ ?_ ?_ ?_ (integrableAtFilter_rpow_atTop h₁)
  · rw [zero_sub, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    rw [← eqOn_deriv_cpow h₂ ht, sum₀_f₀_eq hf]
    ring_nf
  · exact integrableOn_Ici_iff_integrableOn_Ioi.mpr <| intOn_deriv_cpow (hr.trans_lt hs)
  · have hlim : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (- (s.re - r))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by rwa [sub_pos])).comp tendsto_natCast_atTop_atTop
    refine IsBigO.trans_tendsto ?_ hlim
    refine mul_atTop_of_le' (- s.re) _ _ ?_ hO ?_
    · exact (cpow_atTop _).natCast_atTop
    · rw [neg_sub', sub_neg_eq_add]
  · refine mul_atTop_of_le (- (s + 1).re) r _ ?_ ?_ (by rw [← neg_re, neg_add'])
    · exact deriv_cpow_atTop h₂
    · exact floor_atTop hr hO

theorem LSeries_eq_mul_integral (f : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r) {s : ℂ} (hs : r < s.re)
    (hS : LSeriesSummable f s)
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    LSeries f s = s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (- (s + 1)) := by
  have h₁ := (LSeriesSummable_congr' s (f₀_atTop f)).mpr hS
  rw [← LSeries_congr _ (f₀_of_ne_zero f), LSeries_eq_mul_integral_aux (by rw [if_pos rfl])
    hr hs h₁ ?_]
  · simp_rw [sum_f₀_eq]
  · simpa only [sum_f₀_eq] using hO

theorem LSeries_eq_mul_integral' (f : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r) {s : ℂ} (hs : r < s.re)
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    LSeries f s = s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (- (s + 1)) := by
  refine LSeries_eq_mul_integral _ hr hs (LSeriesSummable_of_sum_norm_bigO hO hr hs) ?_
  exact IsBigO.trans (isBigO_of_le _ fun _ ↦ (norm_sum_le _ _).trans <| Real.le_norm_self _) hO

theorem LSeries_eq_mul_integral_of_nonneg (f : ℕ → ℝ) {r : ℝ} (hr : 0 ≤ r) {s : ℂ} (hs : r < s.re)
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) (hf : ∀ n, 0 ≤ f n) :
    LSeries (fun n ↦ f n) s =
      s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, (f k : ℂ)) * t ^ (- (s + 1)) :=
  LSeries_eq_mul_integral' _ hr hs <| hO.congr_left fun _ ↦ by
    simp_rw [norm_real, Real.norm_of_nonneg (hf _)]

end integralrepresentation
