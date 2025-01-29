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

=======
# Partial sums of coefficients of L-series

We prove several results involving partial sums of coefficients (or norm of coefficients) of
L-series.

## Main results

* `LSeriesSummable_of_sum_norm_bigO`: for `f : ℕ → ℂ`, if the partial sums
  `∑ k ∈ Icc 1 n, ‖f k‖` are `O(n ^ r)` for some real `0 ≤ r`, then the L-series `LSeries f`
  converges at `s : ℂ` for all `s` such that `r < s.re`.

* `LSeries_eq_mul_integral` : for `f : ℕ → ℂ`, if the partial sums `∑ k ∈ Icc 1 n, f k` are
  `O(n ^ r)` for some real `0 ≤ r` and the L-series `LSeries f` converges at `s : ℂ` with
  `r < s.re`, then `LSeries f s = s * ∫ t in Set.Ioi 1, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (-(s + 1))`.

* `LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div` : assume that `f : ℕ → ℂ` satifies that
  `(∑ k ∈ Icc 1 n, f k) / n` tends to some complex number `l` when `n → ∞` and that the L-series
  `LSeries f` converges for all `s : ℝ` such that `1 < s`. Then `(s - 1) * LSeries f s` tends
  to `l` when `s → 1` with `1 < s`.

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
  have h₃ (t : ℝ) (ht : t ∈ Set.Ici 1) : DifferentiableAt ℝ (fun x : ℝ ↦ ‖(x : ℂ) ^ (-s)‖) t :=
    have ht' : t ≠ 0 := (zero_lt_one.trans_le ht).ne'
    (differentiableAt_id.ofReal_cpow_const ht' h₁).norm ℝ <|
      (cpow_ne_zero_iff_of_exponent_ne_zero h₁).mpr <| ofReal_ne_zero.mpr ht'
  have h₄ : (deriv fun t : ℝ ↦ ‖(t : ℂ) ^ (-s)‖) =ᶠ[atTop] fun t ↦ -s.re * t ^ (-(s.re +1)) := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [deriv_norm_ofReal_cpow _ ht, neg_re, neg_add']
  simp_rw [LSeriesSummable, funext (LSeries.term_def₀ hf s), mul_comm (f _)]
  refine summable_mul_of_bigO_atTop' (f := fun t ↦ (t : ℂ) ^ (-s))
    (g := fun t ↦ t ^ (-(s.re + 1) + r)) _ h₃ ?_ ?_ ?_ ?_
  · refine (integrableOn_Ici_iff_integrableOn_Ioi.mpr
      (integrableOn_Ioi_deriv_norm_ofReal_cpow zero_lt_one ?_)).locallyIntegrableOn
    exact neg_re _ ▸ neg_nonpos.mpr  <| hr.trans hs.le
  · refine (IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow _ _ _ ?_ hO h₂).congr_right  (by simp)
    exact (norm_ofReal_cpow_eventually_eq_atTop _).isBigO.natCast_atTop
  · refine h₄.isBigO.of_const_mul_right.mul_atTop_rpow_of_isBigO_rpow _ r _ ?_ le_rfl
    exact (hO.comp_tendsto tendsto_nat_floor_atTop).trans <|
      isEquivalent_nat_floor.isBigO.rpow hr (eventually_ge_atTop 0)
  · rwa [integrableAtFilter_rpow_atTop_iff, neg_add_lt_iff_lt_add, add_neg_cancel_right]

/-- If the partial sums `∑ k ∈ Icc 1 n, ‖f k‖` are `O(n ^ r)` for some real `0 ≤ r`, then the
L-series `LSeries f` converges at `s : ℂ` for all `s` such that `r < s.re`. -/
theorem LSeriesSummable_of_sum_norm_bigO
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] fun n ↦ (n : ℝ) ^ r)
    (hr : 0 ≤ r) (hs : r < s.re) :
    LSeriesSummable f s := by
  have h₁ : (fun n ↦ if n = 0 then 0 else f n) =ᶠ[atTop] f := by
    filter_upwards [eventually_ne_atTop 0] with n hn using by simp_rw [if_neg hn]
  refine (LSeriesSummable_of_sum_norm_bigO_aux (if_pos rfl) ?_ hr hs).congr' _ h₁
  refine hO.congr' (Eventually.of_forall fun _ ↦ Finset.sum_congr rfl fun _ h ↦ ?_) EventuallyEq.rfl
  rw [if_neg (zero_lt_one.trans_le (mem_Icc.mp h).1).ne']

/-- If `f` takes nonnegative real values and the partial sums `∑ k ∈ Icc 1 n, f k` are `O(n ^ r)`
for some real `0 ≤ r`, then the L-series `LSeries f` converges at `s : ℂ` for all `s`
such that `r < s.re`. -/
theorem LSeriesSummable_of_sum_norm_bigO_and_nonneg
    {f : ℕ → ℝ} (hO : (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r)
    (hf : ∀ n, 0 ≤ f n) (hr : 0 ≤ r) (hs : r < s.re) :
    LSeriesSummable (fun n ↦ f n) s :=
  LSeriesSummable_of_sum_norm_bigO (by simpa [_root_.abs_of_nonneg (hf _)]) hr hs

end summable

section integralrepresentation

private theorem LSeries_eq_mul_integral_aux {f : ℕ → ℂ} (hf : f 0 = 0) {r : ℝ} (hr : 0 ≤ r) {s : ℂ}
    (hs : r < s.re) (hS : LSeriesSummable f s)
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    LSeries f s = s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (- (s + 1)) := by
  have h₁ : (-s - 1).re + r < -1 := by
    rwa [sub_re, one_re, neg_re, neg_sub_left, neg_add_lt_iff_lt_add, add_neg_cancel_comm]
  have h₂ : s ≠ 0 := ne_zero_of_re_pos (hr.trans_lt hs)
  have h₃ (t : ℝ) (ht : t ∈ Set.Ici 1) : DifferentiableAt ℝ (fun x : ℝ ↦ (x : ℂ) ^ (-s)) t :=
    differentiableAt_id.ofReal_cpow_const (zero_lt_one.trans_le ht).ne' (neg_ne_zero.mpr h₂)
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
  · refine (integrableOn_Ici_iff_integrableOn_Ioi.mpr <|
      integrableOn_Ioi_deriv_ofReal_cpow zero_lt_one
        (by simpa using hr.trans_lt hs)).locallyIntegrableOn
  · have hlim : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-(s.re - r))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by rwa [sub_pos])).comp tendsto_natCast_atTop_atTop
    refine (IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow (-s.re) _ _ ?_ hO ?_).trans_tendsto hlim
    · exact isBigO_norm_left.mp <| (norm_ofReal_cpow_eventually_eq_atTop _).isBigO.natCast_atTop
    · linarith
  · refine .mul_atTop_rpow_of_isBigO_rpow (-(s + 1).re) r _ ?_ ?_ (by rw [← neg_re, neg_add'])
    · simpa [- neg_add_rev, neg_add'] using isBigO_deriv_ofReal_cpow_const_atTop _
    · exact (hO.comp_tendsto tendsto_nat_floor_atTop).trans <|
        isEquivalent_nat_floor.isBigO.rpow hr (eventually_ge_atTop 0)

/-- If the partial sums `∑ k ∈ Icc 1 n, f k` are `O(n ^ r)` for some real `0 ≤ r` and the
L-series `LSeries f` converges at `s : ℂ` with `r < s.re`, then
`LSeries f s = s * ∫ t in Set.Ioi 1, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (-(s + 1))`. -/
theorem LSeries_eq_mul_integral (f : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r) {s : ℂ} (hs : r < s.re)
    (hS : LSeriesSummable f s)
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    LSeries f s = s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (-(s + 1)) := by
  rw [← LSeriesSummable_congr' s (f := fun n ↦ if n = 0 then 0 else f n)
    (by filter_upwards [eventually_ne_atTop 0] with n h using if_neg h)] at hS
  have (n) : ∑ k ∈ Icc 1 n, (if k = 0 then 0 else f k) = ∑ k ∈ Icc 1 n, f k :=
    Finset.sum_congr rfl fun k hk ↦ by rw [if_neg (zero_lt_one.trans_le (mem_Icc.mp hk).1).ne']
  rw [← LSeries_congr _ (fun _ ↦ if_neg _), LSeries_eq_mul_integral_aux (if_pos rfl) hr hs hS] <;>
  simp_all

/-- A version of `LSeries_eq_mul_integral` where we use the stronger condition that the partial sums
`∑ k ∈ Icc 1 n, ‖f k‖` are `O(n ^ r)` to deduce the integral representation. -/
theorem LSeries_eq_mul_integral' (f : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r) {s : ℂ} (hs : r < s.re)
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    LSeries f s = s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (-(s + 1)) :=
  LSeries_eq_mul_integral _ hr hs (LSeriesSummable_of_sum_norm_bigO hO hr hs) <|
    (isBigO_of_le _ fun _ ↦ (norm_sum_le _ _).trans <| Real.le_norm_self _).trans hO

/-- If `f` takes nonnegative real values and the partial sums `∑ k ∈ Icc 1 n, f k` are `O(n ^ r)`
for some real `0 ≤ r`, then for `s : ℂ` with `r < s.re`, we have
`LSeries f s = s * ∫ t in Set.Ioi 1, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (-(s + 1))`. -/
theorem LSeries_eq_mul_integral_of_nonneg (f : ℕ → ℝ) {r : ℝ} (hr : 0 ≤ r) {s : ℂ} (hs : r < s.re)
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) (hf : ∀ n, 0 ≤ f n) :
    LSeries (fun n ↦ f n) s =
      s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, (f k : ℂ)) * t ^ (-(s + 1)) :=
  LSeries_eq_mul_integral' _ hr hs <| hO.congr_left fun _ ↦ by simp [_root_.abs_of_nonneg (hf _)]

end integralrepresentation

noncomputable section residue

variable {f : ℕ → ℂ}

section lemmas

-- Miscellaneous results

-- inline
-- private theorem norm_mul_id_mul_norm_cpow_succ {ε t : ℝ} {c : ℂ} (hε : 0 ≤ ε) (ht : t ≠ 0) :
--     ‖ε * t‖ * ‖(t : ℂ) ^ (- (c + 1))‖ = ε * ‖(t : ℂ) ^ (- c)‖ := by
--   replace ht := ofReal_ne_zero.mpr ht
--   rw [← norm_real, ←  norm_mul, ofReal_mul, mul_assoc, norm_mul, norm_real, Real.norm_of_nonneg hε,
--     neg_add', cpow_sub _ _ ht, cpow_one, mul_div_cancel₀ _ ht]

-- Move
theorem Complex.abs_ofReal_cpow_le_abs_ofReal_cpow {t : ℝ} (ht : 1 ≤ t) {c d : ℂ} (h : c.re ≤ d.re) :
    abs ((t : ℂ) ^ c) ≤ abs ((t : ℂ) ^ d) := by
  simp_rw [abs_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le ht)]
  refine Real.rpow_le_rpow_of_exponent_le ht h

-- keep (generalize)
-- private theorem norm_cpow_le_norm_cpow {t : ℝ} {c d : ℂ} (ht : 1 ≤ t) (hc : d.re ≤ c.re) :
--    ‖(t : ℂ) ^ (-c)‖ ≤ ‖(t : ℂ) ^ (-d)‖ := by
--  sorry
--  simp_rw [eqOn_norm_cpow (zero_lt_one.trans_le ht)]
--  refine Real.rpow_le_rpow_of_exponent_le ht (neg_le_neg_iff.mpr hc)

-- keep
private theorem isBigO_of_tendsto_sum_div {𝕜 : Type*} [RCLike 𝕜] {f : ℕ → 𝕜} {l : 𝕜}
    (hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Icc 1 n, f k) / n) atTop (𝓝 l)) :
    (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
  simp_rw [Real.rpow_one]
  refine isBigO_norm_left.mp <| isBigO_of_div_tendsto_nhds ?_ ‖l‖ ?_
  · filter_upwards [eventually_ne_atTop 0] with _ h using by simp [h]
  · simpa only [Function.comp_def, norm_div, RCLike.norm_natCast] using (tendsto_norm.comp hlim)

-- Some more results about integrability

-- inline
private theorem intOn_norm_cpow {T : ℝ} (hT : 0 < T) {c : ℂ} (hc : 1 < c.re) :
    IntegrableOn (fun t : ℝ ↦ ‖(t : ℂ) ^ (-c)‖) (Set.Ioi T) := sorry
--  ((integrableOn_Ioi_rpow_iff hT).mpr (by rwa [neg_lt_neg_iff])).congr_fun
--    (eqOn_norm_cpow.symm.mono (Set.Ioi_subset_Ioi hT.le)) measurableSet_Ioi

-- inline
private theorem intOn_norm_mul_id_mul_norm_cpow_succ {ε : ℝ} {T : ℝ} {c : ℂ} (hε : 0 ≤ ε)
    (hT : 0 < T) (hc : 1 < c.re) :
    IntegrableOn (fun t : ℝ ↦ ‖ε * t‖ * ‖(t : ℂ) ^ (-(c + 1))‖) (Set.Ioi T) := by
  refine IntegrableOn.congr_fun (f := fun t : ℝ ↦ ε * ‖(t : ℂ) ^ (-c)‖) ?_ ?_ measurableSet_Ioi
  · exact (intOn_norm_cpow hT hc).const_mul _
  · sorry
    -- exact fun t ht ↦ (norm_mul_id_mul_norm_cpow_succ hε (hT.trans ht).ne').symm

private theorem locintOn_sum_mul_cpow {a : ℝ} {c : ℂ} (ha : 0 < a) (hc : 0 < c.re) :
    LocallyIntegrableOn (fun t ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * ↑t ^ (-(c + 1))) (Set.Ici a) := by
  sorry
--  simp_rw [mul_comm]
--  refine locallyIntegrableOn_mul_sum_Icc _ ha.le <|
--    integrableOn_Ici_iff_integrableOn_Ioi.mpr (intO_cpow ha ?_)
--  rwa [add_re, one_re, lt_add_iff_pos_left]

-- keep
private theorem intOn_sum_mul_cpow {f : ℕ → ℂ} {a : ℝ} {c : ℂ} (ha : 0 < a) (hc : 1 < c.re)
    (hf : (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun t ↦ (t : ℝ) ^ (1 : ℝ)) :
    IntegrableOn (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(c + 1))) (Set.Ici a) := by
  sorry
--  refine (locintOn_sum_mul_cpow ha (zero_lt_one.trans hc)).integrableOn_of_isBigO_atTop ?_ <|
--    integrableAtFilter_rpow_atTop (by rwa [neg_lt_neg_iff])
--  refine mul_atTop_of_le 1 (-(c + 1).re) _ (floor_atTop zero_le_one hf) ?_ ?_
--  · exact isBigO_norm_left.mp <| norm_cpow_atTop
--  · rw [add_re, one_re, neg_add_rev, add_neg_cancel_left]

-- not clear
private theorem intOn_Icc_cpow {a b : ℝ} {c : ℂ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (-c)) (Set.Icc a b) := by
  refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
  exact continuous_ofReal.continuousOn.cpow_const
    (fun x hx ↦ ofReal_mem_slitPlane.mpr (ha.trans_le hx.1))

-- inline
private theorem intOn_Icc_sum_mul_cpow {a b : ℝ} {c : ℂ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-c)) (Set.Icc a b) := by
  simp_rw [mul_comm]
  exact integrableOn_mul_sum_Icc _ ha.le (intOn_Icc_cpow ha)

-- Some results about integrals

-- inline
private theorem int_Ioi_eq {a b : ℝ} (h : a ≤ b) {g : ℝ → ℂ} (hg : IntegrableOn g (Set.Ioi a)) :
    ∫ (t : ℝ) in Set.Ioi a, g t =
      (∫ (t : ℝ) in Set.Ioc a b, g t) + ∫ (t : ℝ) in Set.Ioi b, g t := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi h, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi (hg.mono_set Set.Ioc_subset_Ioi_self) (hg.mono_set (Set.Ioi_subset_Ioi h))]

-- -- inline
-- private theorem sub_mul_int_rpow {s : ℝ} (hs : 1 < s) :
--     (s - 1) * ∫ (t : ℝ) in Set.Ioi 1, t ^ (-s) = 1 := by
--   rw [integral_Ioi_rpow_of_lt (by rwa [neg_lt_neg_iff]) zero_lt_one, Real.one_rpow, neg_div,
--     ← one_div_neg_eq_neg_one_div, neg_add', neg_neg, mul_one_div, div_self (sub_ne_zero.mpr hs.ne')]

-- inline
-- private theorem sub_mul_int_cpow {s : ℂ} (hs : 1 < s.re) :
--     (s - 1) * ∫ (t : ℝ) in Set.Ioi 1, (t : ℂ) ^ (-s : ℂ) = 1 := by
--   have : 1 - s ≠ 0 := by
--     contrapose! hs
--     rw [← sub_eq_zero.mp hs, one_re]
--   rw [integral_Ioi_cpow_of_lt (by rwa [neg_re, neg_lt_neg_iff]) zero_lt_one, ofReal_one, one_cpow,
--     ← mul_div_assoc, mul_neg_one, neg_add_eq_sub, neg_sub, div_self this]

-- keep
private theorem norm_mul_int_cpow_le {T : ℝ} {c l : ℂ} (hc : 1 ≤ c.re):
    ‖l * ∫ (t : ℝ) in Set.Ioc 1 T, (t : ℂ) ^ (-c)‖ ≤
      ‖l‖ * ∫ (t : ℝ) in Set.Ioc 1 T, ‖(t : ℂ) ^ (-1 : ℂ)‖ := by
  by_cases hT : 1 < T
  · rw [norm_mul]
    refine mul_le_mul_of_nonneg_left (le_trans (norm_integral_le_integral_norm _)
      (setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun t ht ↦ ?_)) (norm_nonneg _)
    · exact (integrableOn_Icc_iff_integrableOn_Ioc.mp <| intOn_Icc_cpow zero_lt_one).norm
    · exact (integrableOn_Icc_iff_integrableOn_Ioc.mp <| intOn_Icc_cpow zero_lt_one).norm
    · refine abs_ofReal_cpow_le_abs_ofReal_cpow ht.1.le ?_
      rwa [neg_re, neg_re, one_re, neg_le_neg_iff]
  · rw [Set.Ioc_eq_empty hT, setIntegral_empty, setIntegral_empty, mul_zero, norm_zero, mul_zero]

-- keep
private theorem norm_int_sum_mul_cpow_le {T : ℝ} {c : ℂ} (hc : 1 ≤ c.re) :
    ‖∫ (t : ℝ) in Set.Ioc 1 T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(c + 1))‖ ≤
      ∫ (t : ℝ) in Set.Ioc 1 T, ‖(∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-2 : ℂ)‖ := by
  by_cases hT : 1 < T
  · refine le_trans (norm_integral_le_integral_norm _) <|
      setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun t ht ↦ ?_
    · exact (integrableOn_Icc_iff_integrableOn_Ioc.mp <| intOn_Icc_sum_mul_cpow zero_lt_one).norm
    · exact (integrableOn_Icc_iff_integrableOn_Ioc.mp <| intOn_Icc_sum_mul_cpow zero_lt_one).norm
    · rw [norm_mul, norm_mul]
      refine mul_le_mul_of_nonneg_left (abs_ofReal_cpow_le_abs_ofReal_cpow ht.1.le ?_)
        (norm_nonneg _)
      rw [neg_re, neg_re, add_re, one_re, re_ofNat]
      linarith
  · rw [Set.Ioc_eq_empty hT, setIntegral_empty, setIntegral_empty, norm_zero]



end lemmas

section newlemmas

theorem toto {s : ℝ} (S : ℝ → ℂ) :
    IntegrableOn (fun t ↦ ‖S t‖ * (t ^ (-s - 1))) (Set.Ioi 1) := by

  sorry

end newlemmas

section proof

variable {l : ℂ} (hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Icc 1 n, f k) / n) atTop (𝓝 l))

include hlim in
private theorem aux₁ {ε : ℝ} (hε : ε > 0) :
    ∀ᶠ t : ℝ in atTop, ‖(∑ k ∈ Icc 1 ⌊t⌋₊, f k) - l * t‖ < ε * t := by
  have h_lim' : Tendsto (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, f k : ℂ) / t) atTop (𝓝 l) := by
    refine (mul_one l ▸ ofReal_one ▸ ((hlim.comp tendsto_nat_floor_atTop).mul <|
      tendsto_ofReal_iff.mpr <| tendsto_nat_floor_div_atTop)).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    rw [Function.comp_def, ofReal_div, ofReal_natCast, div_mul_div_cancel₀ (by
      rwa [Nat.cast_ne_zero, ne_eq, Nat.floor_eq_zero, not_lt])]
  rw [Metric.tendsto_nhds] at h_lim'
  filter_upwards [eventually_gt_atTop 0, h_lim' ε hε] with t ht₁ ht₂
  rwa [dist_eq_norm, div_sub' _ _ _ (ne_zero_of_re_pos ht₁), norm_div, norm_real,
    Real.norm_of_nonneg ht₁.le, mul_comm, div_lt_iff₀ ht₁] at ht₂

private theorem aux₂ {s T ε : ℝ} {S : ℝ → ℂ} (hS : Measurable S) (hε : 0 < ε) (hs : 1 < s)
    (hT₀ : 1 ≤ T) (hT : ∀ t > T, ‖S t - l * t‖ ≤ ε * t) :
    (s - 1) * ∫ (t : ℝ) in Set.Ioi T, ‖S t - l * t‖ * t ^ (-s - 1) ≤ ε := by
  have h {t : ℝ} : t ^ (-s) = t * t ^ (-s - 1) := sorry
  calc
    _ ≤ (s - 1) * ∫ (t : ℝ) in Set.Ioi T, ε * t ^ (-s) := ?_
    _ ≤ ε * ((s - 1) * ∫ (t : ℝ) in Set.Ioi 1, t ^ (-s)) := ?_
    _ = ε := ?_
  · refine mul_le_mul_of_nonneg_left (setIntegral_mono_on ?_ ?_ measurableSet_Ioi fun t ht ↦ ?_) ?_
    · refine (toto _).mono_set ?_
      sorry -- Integrable (fun t ↦ ‖S t - l * ↑t‖ * t ^ (-s - 1)) (volume.restrict (Set.Ioi T))
    · exact (integrableOn_Ioi_rpow_of_lt (neg_lt_neg_iff.mpr hs)
        (zero_lt_one.trans_le hT₀)).const_mul  _
    · rw [h, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ ?_
      · exact hT t ht
      · sorry
    · sorry
  · rw [integral_mul_left, ← mul_assoc, ← mul_assoc, mul_comm ε]
    gcongr
    · sorry
    · refine setIntegral_mono_set ?_ ?_ ?_
      · exact integrableOn_Ioi_rpow_of_lt (neg_lt_neg_iff.mpr hs) zero_lt_one
      · sorry
      · sorry
  · sorry

variable (hfS : ∀ s : ℝ, 1 < s → LSeriesSummable f s)

include hlim hfS in
private theorem aux₃ {ε : ℝ} (hε : ε > 0) :
    ∃ C ≥ 0, ∀ s : ℝ, 1 < s → ‖(s - 1) * LSeries f s - s * l‖ ≤ (s - 1) * s * C + s * ε := by
  obtain ⟨T, hT₁, hT⟩ :=
    (eventually_forall_ge_atTop.mpr (aux₁ hlim hε)).frequently.forall_exists_of_atTop 1
  set S : ℝ → ℂ := fun t ↦ ∑ k ∈ Icc 1 ⌊t⌋₊, f k
  let C := ∫ t in Set.Ioc 1 T, ‖S t - l * t‖ * t ^ (-1 - 1 : ℝ)
  refine ⟨C, sorry, fun s hs ↦ ?_⟩
  have h₂ : (s - 1) * ∫ (t : ℝ) in Set.Ioi 1, (t : ℂ) ^ (-s : ℂ) = 1 := sorry

  let Cs := ∫ t in Set.Ioc 1 T, ‖S t - l * t‖ * t ^ (-s - 1)
  have : Cs ≤ C := by
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun t ht ↦ ?_
    · refine (toto _).mono_set ?_
      sorry -- IntegrableOn (fun t ↦ ‖S t - l * ↑t‖ * t ^ (-s - 1)) (Set.Ioc 1 T) volume
    · refine (toto _).mono_set ?_
      sorry -- IntegrableOn (fun t ↦ ‖S t - l * ↑t‖ * t ^ (-1 - 1)) (Set.Ioc 1 T) volume
    · gcongr
      exact ht.1.le
  calc
    _ = ‖(s - 1) * s *
          ((∫ (t : ℝ) in Set.Ioi 1, S t * (t : ℂ) ^ (-s - 1 : ℂ))
            - ∫ (t : ℝ) in Set.Ioi 1, l * (t : ℂ) ^ ((-s : ℂ)))‖ := ?_
    _ = ‖(s - 1) * s *
          ∫ (t : ℝ) in Set.Ioi 1, (S t * (t : ℂ) ^ (-s - 1 : ℂ) - l * t ^ (-s : ℂ))‖ := ?_
    _ = ‖(s - 1) * s * ∫ (t : ℝ) in Set.Ioi 1, (S t - l * t) * (t : ℂ) ^ (-s - 1 : ℂ)‖ := ?_
    _ ≤ (s - 1) * s * ∫ (t : ℝ) in Set.Ioi 1, ‖S t - l * t‖ * t ^ (-s - 1) := ?_
    _ = (s - 1) * s * (Cs + ∫ (t : ℝ) in Set.Ioi T, ‖S t - l * t‖ * t ^ (-s - 1)) := ?_
    _ ≤ (s - 1) * s * C +
          s * ((s - 1) * ∫ (t : ℝ) in Set.Ioi T, ‖S t - l * t‖ * t ^ (-s - 1)) := ?_
    _ ≤ (s - 1) * s * C + s * ε := ?_
  · sorry
  · rw [integral_sub]
    · sorry -- Integrable (fun t ↦ S t * ↑t ^ (-↑s - 1))) (volume.restrict (Set.Ioi 1))
    · exact (integrableOn_Ioi_cpow_of_lt
        (by rwa [neg_re, ofReal_re, neg_lt_neg_iff]) zero_lt_one).const_mul  _
  · congr 2
    refine setIntegral_congr_fun ?_ ?_
    · sorry
    · sorry
  · rw [norm_mul]
    sorry
  · rw [← Set.Ioc_union_Ioi_eq_Ioi hT₁, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi]
    · refine (toto _).mono_set ?_
      sorry -- IntegrableOn (fun t ↦ ‖S t - l * ↑t‖ * t ^ (-s - 1))) (Set.Ioc 1 T) volume
    · refine (toto _).mono_set ?_
      sorry -- IntegrableOn (fun t ↦ ‖S t - l * ↑t‖ * t ^ (-s - 1))) (Set.Ioi T) volume
  · rw [mul_add, ← mul_assoc, mul_comm s]
    refine add_le_add_right (mul_le_mul_of_nonneg_left this ?_) _
    sorry -- 0 ≤ (s - 1) * s
  · gcongr
    refine aux₂ ?_ hε hs hT₁ ?_
    · sorry
    · intro t ht
      exact (hT t ht.le).le



-- private theorem aux₂ {s T ε : ℝ} {g : ℝ → ℂ} (hg : Measurable g) (hε : 0 < ε) (hs : 1 < s)
--     (hT₀ : 1 ≤ T) (hT : ∀ t > T, ‖g t - l * t‖ ≤ ε * t) :
--     (s - 1) * ∫ (t : ℝ) in Set.Ioi T, ‖g t * ↑t ^ (-((s : ℂ) + 1)) - l * t ^ (-(s : ℂ))‖ ≤ ε := by
--   have h₁ {t : ℝ} {s : ℂ} : t ≠ 0 → t * (t : ℂ) ^ (-(s + 1)) = t ^ (-s) := fun ht ↦ by
--     replace ht := ofReal_ne_zero.mpr ht
--     rw [neg_add', cpow_sub _ _ ht, cpow_one, mul_div_cancel₀ _ ht]
--   have h₂ {a : ℝ} (ha : 0 < a) :
--       IntegrableOn (fun t : ℝ ↦ ‖ε * t‖ * ‖(t : ℂ) ^ (-((s : ℂ) + 1))‖) (Set.Ioi a) := by
--     refine IntegrableOn.congr_fun (f := fun t : ℝ ↦ ‖ε‖ * ‖(t : ℂ) ^ (-s : ℂ)‖) ?_ (fun t ht ↦ ?_)
--       measurableSet_Ioi
--     · exact (integrableOn_Ioi_norm_cpow_of_lt
--         (by rwa [neg_re, ofReal_re, neg_lt_neg_iff]) ha).const_mul _
--     · rw [norm_mul, ← norm_real t, mul_assoc, ← norm_mul, h₁ (ha.trans ht).ne']
--   have h₃ : IntegrableOn (fun t ↦ ‖g t - l * t‖ * ‖(t : ℂ) ^ (-((s : ℂ) + 1))‖) (Set.Ioi T) := by
--     refine Integrable.mono (h₂ (zero_lt_one.trans_le hT₀)) ?_ ?_
--     · exact Measurable.aestronglyMeasurable (by fun_prop)
--     · rw [ae_restrict_iff' measurableSet_Ioi]
--       filter_upwards with t ht
--       rw [norm_mul, norm_mul, norm_norm, norm_norm, norm_norm]
--       sorry
--       -- exact mul_le_mul_of_nonneg_right (hT t ht) (norm_nonneg _)
--   calc
--     _ = (s - 1) * ∫ (t : ℝ) in Set.Ioi T, ‖(g t - l * t) * (t : ℂ) ^ (-(s + 1) : ℂ)‖ := ?_
-- --    _ ≤ (s - 1) * ∫ (t : ℝ) in Set.Ioi T, ‖(g t - l * t)‖ * ‖(t : ℂ) ^ (-(s + 1) : ℂ)‖ := ?_
--     _ ≤ (s - 1) * ∫ (t : ℝ) in Set.Ioi T, ε * t * ‖(t : ℂ) ^ (-(s + 1) : ℂ)‖ := ?_
--     _ = (s - 1) * ∫ (t : ℝ) in Set.Ioi T, ε * ‖(t : ℂ) ^ (-(s : ℂ))‖ := ?_
--     _ ≤ (s - 1) * ∫ (t : ℝ) in Set.Ioi 1, ε * ‖(t : ℂ) ^ (-(s : ℂ))‖ := ?_
--     _ = ε * ((s - 1) * ∫ (t : ℝ) in Set.Ioi 1, t ^ (-s)) := ?_
--     _ = ε := ?_
--   · congr 1
--     refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
--     rw [sub_mul, mul_assoc, h₁ (zero_lt_one.trans (hT₀.trans_lt ht)).ne']
--   · simp_rw [norm_mul]
--     refine mul_le_mul_of_nonneg_left ?_ (sub_pos_of_lt hs).le
--     refine setIntegral_mono_on ?_ ?_ measurableSet_Ioi ?_
--     · sorry -- IntegrableOn (fun t ↦ ε * t * ‖↑t ^ (-(↑s + 1))‖) (Set.Ioi T) volume
--     · sorry -- IntegrableOn (fun t ↦ ε * t * ‖↑t ^ (-(↑s + 1))‖) (Set.Ioi T) volum
--     · intro t ht
--       refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
--       exact hT t ht
--   · refine congr_arg (_ * ·) (setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_)
--     replace ht : 0 < t := (zero_le_one.trans hT₀).trans_lt ht
--     rw [← h₁ (s := s) ht.ne', norm_mul, norm_real, Real.norm_of_nonneg ht.le, mul_assoc]
--   · refine mul_le_mul_of_nonneg_left ?_ (sub_pos_of_lt hs).le
--     refine setIntegral_mono_set ?_ ?_ ?_
--     · sorry -- IntegrableOn (fun t ↦ ε * ‖↑t ^ (-↑s)‖) (Set.Ioi 1) volume
--     · filter_upwards with _ using mul_nonneg hε.le (norm_nonneg _)
--     · exact HasSubset.Subset.eventuallyLE <| Set.Ioi_subset_Ioi hT₀
--   · rw [integral_mul_left, ← mul_assoc, ← mul_assoc, mul_comm ε]
--     refine congr_arg (_ * ·) (setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_)
--     replace ht : 0 ≤ t := zero_le_one.trans ht.le
--     rw [← ofReal_neg, ← ofReal_cpow ht, norm_real, Real.norm_of_nonneg (Real.rpow_nonneg ht _)]
--   · rw [integral_Ioi_rpow_of_lt (by rwa [neg_lt_neg_iff]) zero_lt_one, Real.one_rpow, show -s + 1 =
--       -(s - 1) by ring, neg_div_neg_eq, mul_one_div, div_self (sub_pos_of_lt hs).ne', mul_one]

  --   exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (sub_pos_of_lt hs).le
  -- · exact mul_le_mul_of_nonneg_left (setIntegral_mono_on h₃ (h₂ (zero_lt_one.trans_le hT₀))
  --     measurableSet_Ioi (fun t ht ↦ mul_le_mul_of_nonneg_right (hT t ht) (norm_nonneg _)))
  --     (sub_pos_of_lt hs).le
  -- · refine mul_le_mul_of_nonneg_left ?_ (sub_pos_of_lt hs).le
  --   · refine setIntegral_mono_set (h₂ zero_lt_one) ?_ ?_
  --     · filter_upwards with _ using mul_nonneg (norm_nonneg _) (norm_nonneg _)
  --     · exact HasSubset.Subset.eventuallyLE <| Set.Ioi_subset_Ioi hT₀
  -- · refine congr_arg (_ * ·) (setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_)
  --   rw [norm_mul, Real.norm_of_nonneg hε.le, ← norm_real, mul_assoc, ← norm_mul,
  --     h₁ (zero_lt_one.trans ht).ne']
  -- · rw [integral_mul_left, ← mul_assoc, mul_comm _ ε, ← mul_assoc]
  --   refine congr_arg (_ * ·) (setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_)
  --   have ht : 0 ≤ t := zero_le_one.trans ht.le
  --   rw [← ofReal_neg, ← ofReal_cpow ht, norm_real, Real.norm_of_nonneg (Real.rpow_nonneg ht _)]
  -- · rw [integral_Ioi_rpow_of_lt (by rwa [neg_lt_neg_iff]) zero_lt_one, Real.one_rpow, show -s + 1 =
  --     -(s - 1) by ring, neg_div_neg_eq, mul_one_div, div_self (sub_pos_of_lt hs).ne', mul_one]













#exit






  sorry
  calc
    _ = ‖(s - 1) * s *
          ((∫ (t : ℝ) in Set.Ioi 1, S t * (t : ℂ) ^ (-(s + 1) : ℂ))
            - ∫ (t : ℝ) in Set.Ioi 1, l * (t : ℂ) ^ (-(s : ℂ)))‖ := ?_
    _ = ‖(s - 1) * s *
        ∫ (t : ℝ) in Set.Ioi 1, (S t * (t : ℂ) ^ (-(s + 1) : ℂ) - l * t ^ (-(s : ℂ)))‖ := ?_
    _ ≤ (s - 1) * s *
          ∫ (t : ℝ) in Set.Ioi 1, ‖S t * (t : ℂ) ^ (-(s + 1) : ℂ) - l * t ^ (-(s : ℂ))‖ := ?_
    _ = (s - 1) * s * (Cs +
        ∫ (t : ℝ) in Set.Ioi T, ‖S t * (t : ℂ) ^ (-(s + 1) : ℂ) - l * t ^ (-(s : ℂ))‖) := ?_
    _ ≤ (s - 1) * s * ‖C‖ + s * ((s - 1) *
          ∫ (t : ℝ) in Set.Ioi T, ‖S t * (t : ℂ) ^ (-(s + 1) : ℂ) - l * t ^ (-(s : ℂ))‖) := ?_
    _ ≤ (s - 1) * s * ‖C‖ + s * ε := ?_
  · rw [mul_sub, integral_mul_left, ← mul_assoc, mul_rotate _ _ l, mul_assoc, mul_assoc, h₂,
      mul_one, mul_comm _ l, LSeries_eq_mul_integral _ zero_le_one (by rwa [ofReal_re]) (hfS _ hs)]
    exact isBigO_of_tendsto_sum_div hlim
  · rw [integral_sub]
    ·
      sorry
      -- Integrable (fun t ↦ S t * ↑t ^ (-(↑s + 1))) (volume.restrict (Set.Ioi 1))
    · sorry
      -- Integrable (fun t ↦ l * ↑t ^ (-↑s)) (volume.restrict (Set.Ioi 1))
  · rw [norm_mul, show ((s : ℂ) - 1) * s = ((s - 1) * s : ℝ) by simp, norm_real,
      Real.norm_of_nonneg]
    · refine mul_le_mul_of_nonneg_left ?_ ?_
      · exact norm_integral_le_integral_norm _
      · sorry -- 0 ≤ (s - 1) * s
    · sorry -- 0 ≤ (s - 1) * s
  · rw [← Set.Ioc_union_Ioi_eq_Ioi hT₁, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi]
    · sorry
      -- IntegrableOn (fun t ↦ S t * ↑t ^ (-(↑s + 1)) - l * ↑t ^ (-↑s)) (Set.Ioc 1 T) volume
    · sorry
      -- IntegrableOn (fun t ↦ S t * ↑t ^ (-(↑s + 1)) - l * ↑t ^ (-↑s)) (Set.Ioi T) volume
  · rw [← mul_assoc, mul_comm s, ← mul_add]
    gcongr

#exit
    · sorry  -- 0 ≤ (s - 1) * s
    · refine (norm_add_le _ _).trans ?_
      gcongr
      · sorry -- ‖Cs‖ ≤ ‖C‖
      exact norm_integral_le_integral_norm _
  · gcongr
    refine aux₂ ?_ hε hs hT₁ ?_
    · sorry -- Measurable S
    · intro t ht
      exact (hT t ht.le).le

#exit

include hlim hfS in
private theorem aux₃ {ε : ℝ} (hε : ε > 0) :
    ∃ C ≥ 0, ∀ s : ℝ, 1 < s → ‖(s - 1) * LSeries f s - l * s‖ ≤ (s - 1) * s * C + s * ε := by
  obtain ⟨T, hT₁, hT⟩ :=
    (eventually_forall_ge_atTop.mpr (aux₁ hlim hε)).frequently.forall_exists_of_atTop 1
  set S : ℝ → ℂ := fun t ↦ ∑ k ∈ Icc 1 ⌊t⌋₊, f k
  let C₁ := ∫ t in Set.Ioc 1 T, ‖S t * (t : ℂ) ^ (-2 : ℂ)‖
  let C₂ := ‖l‖ * ∫ t in Set.Ioc 1 T, ‖(t : ℂ) ^ (-1 : ℂ)‖
  have h₁ : 0 ≤ C₁ + C₂ := add_nonneg (integral_nonneg fun _ ↦ norm_nonneg _) <|
      mul_nonneg (norm_nonneg _) (integral_nonneg fun _ ↦ norm_nonneg _)
  refine ⟨C₁ + C₂, h₁, fun s hs ↦ ?_⟩
  let C₁s := ∫ t in Set.Ioc 1 T, S t * (t : ℂ) ^ (-(s + 1) : ℂ)
  let C₂s := l * ∫ t in Set.Ioc 1 T, (t : ℂ) ^ (-s : ℂ)
  let Cs := ∫ t in Set.Ioc 1 T, S t * (t : ℂ) ^ (-(s + 1 : ℂ)) - l * (t : ℂ) ^ (-(s : ℂ))
  let C := ∫ t in Set.Ioc 1 T, ‖S t * (t : ℂ) ^ (-(1 + 1 : ℂ))‖ + ‖l * (t : ℂ) ^ (-(1 : ℂ))‖

  have h₂ : (s - 1) * ∫ (t : ℝ) in Set.Ioi 1, (t : ℂ) ^ (-s : ℂ) = 1 := sorry
  have h₃ {a b : ℝ} (h : a ≤ b) {g : ℝ → ℂ} (hg : IntegrableOn g (Set.Ioi a)) :
      ∫ (t : ℝ) in Set.Ioi a, g t =
        (∫ (t : ℝ) in Set.Ioc a b, g t) + ∫ (t : ℝ) in Set.Ioi b, g t := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi h, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi (hg.mono_set Set.Ioc_subset_Ioi_self) (hg.mono_set (Set.Ioi_subset_Ioi h))]
  calc
    _ = ‖(s - 1) * s *
          ((∫ (t : ℝ) in Set.Ioi 1, S t * (t : ℂ) ^ (-(s + 1) : ℂ))
            - ∫ (t : ℝ) in Set.Ioi 1, l * (t : ℂ) ^ (-(s : ℂ)))‖ := ?_
    _ = ‖(s - 1) * s *
        ∫ (t : ℝ) in Set.Ioi 1, (S t * (t : ℂ) ^ (-(s + 1) : ℂ) - l * t ^ (-(s : ℂ)))‖ := ?_
    _ ≤ (s - 1) * s *
          ‖∫ (t : ℝ) in Set.Ioi 1, S t * (t : ℂ) ^ (-(s + 1) : ℂ) - l * t ^ (-(s : ℂ))‖ := ?_
    _ = (s - 1) * s * ‖Cs +
        ∫ (t : ℝ) in Set.Ioi T, S t * (t : ℂ) ^ (-(s + 1) : ℂ) - l * t ^ (-(s : ℂ))‖ := ?_
    _ ≤ (s - 1) * s * ‖C‖ + s * ((s - 1) *
          ∫ (t : ℝ) in Set.Ioi T, ‖S t * (t : ℂ) ^ (-(s + 1) : ℂ) - l * t ^ (-(s : ℂ))‖) := ?_
    _ ≤ (s - 1) * s * ‖C‖ + s * ε := ?_
  · rw [mul_sub, integral_mul_left, ← mul_assoc, mul_rotate _ _ l, mul_assoc, mul_assoc, h₂,
      mul_one, mul_comm _ l, LSeries_eq_mul_integral _ zero_le_one (by rwa [ofReal_re]) (hfS _ hs)]
    exact isBigO_of_tendsto_sum_div hlim
  · rw [integral_sub]
    ·
      sorry
      -- Integrable (fun t ↦ S t * ↑t ^ (-(↑s + 1))) (volume.restrict (Set.Ioi 1))
    · sorry
      -- Integrable (fun t ↦ l * ↑t ^ (-↑s)) (volume.restrict (Set.Ioi 1))
  · rw [norm_mul, norm_mul, show (s : ℂ) - 1 = (s - 1 : ℝ) by simp, norm_real, norm_real,
      Real.norm_of_nonneg, Real.norm_of_nonneg]
    sorry -- 0 ≤ s
    sorry -- 0 ≤ s - 1
  · rw [← Set.Ioc_union_Ioi_eq_Ioi hT₁, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi]
    · sorry
      -- IntegrableOn (fun t ↦ S t * ↑t ^ (-(↑s + 1)) - l * ↑t ^ (-↑s)) (Set.Ioc 1 T) volume
    · sorry
      -- IntegrableOn (fun t ↦ S t * ↑t ^ (-(↑s + 1)) - l * ↑t ^ (-↑s)) (Set.Ioi T) volume
  · rw [← mul_assoc, mul_comm s, ← mul_add]
    gcongr
    · sorry  -- 0 ≤ (s - 1) * s
    · refine (norm_add_le _ _).trans ?_
      gcongr
      · sorry -- ‖Cs‖ ≤ ‖C‖
      exact norm_integral_le_integral_norm _
  · gcongr
    refine aux₂ ?_ hε hs hT₁ ?_
    · sorry -- Measurable S
    · intro t ht
      exact (hT t ht.le).le





#exit

  · rw [LSeries_eq_mul_integral _ zero_le_one (by rwa [ofReal_re]) (hfS _ hs), mul_sub,
        ← mul_assoc _ l, mul_rotate _ _ l, mul_assoc, mul_assoc, h₂, mul_one, mul_comm l]
    exact isBigO_of_tendsto_sum_div hlim
  · rw [h₃ hT₁, h₃ hT₁]
    · sorry
    · sorry
  · refine le_trans (norm_add_le _ _) <| le_trans (add_le_add_right (norm_sub_le _ _) _) ?_
    rw [norm_mul (((s : ℂ) - 1) * s), norm_mul (((s : ℂ) - 1) * s), norm_mul (((s : ℂ) - 1) * s),
      show (((s : ℂ) - 1) * s)  = ((s - 1) * s : ℝ) by rw [ofReal_mul, ofReal_sub,
        ofReal_one], Complex.norm_real, Real.norm_of_nonneg]
    sorry
  ·




#exit



include hlim hfS in
private theorem key_step {ε : ℝ} (hε : ε > 0) :
    ∃ C ≥ 0, ∀ s : ℝ, 1 < s → ‖(s - 1) * LSeries f s - l * s‖ ≤ (s - 1) * s * C + s * ε := by
  obtain ⟨T', hT'⟩ := (eventually_atTop).mp <| aux₁ hlim hε
  let T := max 1 T'
  have hT₀ : 0 < T := zero_lt_one.trans_le (le_max_left _ _)
  let C₁ := ∫ t in Set.Ioc 1 T, ‖(∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-2 : ℂ)‖
  let C₂ := ‖l‖ * ∫ t in Set.Ioc 1 T, ‖(t : ℂ) ^ (-1 : ℂ)‖
  refine ⟨C₁ + C₂, ?_, fun s hs ↦ ?_⟩
  · exact add_nonneg (integral_nonneg fun _ ↦ norm_nonneg _) <|
      mul_nonneg (norm_nonneg _) (integral_nonneg fun _ ↦ norm_nonneg _)
  · have h₃ : (s - 1) * ∫ (t : ℝ) in Set.Ioi 1, t ^ (-s) = 1 := by
      sorry
--   rw [integral_Ioi_rpow_of_lt (by rwa [neg_lt_neg_iff]) zero_lt_one, Real.one_rpow, neg_div,
--     ← one_div_neg_eq_neg_one_div, neg_add', neg_neg, mul_one_div, div_self (sub_ne_zero.mpr hs.ne')]
    have h₄ : (s - 1) * ∫ (t : ℝ) in Set.Ioi 1, (t : ℂ) ^ (-s : ℂ) = 1 := sorry
-- private theorem sub_mul_int_cpow {s : ℂ} (hs : 1 < s.re) :
--     (s - 1) * ∫ (t : ℝ) in Set.Ioi 1, (t : ℂ) ^ (-s : ℂ) = 1 := by
--   have : 1 - s ≠ 0 := by
--     contrapose! hs
--     rw [← sub_eq_zero.mp hs, one_re]
--   rw [integral_Ioi_cpow_of_lt (by rwa [neg_re, neg_lt_neg_iff]) zero_lt_one, ofReal_one, one_cpow,
--     ← mul_div_assoc, mul_neg_one, neg_add_eq_sub, neg_sub, div_self this]
    have hs' : 0 ≤ (s - 1) * s := mul_nonneg (sub_nonneg.mpr hs.le) (zero_le_one.trans hs.le)
--    have hT₁ : ∀ t ∈ Set.Ioi T,
--        ‖∑ k ∈ Icc 1 ⌊t⌋₊, f k - l * t‖ * ‖(t : ℂ) ^ (-((s : ℂ) + 1))‖ ≤ ‖ε * t‖ *
--          ‖(t : ℂ) ^ (-((s : ℂ) + 1))‖ := fun t ht ↦ by
--      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
--      rw [Real.norm_of_nonneg (mul_nonneg hε.le (hT₀.trans ht).le)]
--      exact (hT' _ (le_trans (le_max_right 1 T') ht.le)).le
    let C₁s := ∫ t in Set.Ioc 1 T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1) : ℂ)
    let C₂s := l * ∫ t in Set.Ioc 1 T, (t : ℂ) ^ (-s : ℂ)
    calc
      _ = ‖(s - 1) * s *
            ((∫ (t : ℝ) in Set.Ioi 1, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1) : ℂ))
              - l * ∫ (t : ℝ) in Set.Ioi 1, (t : ℂ) ^ (-s : ℂ))‖ := ?_
      _ = ‖(s - 1) * s *
            ((∫ (t : ℝ) in Set.Ioc 1 T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1) : ℂ)) +
              (∫ (t : ℝ) in Set.Ioi T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1) : ℂ))
                - l * ((∫ (t : ℝ) in Set.Ioc 1 T, (t : ℂ) ^ (-s : ℂ))
                  + (∫ (t : ℝ) in Set.Ioi T, (t : ℂ) ^ (-s : ℂ))))‖ := ?_
      _ = ‖(s - 1) * s * C₁s  -(s - 1) * s * C₂s +
            (s - 1) * s *
              ((∫ (t : ℝ) in Set.Ioi T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1) : ℂ)) -
                l * (∫ (t : ℝ) in Set.Ioi T, (t : ℂ) ^ (-s : ℂ)))‖ := by congr; ring
      _ ≤ (s - 1) * s * ‖C₁s‖ + (s - 1) * s * ‖C₂s‖ +
            (s - 1) * s *
              ‖(∫ (t : ℝ) in Set.Ioi T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1) : ℂ)) -
                l * (∫ (t : ℝ) in Set.Ioi T, (t : ℂ) ^ (-s : ℂ))‖ := ?_
      _ ≤ (s - 1) * s * C₁ + (s - 1) * s * C₂ +
            (s - 1) * s *
              ‖∫ (t : ℝ) in Set.Ioi T,
                (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1) : ℂ) - l * (t : ℂ) ^ (-s : ℂ)‖ := ?_
      _ ≤ (s - 1) * s * (C₁ + C₂) + s * ε := ?_
    · rw [LSeries_eq_mul_integral _ zero_le_one (by rwa [ofReal_re]) (hfS _ hs), mul_sub,
        ← mul_assoc _ l, mul_rotate _ _ l, mul_assoc, mul_assoc, h₄, mul_one, mul_comm l]
      exact isBigO_of_tendsto_sum_div hlim -- Factor out this result?
    · rw [int_Ioi_eq (le_max_left _ _), int_Ioi_eq (le_max_left 1 _)]
      · rw [integrableOn_Ioi_cpow_iff zero_lt_one]
        rwa [neg_re, ofReal_re, neg_lt_neg_iff]
      · refine integrableOn_Ici_iff_integrableOn_Ioi.mp <|
          intOn_sum_mul_cpow zero_lt_one ?_ (isBigO_of_tendsto_sum_div hlim)
        rwa [ofReal_re]
    · refine le_trans (norm_add_le _ _) <| le_trans (add_le_add_right (norm_sub_le _ _) _) ?_
      rw [norm_mul (((s : ℂ) - 1) * s), norm_mul (((s : ℂ) - 1) * s), norm_mul (((s : ℂ) - 1) * s),
        show (((s : ℂ) - 1) * s)  = ((s - 1) * s : ℝ) by rw [ofReal_mul, ofReal_sub,
          ofReal_one], Complex.norm_real, Real.norm_of_nonneg hs']
    · gcongr
      · exact norm_int_sum_mul_cpow_le (by rw [ofReal_re]; exact hs.le)
      · exact norm_mul_int_cpow_le (by rw [ofReal_re]; exact hs.le)
      · rw [integral_sub, integral_mul_left]
        · exact integrableOn_Ici_iff_integrableOn_Ioi.mp <|
            intOn_sum_mul_cpow hT₀ (by rwa [ofReal_re]) (isBigO_of_tendsto_sum_div hlim)
        · refine Integrable.const_mul ?_ _ -- (intO_cpow hT (by rwa [ofReal_re])) _
          rw [← IntegrableOn, integrableOn_Ioi_cpow_iff hT₀]
          rwa [neg_re, ofReal_re, neg_lt_neg_iff]
    · rw [← mul_add, mul_comm _ s, mul_assoc, mul_assoc]
      gcongr
      refine aux₂ ?_ hε hs (le_max_left _ _) fun t ht ↦ ?_
      · -- Using exact does not work here
        convert Measurable.comp' (by measurability : Measurable fun n : ℕ ↦ ∑ k ∈ Icc 1 n, f k)
          (Nat.measurable_floor (R := ℝ))
      · rw [Real.norm_of_nonneg (mul_nonneg hε.le (hT₀.trans ht).le)]
        exact (hT' t ((le_max_right _ _).trans ht.le)).le








include hlim hfS in
private theorem key_step0 {ε : ℝ} (hε : ε > 0) :
    ∃ C ≥ 0, ∀ s : ℝ, 1 < s → ‖(s - 1) * LSeries f s - l * s‖ ≤ (s - 1) * s * C + s * ε := by
  have h₁ : Measurable (fun t : ℝ ↦ ‖(∑ k in Icc 1 ⌊t⌋₊, f k) - l * t‖) :=
    (((by exact fun _ _ ↦ trivial : Measurable fun n : ℕ ↦ ∑ k ∈ Icc 1 n, f k).comp'
      Nat.measurable_floor).sub (by fun_prop)).norm

  have h₂ {t : ℝ} {s : ℂ} : t ≠ 0 → t * (t : ℂ) ^ (-s - 1) = t ^ (-s) := fun ht ↦ by
    replace ht := ofReal_ne_zero.mpr ht
    rw [cpow_sub _ _ ht, cpow_one, mul_div_cancel₀ _ ht]





  obtain ⟨T', hT'⟩ := (eventually_atTop).mp <| step1 hlim hε
  let T := max 1 T'
  have hT₀ : 0 < T := zero_lt_one.trans_le (le_max_left _ _)
  let C₁ := ∫ t in Set.Ioc 1 T, ‖(∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-2 : ℂ)‖
  let C₂ := ‖l‖ * ∫ t in Set.Ioc 1 T, ‖(t : ℂ) ^ (-1 : ℂ)‖
  refine ⟨C₁ + C₂, ?_, fun s hs ↦ ?_⟩
  · exact add_nonneg (integral_nonneg fun _ ↦ norm_nonneg _) <|
      mul_nonneg (norm_nonneg _) (integral_nonneg fun _ ↦ norm_nonneg _)
  · have h₃ : (s - 1) * ∫ (t : ℝ) in Set.Ioi 1, t ^ (-s) = 1 := by
      sorry
--   rw [integral_Ioi_rpow_of_lt (by rwa [neg_lt_neg_iff]) zero_lt_one, Real.one_rpow, neg_div,
--     ← one_div_neg_eq_neg_one_div, neg_add', neg_neg, mul_one_div, div_self (sub_ne_zero.mpr hs.ne')]

    have h₄ : (s - 1) * ∫ (t : ℝ) in Set.Ioi 1, (t : ℂ) ^ (-s : ℂ) = 1 := sorry
-- private theorem sub_mul_int_cpow {s : ℂ} (hs : 1 < s.re) :
--     (s - 1) * ∫ (t : ℝ) in Set.Ioi 1, (t : ℂ) ^ (-s : ℂ) = 1 := by
--   have : 1 - s ≠ 0 := by
--     contrapose! hs
--     rw [← sub_eq_zero.mp hs, one_re]
--   rw [integral_Ioi_cpow_of_lt (by rwa [neg_re, neg_lt_neg_iff]) zero_lt_one, ofReal_one, one_cpow,
--     ← mul_div_assoc, mul_neg_one, neg_add_eq_sub, neg_sub, div_self this]

    have hs' : 0 ≤ (s - 1) * s := mul_nonneg (sub_nonneg.mpr hs.le) (zero_le_one.trans hs.le)
    have hT₁ : ∀ t ∈ Set.Ioi T,
        ‖∑ k ∈ Icc 1 ⌊t⌋₊, f k - l * t‖ * ‖(t : ℂ) ^ (-((s : ℂ) + 1))‖ ≤ ‖ε * t‖ *
          ‖(t : ℂ) ^ (-((s : ℂ) + 1))‖ := fun t ht ↦ by
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [Real.norm_of_nonneg (mul_nonneg hε.le (hT₀.trans ht).le)]
      exact (hT' _ (le_trans (le_max_right 1 T') ht.le)).le
    let C₁s := ∫ t in Set.Ioc 1 T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1) : ℂ)
    let C₂s := l * ∫ t in Set.Ioc 1 T, (t : ℂ) ^ (-s : ℂ)
    calc
      _ = ‖(s - 1) * s *
            ((∫ (t : ℝ) in Set.Ioi 1, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1) : ℂ))
              - l * ∫ (t : ℝ) in Set.Ioi 1, (t : ℂ) ^ (-s : ℂ))‖ := ?_
      _ = ‖(s - 1) * s *
            ((∫ (t : ℝ) in Set.Ioc 1 T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1) : ℂ)) +
              (∫ (t : ℝ) in Set.Ioi T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1) : ℂ))
                - l * ((∫ (t : ℝ) in Set.Ioc 1 T, (t : ℂ) ^ (-s : ℂ))
                  + (∫ (t : ℝ) in Set.Ioi T, (t : ℂ) ^ (-s : ℂ))))‖ := ?_
      _ = ‖(s - 1) * s * C₁s  -(s - 1) * s * C₂s +
            (s - 1) * s *
              ((∫ (t : ℝ) in Set.Ioi T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1) : ℂ)) -
                l * (∫ (t : ℝ) in Set.Ioi T, (t : ℂ) ^ (-s : ℂ)))‖ := by congr; ring
      _ ≤ (s - 1) * s * ‖C₁s‖ + (s - 1) * s * ‖C₂s‖ +
            (s - 1) * s *
              ‖(∫ (t : ℝ) in Set.Ioi T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1) : ℂ)) -
                l * (∫ (t : ℝ) in Set.Ioi T, (t : ℂ) ^ (-s : ℂ))‖ := ?_
      _ ≤ (s - 1) * s * C₁ + (s - 1) * s * C₂ +
            (s - 1) * s *
              ‖∫ (t : ℝ) in Set.Ioi T,
                (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1) : ℂ) - l * (t : ℂ) ^ (-s : ℂ)‖ := ?_
      _ = (s - 1) * s * (C₁ + C₂) +
            (s - 1) * s *
              ‖∫ (t : ℝ) in Set.Ioi T,
                ((∑ k ∈ Icc 1 ⌊t⌋₊, f k) - l * t) * (t : ℂ) ^ (-(s + 1) : ℂ)‖ := ?_
      _ ≤ (s - 1) * s * (C₁ + C₂) +
            (s - 1) * s *
              ∫ (t : ℝ) in Set.Ioi T,
                ‖((∑ k ∈ Icc 1 ⌊t⌋₊, f k) - l * t)‖ * ‖(t : ℂ) ^ (-(s + 1) : ℂ)‖ := ?_
      _ ≤ (s - 1) * s * (C₁ + C₂) +
            (s - 1) * s * ∫ (t : ℝ) in Set.Ioi T, ‖ε * t‖ * ‖(t : ℂ) ^ (-(s + 1) : ℂ)‖ := ?_
      _ ≤ (s - 1) * s * (C₁ + C₂) +
            (s - 1) * s * ∫ (t : ℝ) in Set.Ioi 1, ‖ε * t‖ * ‖(t : ℂ) ^ (-(s + 1) : ℂ)‖ := ?_
      _ = (s - 1) * s * (C₁ + C₂) +
            (s - 1) * s * ∫ (t : ℝ) in Set.Ioi 1, ε * ‖(t : ℂ) ^ (-s : ℂ)‖ := ?_
      _ = (s - 1) * s * (C₁ + C₂) +
            s * ε * ((s - 1) * ∫ (t : ℝ) in Set.Ioi 1, t ^ (-s)) := ?_
      _ = (s - 1) * s * (C₁ + C₂) + s * ε := by rw [h₃, mul_one]
    · rw [LSeries_eq_mul_integral _ zero_le_one (by rwa [ofReal_re]) (hfS _ hs), mul_sub,
        ← mul_assoc _ l, mul_rotate _ _ l, mul_assoc, mul_assoc, h₄, mul_one, mul_comm l]
      exact isBigO_of_tendsto_sum_div hlim -- Factor out this result?
    · rw [int_Ioi_eq (le_max_left _ _), int_Ioi_eq (le_max_left 1 _)]
      · rw [integrableOn_Ioi_cpow_iff zero_lt_one]
        rwa [neg_re, ofReal_re, neg_lt_neg_iff]
      · refine integrableOn_Ici_iff_integrableOn_Ioi.mp <|
          intOn_sum_mul_cpow zero_lt_one ?_ (isBigO_of_tendsto_sum_div hlim)
        rwa [ofReal_re]
    · refine le_trans (norm_add_le _ _) <| le_trans (add_le_add_right (norm_sub_le _ _) _) ?_
      rw [norm_mul (((s : ℂ) - 1) * s), norm_mul (((s : ℂ) - 1) * s), norm_mul (((s : ℂ) - 1) * s),
        show (((s : ℂ) - 1) * s)  = ((s - 1) * s : ℝ) by rw [ofReal_mul, ofReal_sub,
          ofReal_one], Complex.norm_real, Real.norm_of_nonneg hs']
    · gcongr
      · exact norm_int_sum_mul_cpow_le (by rw [ofReal_re]; exact hs.le)
      · exact norm_mul_int_cpow_le (by rw [ofReal_re]; exact hs.le)
      · rw [integral_sub, integral_mul_left]
        · exact integrableOn_Ici_iff_integrableOn_Ioi.mp <|
            intOn_sum_mul_cpow hT₀ (by rwa [ofReal_re]) (isBigO_of_tendsto_sum_div hlim)
        · refine Integrable.const_mul ?_ _ -- (intO_cpow hT (by rwa [ofReal_re])) _
          rw [← IntegrableOn, integrableOn_Ioi_cpow_iff hT₀]
          rwa [neg_re, ofReal_re, neg_lt_neg_iff]
    · rw [mul_add]
      congr 3
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
      rw [sub_mul, neg_add', mul_assoc, h₂ (hT₀.trans ht).ne']
    · refine add_le_add_left (mul_le_mul_of_nonneg_left ?_ hs') _
      exact le_of_le_of_eq (norm_integral_le_integral_norm _) (by simp_rw [norm_mul])
    · refine add_le_add_left (mul_le_mul_of_nonneg_left
        (setIntegral_mono_on ?_ ?_ measurableSet_Ioi hT₁) hs') _
      · refine Integrable.mono
          (intOn_norm_mul_id_mul_norm_cpow_succ hε.le hT₀ (by rwa [ofReal_re])) ?_
          ((ae_restrict_iff' measurableSet_Ioi).mpr ?_)
        · exact Measurable.aestronglyMeasurable <| h₁.mul (by fun_prop)
        · filter_upwards with t ht
          rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
          exact hT₁ t ht
      · exact intOn_norm_mul_id_mul_norm_cpow_succ hε.le hT₀ (by rwa [ofReal_re])
    · refine add_le_add_left (mul_le_mul_of_nonneg_left (setIntegral_mono_set ?_ ?_ ?_) hs') _
      · refine intOn_norm_mul_id_mul_norm_cpow_succ hε.le zero_lt_one (by rwa [ofReal_re])
      · filter_upwards with _ using mul_nonneg (norm_nonneg _) (norm_nonneg _)
      · exact HasSubset.Subset.eventuallyLE <| Set.Ioi_subset_Ioi (le_max_left _ _)
    · congr 2
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
      rw [norm_mul, mul_assoc, Real.norm_of_nonneg hε.le, ← norm_real, ← norm_mul, neg_add',
        h₂ (zero_lt_one.trans ht).ne']
    · rw [integral_mul_left, ← mul_assoc, ← mul_assoc, ← mul_rotate _ s]
      congr 2
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
      rw [Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht), neg_re,
        ofReal_re]

include hlim hfS in
theorem LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div :
    Tendsto (fun s : ℝ ↦ (s - 1) * LSeries f s) (𝓝[>] 1) (𝓝 l) := by
  refine Metric.tendsto_nhdsWithin_nhds.mpr fun ε hε ↦ ?_
  have hε6 : 0 < ε / 6 := by positivity
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨C, hC₁, hC₂⟩ := key_step hlim hfS hε6
  have lim1 : Tendsto (fun s ↦ (s - 1) * s * C) (𝓝[>] 1) (𝓝 0) := by
    have : ContinuousAt (fun s ↦ (s - 1) * s * C) 1 := by fun_prop
    convert tendsto_nhdsWithin_of_tendsto_nhds this.tendsto
    rw [sub_self, zero_mul, zero_mul]
  have lim2 : Tendsto (fun s : ℝ ↦ s * l) (𝓝[>] 1) (𝓝 l) := by
    have : ContinuousAt (fun s : ℝ ↦ s * l) 1 := by fun_prop
    convert tendsto_nhdsWithin_of_tendsto_nhds this.tendsto
    rw [Complex.ofReal_one, one_mul]
  rw [Metric.tendsto_nhdsWithin_nhds] at lim1 lim2
  obtain ⟨δ₁, _, hδ₁⟩ := lim1 _ hε3
  obtain ⟨δ₂, _, hδ₂⟩ := lim2 _ hε3
  refine ⟨min 1 (min δ₁ δ₂), by positivity, fun s hs₁ hs₂ ↦ ?_⟩
  specialize hC₂ s hs₁
  specialize hδ₁ hs₁ <| hs₂.trans_le <| (min_le_right _ _).trans (min_le_left _ _)
  specialize hδ₂ hs₁ <| hs₂.trans_le <| (min_le_right _ _).trans (min_le_right _ _)
  rw [dist_eq_norm] at hδ₁ hδ₂ hs₂ ⊢
  rw [sub_zero, Real.norm_of_nonneg (mul_nonneg
    (mul_nonneg (sub_nonneg.mpr hs₁.le) (zero_lt_one.trans hs₁).le) hC₁)] at hδ₁
  have sle2 : s < 2 := by
    have := (abs_lt.mp <| Real.norm_eq_abs _ ▸ (hs₂.trans_le (min_le_left _ _))).2
    rwa [sub_lt_iff_lt_add', one_add_one_eq_two] at this
  calc
    _ ≤ ‖(s - 1) * LSeries f s - l * s‖ + ‖l * s - l‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < (s - 1) * s * C + s * (ε / 6) + (ε / 3) := add_lt_add_of_le_of_lt hC₂ (by rwa [mul_comm])
    _ ≤ (ε / 3) + s * (ε / 6) + (ε / 3) := by gcongr
    _ < (ε / 3) + (ε / 3) + (ε / 3) := ?_
    _ = ε := add_thirds ε
  refine add_lt_add_right (add_lt_add_left ?_ (ε / 3)) (ε / 3)
  exact lt_of_lt_of_eq ((mul_lt_mul_right hε6).mpr sle2) (by ring)

theorem LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg (f : ℕ → ℝ) {l : ℝ}
    (hf : Tendsto (fun n ↦ (∑ k ∈ Icc 1 n, f k) / (n : ℝ)) atTop (𝓝 l))
    (hf' : ∀ n, 0 ≤ f n) :
    Tendsto (fun s : ℝ ↦ (s - 1) * LSeries (fun n ↦ f n) s) (𝓝[>] 1) (𝓝 l) := by
  refine  LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div (f := fun n ↦ f n)
    (hf.ofReal.congr fun _ ↦ ?_) fun s hs ↦ ?_
  · simp_rw [ofReal_div, ofReal_sum, ofReal_natCast]
  · exact LSeriesSummable_of_sum_norm_bigO_and_nonneg
      (isBigO_of_tendsto_sum_div hf) hf' zero_le_one (by rwa [ofReal_re])

end proof

end residue
