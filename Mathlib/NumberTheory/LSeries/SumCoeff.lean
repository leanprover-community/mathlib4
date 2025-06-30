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
  `r < s.re`, then `LSeries f s = s * ∫ t in Set.Ioi 1, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (-(s + 1))`.

* `LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div` : assume that `f : ℕ → ℂ` satisfies that
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
  LSeriesSummable_of_sum_norm_bigO (by simpa [abs_of_nonneg (hf _)]) hr hs

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
    rw [← insert_Icc_add_one_left_eq_Icc n.zero_le, sum_insert (by aesop), hf, zero_add, zero_add]
  simp_rw [← h₄] at hO
  rw [← integral_const_mul]
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
  LSeries_eq_mul_integral' _ hr hs <| hO.congr_left fun _ ↦ by simp [abs_of_nonneg (hf _)]

end integralrepresentation

noncomputable section residue

variable {f : ℕ → ℂ} {l : ℂ}

section lemmas

private theorem lemma₁ (hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Icc 1 n, f k) / n) atTop (𝓝 l))
    {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s : ℂ) - 1)) (Set.Ici 1) := by
  have h₁ : LocallyIntegrableOn (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s : ℂ) - 1))
        (Set.Ici 1) := by
    simp_rw [mul_comm]
    refine locallyIntegrableOn_mul_sum_Icc f zero_le_one ?_
    refine ContinuousOn.locallyIntegrableOn (fun t ht ↦ ?_) measurableSet_Ici
    exact (continuousAt_ofReal_cpow_const _ _ <|
      Or.inr (zero_lt_one.trans_le ht).ne').continuousWithinAt
  have h₂ : (fun t : ℝ ↦ ∑ k ∈ Icc 1 ⌊t⌋₊, f k) =O[atTop] fun t ↦ t ^ (1 : ℝ) := by
    simp_rw [Real.rpow_one]
    refine IsBigO.trans_isEquivalent ?_ isEquivalent_nat_floor
    have : Tendsto (fun n ↦ (∑ k ∈ Icc 1 n, f k) / ((n : ℝ) ^ (1 : ℝ) : ℝ)) atTop (𝓝 l) := by
      simpa using hlim
    simpa using (isBigO_atTop_natCast_rpow_of_tendsto_div_rpow this).comp_tendsto
        tendsto_nat_floor_atTop
  refine h₁.integrableOn_of_isBigO_atTop (g := fun t ↦ t ^(-s)) ?_ ?_
  · refine IsBigO.mul_atTop_rpow_of_isBigO_rpow 1 (-s - 1) _ h₂ ?_ (by linarith)
    exact (norm_ofReal_cpow_eventually_eq_atTop _).isBigO.of_norm_left
  · rwa [integrableAtFilter_rpow_atTop_iff, neg_lt_neg_iff]

private theorem lemma₂ {s T ε : ℝ} {S : ℝ → ℂ} (hs : 1 < s)
    (hS₁ : LocallyIntegrableOn (fun t ↦ S t) (Set.Ici 1)) (hS₂ : ∀ t ≥ T, ‖S t‖ ≤ ε * t) :
    IntegrableOn (fun t : ℝ ↦ ‖S t‖ * (t ^ (-s - 1))) (Set.Ici 1) := by
  have h : LocallyIntegrableOn (fun t : ℝ ↦ ‖S t‖ * (t ^ (-s - 1))) (Set.Ici 1) := by
    refine hS₁.norm.mul_continuousOn ?_ isLocallyClosed_Ici
    exact fun t ht ↦ (Real.continuousAt_rpow_const _ _
      <| Or.inl (zero_lt_one.trans_le ht).ne').continuousWithinAt
  refine h.integrableOn_of_isBigO_atTop (g := fun t ↦ t ^(-s)) (isBigO_iff.mpr ⟨ε, ?_⟩) ?_
  · filter_upwards [eventually_ge_atTop T, eventually_gt_atTop 0] with t ht ht'
    simpa [abs_of_nonneg, Real.rpow_nonneg, ht'.le, Real.rpow_sub ht', mul_assoc, ht'.ne',
      mul_div_cancel₀] using mul_le_mul_of_nonneg_right (hS₂ t ht) (norm_nonneg <| t ^ (-s - 1))
  · exact integrableAtFilter_rpow_atTop_iff.mpr <| neg_lt_neg_iff.mpr hs

end lemmas

section proof
-- See `LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_aux₃` for the strategy of proof

private theorem LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_aux₁
  (hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Icc 1 n, f k) / n) atTop (𝓝 l)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ‖(∑ k ∈ Icc 1 ⌊t⌋₊, f k) - l * t‖ < ε * t := by
  have h_lim' : Tendsto (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, f k : ℂ) / t) atTop (𝓝 l) := by
    refine (mul_one l ▸ ofReal_one ▸ ((hlim.comp tendsto_nat_floor_atTop).mul <|
      tendsto_ofReal_iff.mpr <| tendsto_nat_floor_div_atTop)).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    simp [div_mul_div_cancel₀ (show (⌊t⌋₊ : ℂ) ≠ 0 by simpa)]
  filter_upwards [eventually_gt_atTop 0, Metric.tendsto_nhds.mp h_lim' ε hε] with t ht₁ ht₂
  rwa [dist_eq_norm, div_sub' (ne_zero_of_re_pos ht₁), norm_div, norm_real,
    Real.norm_of_nonneg ht₁.le, mul_comm, div_lt_iff₀ ht₁] at ht₂

private theorem LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_aux₂ {s T ε : ℝ} {S : ℝ → ℂ}
    (hS : LocallyIntegrableOn (fun t ↦ S t - l * t) (Set.Ici 1)) (hε : 0 < ε)
    (hs : 1 < s) (hT₁ : 1 ≤ T) (hT : ∀ t ≥ T, ‖S t - l * t‖ ≤ ε * t) :
    (s - 1) * ∫ (t : ℝ) in Set.Ioi T, ‖S t - l * t‖ * t ^ (-s - 1) ≤ ε := by
  have hT₀ : 0 < T := zero_lt_one.trans_le hT₁
  have h {t : ℝ} (ht : 0 < t) : t ^ (-s) = t * t ^ (-s - 1) := by
    rw [Real.rpow_sub ht, Real.rpow_one, mul_div_cancel₀ _ ht.ne']
  calc
    _ ≤ (s - 1) * ∫ (t : ℝ) in Set.Ioi T, ε * t ^ (-s) := by
      refine mul_le_mul_of_nonneg_left (setIntegral_mono_on ?_ ?_ measurableSet_Ioi fun t ht ↦ ?_)
        (sub_pos_of_lt hs).le
      · exact (lemma₂ hs hS hT).mono_set <| Set.Ioi_subset_Ici_iff.mpr hT₁
      · exact (integrableOn_Ioi_rpow_of_lt (neg_lt_neg_iff.mpr hs) hT₀).const_mul  _
      · have ht' : 0 < t := hT₀.trans ht
        rw [h ht', ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hT t ht.le) (Real.rpow_nonneg ht'.le _)
    _ ≤ ε * ((s - 1) * ∫ (t : ℝ) in Set.Ioi 1, t ^ (-s)) := by
      rw [integral_const_mul, ← mul_assoc, ← mul_assoc, mul_comm ε]
      refine mul_le_mul_of_nonneg_left (setIntegral_mono_set ?_ ?_
        (Set.Ioi_subset_Ioi hT₁).eventuallyLE) (mul_nonneg (sub_pos_of_lt hs).le hε.le)
      · exact integrableOn_Ioi_rpow_of_lt (neg_lt_neg_iff.mpr hs) zero_lt_one
      · exact (ae_restrict_iff' measurableSet_Ioi).mpr <| univ_mem' fun t ht ↦
        Real.rpow_nonneg (zero_le_one.trans ht.le) _
    _ = ε := by
      rw [integral_Ioi_rpow_of_lt (by rwa [neg_lt_neg_iff]) zero_lt_one, Real.one_rpow]
      field_simp [show -s + 1 ≠ 0 by linarith, hε.ne']
      ring

private theorem LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_aux₃
    (hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Icc 1 n, f k) / n) atTop (𝓝 l))
    (hfS : ∀ s : ℝ, 1 < s → LSeriesSummable f s) {ε : ℝ} (hε : ε > 0) :
    ∃ C ≥ 0, (fun s : ℝ ↦ ‖(s - 1) * LSeries f s - s * l‖) ≤ᶠ[𝓝[>] 1]
      fun s ↦ (s - 1) * s * C + s * ε := by
  obtain ⟨T, hT₁, hT⟩ := (eventually_forall_ge_atTop.mpr
    (LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_aux₁
      hlim hε)).frequently.forall_exists_of_atTop 1
  let S : ℝ → ℂ := fun t ↦ ∑ k ∈ Icc 1 ⌊t⌋₊, f k
  let C := ∫ t in Set.Ioc 1 T, ‖S t - l * t‖ * t ^ (-1 - 1 : ℝ)
  have hC : 0 ≤ C := by
    refine setIntegral_nonneg_ae measurableSet_Ioc (univ_mem' fun t ht ↦ ?_)
    exact mul_nonneg (norm_nonneg _) <| Real.rpow_nonneg (zero_le_one.trans ht.1.le) _
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_mem_nhdsWithin] with s hs
  rw [Set.mem_Ioi] at hs
  have hs' : 0 ≤ (s - 1) * s := mul_nonneg (sub_nonneg.mpr hs.le) (zero_le_one.trans hs.le)
  have h₀ : LocallyIntegrableOn (fun t ↦ S t - l * t) (Set.Ici 1) := by
    refine .sub ?_ <| ContinuousOn.locallyIntegrableOn (by fun_prop) measurableSet_Ici
    simpa using locallyIntegrableOn_mul_sum_Icc f zero_le_one (locallyIntegrableOn_const 1)
  have h₁ : IntegrableOn (fun t ↦ ‖S t - l * t‖ * t ^ (-s - 1)) (Set.Ici 1) :=
    lemma₂ hs h₀ fun t ht ↦ (hT t ht).le
  have h₂ : IntegrableOn (fun t : ℝ ↦ ‖S t - l * t‖ * (t ^ ((-1 : ℝ) - 1))) (Set.Ioc 1 T) := by
    refine ((h₀.norm.mul_continuousOn ?_ isLocallyClosed_Ici).integrableOn_compact_subset
      Set.Icc_subset_Ici_self isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
    exact fun t ht ↦ (Real.continuousAt_rpow_const _ _
      <| Or.inl (zero_lt_one.trans_le ht).ne').continuousWithinAt
  have h₃ : (s - 1) * ∫ (t : ℝ) in Set.Ioi 1, (t : ℂ) ^ (-s : ℂ) = 1 := by
    rw [integral_Ioi_cpow_of_lt (by rwa [neg_re, neg_lt_neg_iff]) zero_lt_one, ofReal_one,
      one_cpow, show -(s : ℂ) + 1 = -(s - 1) by ring, neg_div_neg_eq, mul_div_cancel₀]
    exact (sub_ne_zero.trans ofReal_ne_one).mpr hs.ne'
  let Cs := ∫ t in Set.Ioc 1 T, ‖S t - l * t‖ * t ^ (-s - 1)
  have h₄ : Cs ≤ C := by
    refine setIntegral_mono_on ?_ h₂ measurableSet_Ioc fun t ht ↦ ?_
    · exact h₁.mono_set <| Set.Ioc_subset_Ioi_self.trans Set.Ioi_subset_Ici_self
    · gcongr
      exact ht.1.le
  calc
    -- First, we replace `s * l` by `(s - 1) * s` times the integral of `l * t ^ (-s)` using `h₃`
    -- and replace `LSeries f s` by its integral representation.
    _ = ‖((s - 1) * s * ∫ t in Set.Ioi 1, S t * ↑t ^ (-(s : ℂ) - 1)) -
          l * s * ((s - 1) * ∫ (t : ℝ) in Set.Ioi 1, ↑t ^ (-(s : ℂ)))‖ := by
      rw [h₃, mul_one, mul_comm l, LSeries_eq_mul_integral _ zero_le_one (by rwa [ofReal_re])
        (hfS _ hs), neg_add', mul_assoc]
      exact isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (a := l) (by simpa using hlim)
    _ = ‖(s - 1) * s * ∫ t in Set.Ioi 1, (S t * (t : ℂ) ^ (-s - 1 : ℂ) - l * t ^ (-s : ℂ))‖ := by
      rw [integral_sub, integral_const_mul]
      · congr; ring
      · exact (lemma₁ hlim hs).mono_set Set.Ioi_subset_Ici_self
      · exact (integrableOn_Ioi_cpow_of_lt
          (by rwa [neg_re, ofReal_re, neg_lt_neg_iff]) zero_lt_one).const_mul  _
    _ = ‖(s - 1) * s * ∫ t in Set.Ioi 1, (S t - l * t) * (t : ℂ) ^ (-s - 1 : ℂ)‖ := by
      congr 2
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
      replace ht : (t : ℂ) ≠ 0 := ne_zero_of_one_lt_re ht
      rw [sub_mul, cpow_sub _ _ ht, cpow_one, mul_assoc, mul_div_cancel₀ _ ht]
    _ ≤ (s - 1) * s * ∫ t in Set.Ioi 1, ‖(S t - l * ↑t) * ↑t ^ (-s - 1 : ℂ)‖ := by
      rw [norm_mul, show ((s : ℂ) - 1) * s = ((s - 1) * s : ℝ) by simp, norm_real,
        Real.norm_of_nonneg hs']
      exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hs'
    -- Next, step is to bound the integral of `‖S t - l * t‖ * t ^ (-s - 1)`.
    _ = (s - 1) * s * ∫ t in Set.Ioi 1, ‖S t - l * t‖ * t ^ (-s - 1) := by
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
      replace ht : 0 ≤ t := zero_le_one.trans ht.le
      rw [norm_mul, show (-(s : ℂ) - 1) = (-s - 1 : ℝ) by simp, ← ofReal_cpow ht, norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg ht _)]
    -- For that, we cut the integral in two parts using `T` as the cutting point.
    _ = (s - 1) * s * (Cs + ∫ t in Set.Ioi T, ‖S t - l * t‖ * t ^ (-s - 1)) := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi hT₁, setIntegral_union Set.Ioc_disjoint_Ioi_same
        measurableSet_Ioi]
      · exact h₁.mono_set <| Set.Ioc_subset_Ioi_self.trans Set.Ioi_subset_Ici_self
      · exact h₁.mono_set <| Set.Ioi_subset_Ici_self.trans <| Set.Ici_subset_Ici.mpr hT₁
    -- The first part can be bounded by `C` using `h₄`.
    _ ≤ (s - 1) * s * C + s * ((s - 1) * ∫ t in Set.Ioi T, ‖S t - l * t‖ * t ^ (-s - 1)) := by
      rw [mul_add, ← mul_assoc, mul_comm s]
      gcongr
    -- The second part is bounded using `LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_aux₂`
    -- since `‖S t - l t‖ ≤ ε * t` for all `t ≥ T`.
    _ ≤ (s - 1) * s * C + s * ε := by
      gcongr
      exact LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_aux₂ h₀ hε hs hT₁
        fun t ht ↦ (hT t ht.le).le

theorem LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div
    (hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Icc 1 n, f k) / n) atTop (𝓝 l))
    (hfS : ∀ s : ℝ, 1 < s → LSeriesSummable f s) :
    Tendsto (fun s : ℝ ↦ (s - 1) * LSeries f s) (𝓝[>] 1) (𝓝 l) := by
  have h₁ {C ε : ℝ} : Tendsto (fun s ↦ (s - 1) * s * C + s * ε) (𝓝[>] 1) (𝓝 ε) := by
    rw [show 𝓝 ε = 𝓝 ((1 - 1) * 1 * C + 1 * ε) by congr; ring]
    exact tendsto_nhdsWithin_of_tendsto_nhds (ContinuousAt.tendsto (by fun_prop))
  have h₂ : IsBoundedUnder
      (fun x1 x2 ↦ x1 ≤ x2) (𝓝[>] 1) fun s : ℝ ↦ ‖(s - 1) * LSeries f s - s * l‖ := by
    obtain ⟨C, _, hC₂⟩ :=
      LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_aux₃ hlim hfS zero_lt_one
    exact h₁.isBoundedUnder_le.mono_le hC₂
  suffices Tendsto (fun s : ℝ ↦ (s - 1) * LSeries f s - s * l) (𝓝[>] 1) (𝓝 0) by
    rw [show 𝓝 l = 𝓝 (0 + 1 * l) by congr; ring]
    have h₃ : Tendsto (fun s : ℝ ↦ s * l) (𝓝[>] 1) (𝓝 (1 * l)) :=
      tendsto_nhdsWithin_of_tendsto_nhds (ContinuousAt.tendsto (by fun_prop))
    exact (this.add h₃).congr fun _ ↦ by ring
  refine tendsto_zero_iff_norm_tendsto_zero.mpr <| tendsto_of_le_liminf_of_limsup_le ?_ ?_ h₂ ?_
  · exact le_liminf_of_le h₂.isCoboundedUnder_ge (univ_mem' (fun _ ↦ norm_nonneg _))
  · refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    rw [zero_add]
    obtain ⟨C, hC₁, hC₂⟩ := LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_aux₃ hlim hfS hε
    refine le_of_le_of_eq (limsup_le_limsup hC₂ ?_ h₁.isBoundedUnder_le) h₁.limsup_eq
    exact isCoboundedUnder_le_of_eventually_le _ (univ_mem' fun _ ↦ norm_nonneg _)
  · exact isBoundedUnder_of_eventually_ge (univ_mem' fun _ ↦ norm_nonneg _)

theorem LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg (f : ℕ → ℝ) {l : ℝ}
    (hf : Tendsto (fun n ↦ (∑ k ∈ Icc 1 n, f k) / (n : ℝ)) atTop (𝓝 l))
    (hf' : ∀ n, 0 ≤ f n) :
    Tendsto (fun s : ℝ ↦ (s - 1) * LSeries (fun n ↦ f n) s) (𝓝[>] 1) (𝓝 l) := by
  refine  LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div (f := fun n ↦ f n)
    (hf.ofReal.congr fun _ ↦ ?_) fun s hs ↦ ?_
  · simp
  · refine LSeriesSummable_of_sum_norm_bigO_and_nonneg ?_ hf' zero_le_one hs
    exact isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa)

end proof

end residue
