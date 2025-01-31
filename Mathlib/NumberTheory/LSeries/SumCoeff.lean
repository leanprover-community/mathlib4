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

variable {f : ℕ → ℂ} {l : ℂ} (hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Icc 1 n, f k) / n) atTop (𝓝 l))

section lemmas

include hlim in
private theorem lemma₁ {s : ℝ} (hs : 1 < s) :
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
    suffices Tendsto (fun n ↦ (∑ k ∈ Icc 1 n, f k) / ((n : ℝ) ^ (1 : ℝ) : ℝ)) atTop (𝓝 l) by
      simpa using (isBigO_atTop_natCast_rpow_of_tendsto_div_rpow this).comp_tendsto
        tendsto_nat_floor_atTop
    simpa using hlim
  refine h₁.integrableOn_of_isBigO_atTop (g := fun t ↦ t ^(-s)) ?_ ?_
  · refine IsBigO.mul_atTop_rpow_of_isBigO_rpow 1 (-s - 1) _ h₂ ?_ (by linarith)
    exact (norm_ofReal_cpow_eventually_eq_atTop _).isBigO.of_norm_left
  · rwa [integrableAtFilter_rpow_atTop_iff, neg_lt_neg_iff]

private theorem lemma₂ {s T ε : ℝ} {S : ℝ → ℂ} (hs : 1 < s) (hT : 0 < T)
    (hS₁ : LocallyIntegrableOn (fun t ↦ S t) (Set.Ici 1)) (hS₂ : ∀ t ≥ T, ‖S t‖ ≤ ε * t) :
    IntegrableOn (fun t : ℝ ↦ ‖S t‖ * (t ^ (-s - 1))) (Set.Ici 1) := by
  have h : LocallyIntegrableOn (fun t : ℝ ↦ ‖S t‖ * (t ^ (-s - 1))) (Set.Ici 1) := by
    refine hS₁.norm.mul_continuousOn ?_ isLocallyClosed_Ici
    exact fun t ht ↦ (Real.continuousAt_rpow_const _ _
      <| Or.inl (zero_lt_one.trans_le ht).ne').continuousWithinAt
  refine h.integrableOn_of_isBigO_atTop (g := fun t ↦ t ^(-s)) (isBigO_iff.mpr ⟨ε, ?_⟩) ?_
  · filter_upwards [eventually_ge_atTop T] with t ht
    have ht' : 0 < t := hT.trans_le ht
    rw [norm_mul, norm_norm, show t ^ (-s) = t * t ^ (-s - 1) by
        rw [Real.rpow_sub ht', Real.rpow_one, mul_div_cancel₀ _ ht'.ne'],
      norm_mul, Real.norm_of_nonneg ht'.le, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hS₂ t ht) (norm_nonneg _)
  · exact integrableAtFilter_rpow_atTop_iff.mpr <| neg_lt_neg_iff.mpr hs

end lemmas

section proof

include hlim in
private theorem LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_aux₁ {ε : ℝ} (hε : ε > 0) :
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

private theorem LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_aux₂ {s T ε : ℝ} {S : ℝ → ℂ}
    (hS : LocallyIntegrableOn (fun t ↦ S t - l * t) (Set.Ici 1)) (hε : 0 < ε)
    (hs : 1 < s) (hT₁ : 1 ≤ T) (hT : ∀ t ≥ T, ‖S t - l * t‖ ≤ ε * t) :
    (s - 1) * ∫ (t : ℝ) in Set.Ioi T, ‖S t - l * t‖ * t ^ (-s - 1) ≤ ε := by
  have hT₀ : 0 < T := zero_lt_one.trans_le hT₁
  have h {t : ℝ} (ht : 0 < t) : t ^ (-s) = t * t ^ (-s - 1) := by
    rw [Real.rpow_sub ht, Real.rpow_one, mul_div_cancel₀ _ ht.ne']
  calc
    _ ≤ (s - 1) * ∫ (t : ℝ) in Set.Ioi T, ε * t ^ (-s) := ?_
    _ ≤ ε * ((s - 1) * ∫ (t : ℝ) in Set.Ioi 1, t ^ (-s)) := ?_
    _ = ε := ?_
  · refine mul_le_mul_of_nonneg_left (setIntegral_mono_on ?_ ?_ measurableSet_Ioi fun t ht ↦ ?_) ?_
    · exact (lemma₂ hs hT₀ hS hT).mono_set <| Set.Ioi_subset_Ici_iff.mpr hT₁
    · exact (integrableOn_Ioi_rpow_of_lt (neg_lt_neg_iff.mpr hs) hT₀).const_mul  _
    · have ht' : 0 < t := hT₀.trans ht
      rw [h ht', ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hT t ht.le) (Real.rpow_nonneg ht'.le _)
    · exact (sub_pos_of_lt hs).le
  · rw [integral_mul_left, ← mul_assoc, ← mul_assoc, mul_comm ε]
    refine mul_le_mul_of_nonneg_left (setIntegral_mono_set ?_ ?_
      (Set.Ioi_subset_Ioi hT₁).eventuallyLE) (mul_nonneg (sub_pos_of_lt hs).le hε.le)
    · exact integrableOn_Ioi_rpow_of_lt (neg_lt_neg_iff.mpr hs) zero_lt_one
    · exact (ae_restrict_iff' measurableSet_Ioi).mpr <| univ_mem' fun t ht ↦
        Real.rpow_nonneg (zero_le_one.trans ht.le) _
  · rw [integral_Ioi_rpow_of_lt (by rwa [neg_lt_neg_iff]) zero_lt_one, Real.one_rpow, neg_div,
      ← one_div_neg_eq_neg_one_div, neg_add', neg_neg, mul_one_div,
      div_self (sub_ne_zero.mpr hs.ne'), mul_one]

variable (hfS : ∀ s : ℝ, 1 < s → LSeriesSummable f s)

include hlim hfS in
private theorem LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_aux₃ {ε : ℝ} (hε : ε > 0) :
    ∃ C ≥ 0, ∀ s : ℝ, 1 < s → ‖(s - 1) * LSeries f s - l * s‖ ≤ (s - 1) * s * C + s * ε := by
  obtain ⟨T, hT₁, hT⟩ := (eventually_forall_ge_atTop.mpr
    (LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_aux₁
      hlim hε)).frequently.forall_exists_of_atTop 1
  let S : ℝ → ℂ := fun t ↦ ∑ k ∈ Icc 1 ⌊t⌋₊, f k
  let C := ∫ t in Set.Ioc 1 T, ‖S t - l * t‖ * t ^ (-1 - 1 : ℝ)
  have hC : 0 ≤ C := by
    refine setIntegral_nonneg_ae measurableSet_Ioc (univ_mem' fun t ht ↦ ?_)
    exact mul_nonneg (norm_nonneg _) <| Real.rpow_nonneg (zero_le_one.trans ht.1.le) _
  refine ⟨C, hC, fun s hs ↦ ?_⟩
  have hs' : 0 ≤ (s - 1) * s := mul_nonneg (sub_nonneg.mpr hs.le) (zero_le_one.trans hs.le)
  have h₀ : LocallyIntegrableOn (fun t ↦ S t - l * t) (Set.Ici 1) := by
    refine .sub ?_ <| ContinuousOn.locallyIntegrableOn (by fun_prop) measurableSet_Ici
    convert locallyIntegrableOn_mul_sum_Icc f zero_le_one (locallyIntegrableOn_const 1)
    rw [one_mul]
  have h₁ : IntegrableOn (fun t ↦ ‖S t - l * t‖ * t ^ (-s - 1)) (Set.Ici 1) :=
    lemma₂ hs (zero_lt_one.trans_le hT₁) h₀ fun t ht ↦ (hT t ht).le
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
    _ = ‖((s - 1) * s * ∫ t in Set.Ioi 1, S t * ↑t ^ (-(s : ℂ) - 1)) -
          l * s * ((s - 1) * ∫ (t : ℝ) in Set.Ioi 1, ↑t ^ (-(s : ℂ)))‖ := ?_
    _ = ‖(s - 1) * s *
          ∫ (t : ℝ) in Set.Ioi 1, (S t * (t : ℂ) ^ (-s - 1 : ℂ) - l * t ^ (-s : ℂ))‖ := ?_
    _ = ‖(s - 1) * s * ∫ (t : ℝ) in Set.Ioi 1, (S t - l * t) * (t : ℂ) ^ (-s - 1 : ℂ)‖ := ?_
    _ ≤ (s - 1) * s * ∫ (t : ℝ) in Set.Ioi 1, ‖(S t - l * ↑t) * ↑t ^ (-s - 1 : ℂ)‖ := ?_
    _ = (s - 1) * s * ∫ (t : ℝ) in Set.Ioi 1, ‖S t - l * t‖ * t ^ (-s - 1) := ?_
    _ = (s - 1) * s * (Cs + ∫ (t : ℝ) in Set.Ioi T, ‖S t - l * t‖ * t ^ (-s - 1)) := ?_
    _ ≤ (s - 1) * s * C +
          s * ((s - 1) * ∫ (t : ℝ) in Set.Ioi T, ‖S t - l * t‖ * t ^ (-s - 1)) := ?_
    _ ≤ (s - 1) * s * C + s * ε := ?_
  · rw [h₃, mul_one, mul_comm l, LSeries_eq_mul_integral _ zero_le_one (by rwa [ofReal_re])
      (hfS _ hs), neg_add', mul_assoc]
    exact isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (a := l) (by simpa using hlim)
  · rw [integral_sub, integral_mul_left]
    · congr; ring
    · exact (lemma₁ hlim hs).mono_set Set.Ioi_subset_Ici_self
    · exact (integrableOn_Ioi_cpow_of_lt
        (by rwa [neg_re, ofReal_re, neg_lt_neg_iff]) zero_lt_one).const_mul  _
  · congr 2
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    replace ht : (t : ℂ) ≠ 0 := ne_zero_of_one_lt_re ht
    rw [sub_mul, cpow_sub _ _ ht, cpow_one, mul_assoc, mul_div_cancel₀ _ ht]
  · rw [norm_mul, show ((s : ℂ) - 1) * s = ((s - 1) * s : ℝ) by simp, norm_real,
      Real.norm_of_nonneg hs']
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hs'
  · congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    replace ht : 0 ≤ t := zero_le_one.trans ht.le
    rw [norm_mul, show (-(s : ℂ) - 1) = (-s - 1 : ℝ) by simp, ← ofReal_cpow ht, norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg ht _)]
  · rw [← Set.Ioc_union_Ioi_eq_Ioi hT₁, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi]
    · exact h₁.mono_set <| Set.Ioc_subset_Ioi_self.trans Set.Ioi_subset_Ici_self
    · exact h₁.mono_set <| Set.Ioi_subset_Ici_self.trans <| Set.Ici_subset_Ici.mpr hT₁
  · rw [mul_add, ← mul_assoc, mul_comm s]
    exact add_le_add_right (mul_le_mul_of_nonneg_left h₄ hs') _
  · gcongr
    exact LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_aux₂ h₀ hε hs hT₁
      fun t ht ↦ (hT t ht.le).le

include hlim hfS in
theorem LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div :
    Tendsto (fun s : ℝ ↦ (s - 1) * LSeries f s) (𝓝[>] 1) (𝓝 l) := by
  refine Metric.tendsto_nhdsWithin_nhds.mpr fun ε hε ↦ ?_
  have hε6 : 0 < ε / 6 := by positivity
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨C, hC₁, hC₂⟩ := LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_aux₃ hlim hfS hε6
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
  · refine LSeriesSummable_of_sum_norm_bigO_and_nonneg ?_ hf' zero_le_one (by rwa [ofReal_re])
    exact isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (a := l) (by simpa using hf)

end proof

end residue
