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
  `(∑ k ∈ Icc 1 n, ‖f k‖)` are `O(n ^ r)` for some real `0 ≤ r`, then L-series `Lseries f`
  converges at `s : ℂ` for all `s` such that `r < s.re`.

  * `LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div` : assume that `f : ℕ → ℂ` satifies that
  `(∑ k ∈ Icc 1 n, f k) / n` tends to some complex number `l` when `n → ∞` and that the L-series
  `Lseries f` converges for all `s : ℝ` suchh that `1 < s`. Then `(s - 1) * LSeries f s` tends
  to `l` when `s → 1` with `1 < s`.

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
  simp_rw [Nat.range_succ_Icc_zero, term_def₀ hf]
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

theorem LSeries_eq_mul_integral_of_nonneg (f : ℕ → ℝ) {r : ℝ} (hr : 0 ≤ r) {s : ℂ} (hs : r < s.re)
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) (hf : ∀ n, 0 ≤ f n) :
    LSeries (fun n ↦ f n) s =
      s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, (f k : ℂ)) * t ^ (- (s + 1)) := by
  refine LSeries_eq_mul_integral _ hr hs ?_ ?_
  · refine LSeriesSummable_of_sum_norm_bigO (hO.congr_left fun _ ↦ ?_) hr hs
    simp_rw [norm_real, Real.norm_of_nonneg (hf _)]
  · refine (hO.congr_left fun _ ↦ ?_).of_norm_left
    rw [← ofReal_sum, norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ (hf _))]

end integralrepresentation

noncomputable section residue

variable {f : ℕ → ℂ}

section lemmas

-- Miscellaneous results

private theorem mes_norm_sum_sub {g : ℕ → ℂ} {c : ℂ} :
     Measurable (fun t : ℝ ↦ ‖(∑ k in Icc 1 ⌊t⌋₊, g k) - c * t‖) :=
  (((by exact fun _ _ ↦ trivial : Measurable fun n : ℕ ↦ ∑ k ∈ Icc 1 n, g k).comp'
    Nat.measurable_floor).sub (by fun_prop)).norm

private theorem norm_mul_id_mul_norm_cpow_succ {ε t : ℝ} {c : ℂ} (hε : 0 ≤ ε) (ht : t ≠ 0) :
    ‖ε * t‖ * ‖(t : ℂ) ^ (- (c + 1))‖ = ε * ‖(t : ℂ) ^ (- c)‖ := by
  replace ht := ofReal_ne_zero.mpr ht
  rw [← norm_real, ←  norm_mul, ofReal_mul, mul_assoc, norm_mul, norm_real, Real.norm_of_nonneg hε,
    neg_add', cpow_sub _ _ ht, cpow_one, mul_div_cancel₀ _ ht]

private theorem norm_cpow_le_norm_cpow {t : ℝ} {c d : ℂ} (ht : 1 ≤ t) (hc : d.re ≤ c.re) :
    ‖(t : ℂ) ^ (- c)‖ ≤ ‖(t : ℂ) ^ (- d)‖ := by
  simp_rw [eqOn_norm_cpow (zero_lt_one.trans_le ht)]
  refine Real.rpow_le_rpow_of_exponent_le ht (neg_le_neg_iff.mpr hc)

private theorem isBigO_of_tendsto_sum_div {𝕜 : Type*} [RCLike 𝕜] {f : ℕ → 𝕜} {l : 𝕜}
    (hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Icc 1 n, f k) / n) atTop (𝓝 l)) :
    (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
  simp_rw [Real.rpow_one]
  refine isBigO_norm_left.mp <| isBigO_of_div_tendsto_nhds ?_ ‖l‖ ?_
  · filter_upwards [eventually_ne_atTop 0] with _ h using by simp [h]
  · simpa only [Function.comp_def, norm_div, RCLike.norm_natCast] using (tendsto_norm.comp hlim)

-- Some more results about integrability

private theorem intOn_norm_cpow {T : ℝ} (hT : 0 < T) {c : ℂ} (hc : 1 < c.re) :
    IntegrableOn (fun t : ℝ ↦ ‖(t : ℂ) ^ (- c)‖) (Set.Ioi T) :=
  ((integrableOn_Ioi_rpow_iff hT).mpr (by rwa [neg_lt_neg_iff])).congr_fun
    (eqOn_norm_cpow.symm.mono (Set.Ioi_subset_Ioi hT.le)) measurableSet_Ioi

private theorem intOn_norm_mul_id_mul_norm_cpow_succ {ε : ℝ} {T : ℝ} {c : ℂ} (hε : 0 ≤ ε)
    (hT : 0 < T) (hc : 1 < c.re) :
    IntegrableOn (fun t : ℝ ↦ ‖ε * t‖ * ‖(t : ℂ) ^ (- (c + 1))‖) (Set.Ioi T) := by
  refine IntegrableOn.congr_fun (f := fun t : ℝ ↦ ε * ‖(t : ℂ) ^ (- c)‖) ?_ ?_ measurableSet_Ioi
  · exact (intOn_norm_cpow hT hc).const_mul _
  · exact fun t ht ↦ (norm_mul_id_mul_norm_cpow_succ hε (hT.trans ht).ne').symm

private theorem locintOn_sum_mul_cpow {a : ℝ} {c : ℂ} (ha : 0 < a) (hc : 0 < c.re) :
    LocallyIntegrableOn (fun t ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * ↑t ^ (-(c + 1))) (Set.Ici a) := by
  simp_rw [mul_comm]
  refine locallyIntegrableOn_mul_sum _ ha.le <|
    integrableOn_Ici_iff_integrableOn_Ioi.mpr (intO_cpow ha ?_)
  rwa [add_re, one_re, lt_add_iff_pos_left]

private theorem intOn_sum_mul_cpow {f : ℕ → ℂ} {a : ℝ} {c : ℂ} (ha : 0 < a) (hc : 1 < c.re)
    (hf : (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun t ↦ (t : ℝ) ^ (1 : ℝ)) :
    IntegrableOn (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- (c + 1))) (Set.Ici a) := by
  refine (locintOn_sum_mul_cpow ha (zero_lt_one.trans hc)).integrableOn_of_isBigO_atTop ?_ <|
    integrableAtFilter_rpow_atTop (by rwa [neg_lt_neg_iff])
  refine mul_atTop_of_le 1 (- (c + 1).re) _ (floor_atTop zero_le_one hf) ?_ ?_
  · exact isBigO_norm_left.mp <| norm_cpow_atTop
  · rw [add_re, one_re, neg_add_rev, add_neg_cancel_left]

private theorem intOn_Icc_cpow {a b : ℝ} {c : ℂ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (- c)) (Set.Icc a b) := by
  refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
  exact continuous_ofReal.continuousOn.cpow_const
    (fun x hx ↦ ofReal_mem_slitPlane.mpr (ha.trans_le hx.1))

private theorem intOn_Icc_sum_mul_cpow {a b : ℝ} {c : ℂ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- c)) (Set.Icc a b) := by
  simp_rw [mul_comm]
  exact integrableOn_mul_sum _ ha.le (intOn_Icc_cpow ha)

-- Some results about integrals

private theorem int_Ioi_eq {a b : ℝ} (h : a ≤ b) {g : ℝ → ℂ} (hg : IntegrableOn g (Set.Ioi a)) :
    ∫ (t : ℝ) in Set.Ioi a, g t =
      (∫ (t : ℝ) in Set.Ioc a b, g t) + ∫ (t : ℝ) in Set.Ioi b, g t := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi h, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi (hg.mono_set Set.Ioc_subset_Ioi_self) (hg.mono_set (Set.Ioi_subset_Ioi h))]

private theorem sub_mul_int_rpow {s : ℝ} (hs : 1 < s) :
    (s - 1) * ∫ (t : ℝ) in Set.Ioi 1, t ^ (- s) = 1 := by
  rw [integral_Ioi_rpow_of_lt (by rwa [neg_lt_neg_iff]) zero_lt_one, Real.one_rpow, neg_div,
    ← one_div_neg_eq_neg_one_div, neg_add', neg_neg, mul_one_div, div_self (sub_ne_zero.mpr hs.ne')]

private theorem sub_mul_int_cpow {s : ℂ} (hs : 1 < s.re) :
    (s - 1) * ∫ (t : ℝ) in Set.Ioi 1, (t : ℂ) ^ (- s : ℂ) = 1 := by
  have : 1 - s ≠ 0 := by
    contrapose! hs
    rw [← sub_eq_zero.mp hs, one_re]
  rw [integral_Ioi_cpow_of_lt (by rwa [neg_re, neg_lt_neg_iff]) zero_lt_one, ofReal_one, one_cpow,
    ← mul_div_assoc, mul_neg_one, neg_add_eq_sub, neg_sub, div_self this]

private theorem norm_mul_int_cpow_le {T : ℝ} {c l : ℂ} (hc : 1 ≤ c.re):
    ‖l * ∫ (t : ℝ) in Set.Ioc 1 T, (t : ℂ) ^ (- c)‖ ≤
      ‖l‖ * ∫ (t : ℝ) in Set.Ioc 1 T, ‖(t : ℂ) ^ (- 1 : ℂ)‖ := by
  by_cases hT : 1 < T
  · rw [norm_mul]
    refine mul_le_mul_of_nonneg_left (le_trans (norm_integral_le_integral_norm _)
      (setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun t ht ↦ ?_)) (norm_nonneg _)
    · exact (integrableOn_Icc_iff_integrableOn_Ioc.mp <| intOn_Icc_cpow zero_lt_one).norm
    · exact (integrableOn_Icc_iff_integrableOn_Ioc.mp <| intOn_Icc_cpow zero_lt_one).norm
    · exact norm_cpow_le_norm_cpow ht.1.le hc
  · rw [Set.Ioc_eq_empty hT, setIntegral_empty, setIntegral_empty, mul_zero, norm_zero, mul_zero]

private theorem norm_int_sum_mul_cpow_le {T : ℝ} {c : ℂ} (hc : 1 ≤ c.re) :
    ‖∫ (t : ℝ) in Set.Ioc 1 T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- (c + 1))‖ ≤
      ∫ (t : ℝ) in Set.Ioc 1 T, ‖(∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-2 : ℂ)‖ := by
  by_cases hT : 1 < T
  · refine le_trans (norm_integral_le_integral_norm _) <|
      setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun t ht ↦ ?_
    · exact (integrableOn_Icc_iff_integrableOn_Ioc.mp <| intOn_Icc_sum_mul_cpow zero_lt_one).norm
    · exact (integrableOn_Icc_iff_integrableOn_Ioc.mp <| intOn_Icc_sum_mul_cpow zero_lt_one).norm
    · rw [norm_mul, norm_mul]
      refine mul_le_mul_of_nonneg_left (norm_cpow_le_norm_cpow ht.1.le ?_) (norm_nonneg _)
      rwa [re_ofNat, add_re, ← sub_le_iff_le_add, one_re, show (2 : ℝ) - 1 = 1 by norm_num]
  · rw [Set.Ioc_eq_empty hT, setIntegral_empty, setIntegral_empty, norm_zero]

end lemmas

section proof

variable {l : ℂ} (hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Icc 1 n, f k) / n) atTop (𝓝 l))

include hlim in
private theorem step1 {ε : ℝ} (hε : ε > 0) :
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

variable (hfS : ∀ s : ℝ, 1 < s → LSeriesSummable f s)

include hlim hfS in
private theorem key_step {ε : ℝ} (hε : ε > 0) :
    ∃ C ≥ 0, ∀ s : ℝ, 1 < s → ‖(s - 1) * LSeries f s - l * s‖ ≤ (s - 1) * s * C + s * ε := by
  obtain ⟨T₀, hT₀⟩ := (eventually_atTop).mp <| step1 hlim hε
  let T := max 1 T₀
  have hT : 0 < T := zero_lt_one.trans_le (le_max_left _ _)
  let C₁ := ∫ t in Set.Ioc 1 T, ‖(∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- 2 : ℂ)‖
  let C₂ := ‖l‖ * ∫ t in Set.Ioc 1 T, ‖(t : ℂ) ^ (- 1 : ℂ)‖
  refine ⟨C₁ + C₂, ?_, ?_⟩
  · exact add_nonneg (integral_nonneg fun _ ↦ norm_nonneg _) <|
      mul_nonneg (norm_nonneg _) (integral_nonneg fun _ ↦ norm_nonneg _)
  · intro s hs
    have hs' : 0 ≤ (s - 1) * s := mul_nonneg (sub_nonneg.mpr hs.le) (zero_le_one.trans hs.le)
    have hT' : ∀ t ∈ Set.Ioi T,
        ‖∑ k ∈ Icc 1 ⌊t⌋₊, f k - l * t‖ * ‖(t : ℂ) ^ (- ((s : ℂ) + 1))‖ ≤ ‖ε * t‖ *
          ‖(t : ℂ) ^ (- ((s : ℂ) + 1))‖ := fun t ht ↦ by
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [Real.norm_of_nonneg (mul_nonneg hε.le (hT.trans ht).le)]
      exact (hT₀ _ (le_trans (le_max_right 1 T₀) ht.le)).le
    let C₁s := ∫ t in Set.Ioc 1 T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- (s + 1) : ℂ)
    let C₂s := l * ∫ t in Set.Ioc 1 T, (t : ℂ) ^ (- s : ℂ)
    calc
      _ = ‖(s - 1) * s *
            ((∫ (t : ℝ) in Set.Ioi 1, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- (s + 1) : ℂ))
              - l * ∫ (t : ℝ) in Set.Ioi 1, (t : ℂ) ^ (- s : ℂ))‖ := ?_
      _ = ‖(s - 1) * s *
            ((∫ (t : ℝ) in Set.Ioc 1 T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- (s + 1) : ℂ)) +
              (∫ (t : ℝ) in Set.Ioi T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- (s + 1) : ℂ))
                - l * ((∫ (t : ℝ) in Set.Ioc 1 T, (t : ℂ) ^ (- s : ℂ))
                  + (∫ (t : ℝ) in Set.Ioi T, (t : ℂ) ^ (- s : ℂ))))‖ := ?_
      _ = ‖(s - 1) * s * C₁s  - (s - 1) * s * C₂s +
            (s - 1) * s *
              ((∫ (t : ℝ) in Set.Ioi T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- (s + 1) : ℂ)) -
                l * (∫ (t : ℝ) in Set.Ioi T, (t : ℂ) ^ (- s : ℂ)))‖ := by congr; ring
      _ ≤ (s - 1) * s * ‖C₁s‖ + (s - 1) * s * ‖C₂s‖ +
            (s - 1) * s *
              ‖(∫ (t : ℝ) in Set.Ioi T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- (s + 1) : ℂ)) -
                l * (∫ (t : ℝ) in Set.Ioi T, (t : ℂ) ^ (- s : ℂ))‖ := ?_
      _ ≤ (s - 1) * s * C₁ + (s - 1) * s * C₂ +
            (s - 1) * s *
              ‖∫ (t : ℝ) in Set.Ioi T,
                (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- (s + 1) : ℂ) - l * (t : ℂ) ^ (- s : ℂ)‖ := ?_
      _ = (s - 1) * s * (C₁ + C₂) +
            (s - 1) * s *
              ‖∫ (t : ℝ) in Set.Ioi T,
                ((∑ k ∈ Icc 1 ⌊t⌋₊, f k) - l * t) * (t : ℂ) ^ (- (s + 1) : ℂ)‖ := ?_
      _ ≤ (s - 1) * s * (C₁ + C₂) +
            (s - 1) * s *
              ∫ (t : ℝ) in Set.Ioi T,
                ‖((∑ k ∈ Icc 1 ⌊t⌋₊, f k) - l * t)‖ * ‖(t : ℂ) ^ (- (s + 1) : ℂ)‖ := ?_
      _ ≤ (s - 1) * s * (C₁ + C₂) +
            (s - 1) * s * ∫ (t : ℝ) in Set.Ioi T, ‖ε * t‖ * ‖(t : ℂ) ^ (- (s + 1) : ℂ)‖ := ?_
      _ ≤ (s - 1) * s * (C₁ + C₂) +
            (s - 1) * s * ∫ (t : ℝ) in Set.Ioi 1, ‖ε * t‖ * ‖(t : ℂ) ^ (- (s + 1) : ℂ)‖ := ?_
      _ = (s - 1) * s * (C₁ + C₂) +
            (s - 1) * s * ∫ (t : ℝ) in Set.Ioi 1, ε * ‖(t : ℂ) ^ (- s : ℂ)‖ := ?_
      _ = (s - 1) * s * (C₁ + C₂) +
            s * ε * ((s - 1) * ∫ (t : ℝ) in Set.Ioi 1, t ^ (- s)) := ?_
      _ = (s - 1) * s * (C₁ + C₂) + s * ε := by rw [sub_mul_int_rpow hs, mul_one]
    · rw [LSeries_eq_mul_integral _ zero_le_one (by rwa [ofReal_re]) (hfS _ hs), mul_sub,
        ← mul_assoc _ l, mul_rotate _ _ l, mul_assoc, mul_assoc, sub_mul_int_cpow
        (by rwa [ofReal_re]), mul_one, mul_comm l]
      exact isBigO_of_tendsto_sum_div hlim -- Factor out this result?
    · rw [int_Ioi_eq (le_max_left 1 T₀), int_Ioi_eq (le_max_left 1 T₀)]
      · exact intO_cpow zero_lt_one (by rwa [ofReal_re])
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
            intOn_sum_mul_cpow hT (by rwa [ofReal_re]) (isBigO_of_tendsto_sum_div hlim)
        · exact Integrable.const_mul (intO_cpow hT (by rwa [ofReal_re])) _
    · rw [mul_add]
      congr 3
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
      replace ht : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hT.trans ht).ne'
      rw [sub_mul, neg_add', cpow_sub _ _ ht, cpow_one, mul_assoc, mul_div_cancel₀ _ ht]
    · refine add_le_add_left (mul_le_mul_of_nonneg_left ?_ hs') _
      exact le_of_le_of_eq (norm_integral_le_integral_norm _) (by simp_rw [norm_mul])
    · refine add_le_add_left (mul_le_mul_of_nonneg_left
        (setIntegral_mono_on ?_ ?_ measurableSet_Ioi hT') hs') _
      · refine Integrable.mono
          (intOn_norm_mul_id_mul_norm_cpow_succ hε.le hT (by rwa [ofReal_re])) ?_
          ((ae_restrict_iff' measurableSet_Ioi).mpr ?_)
        · refine Measurable.aestronglyMeasurable ?_
          exact mes_norm_sum_sub.mul (by fun_prop)
        · filter_upwards with t ht
          rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
          exact hT' t ht
      · exact intOn_norm_mul_id_mul_norm_cpow_succ hε.le hT (by rwa [ofReal_re])
    · refine add_le_add_left (mul_le_mul_of_nonneg_left (setIntegral_mono_set ?_ ?_ ?_) hs') _
      · refine intOn_norm_mul_id_mul_norm_cpow_succ hε.le zero_lt_one (by rwa [ofReal_re])
      · filter_upwards with _ using mul_nonneg (norm_nonneg _) (norm_nonneg _)
      · exact HasSubset.Subset.eventuallyLE <| Set.Ioi_subset_Ioi (le_max_left 1 T₀)
    · congr 2
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
      rw [norm_mul_id_mul_norm_cpow_succ hε.le (zero_lt_one.trans ht).ne']
    · rw [integral_mul_left, ← mul_assoc, ← mul_assoc, ← mul_rotate _ s]
      congr 2
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
      simp_rw [eqOn_norm_cpow ((Set.Ioi_subset_Ioi zero_le_one) ht), ofReal_re]

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
