/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Littlewood's (1912) Theorem: Mertens Bound Implies the Riemann Hypothesis

This file formalizes Littlewood's 1912 forward theorem: if the Mertens summatory function
`M(x) = ∑ n ≤ ⌊x⌋₊, μ(n)` satisfies `M(x) = O(x ^ (1 / 2 + ε))` as `x → ∞` for every
`ε > 0`, then the Mellin transform representation `s * ∫_{1}^{∞} M(t) t^{-(s + 1)} dt` of
`1 / ζ(s)` extends holomorphically to `{s : ℂ | 1 / 2 < s.re}`, eliminating zeros of
`riemannZeta` off the critical line and proving `RiemannHypothesis`.
-/

@[expose] public section

open scoped LSeries.notation Topology
open Asymptotics Complex Filter MeasureTheory Set

/-- The Mertens summatory function `M(x) = ∑_{n ≤ x} μ(n)`. -/
noncomputable def mertens (x : ℝ) : ℤ :=
  ∑ n ∈ Finset.Iic ⌊x⌋₊, ArithmeticFunction.moebius n

/-- The Mellin-Mertens transform `s * ∫ x in Ioi 1, M(x) * x ^ (-(s + 1))`, representing
`1 / ζ(s)` on `1 < s.re` and extending analytically to `1 / 2 < s.re` under Littlewood's bound. -/
noncomputable def mellinMertens (s : ℂ) : ℂ :=
  s * ∫ x in Set.Ioi (1 : ℝ), (mertens x : ℂ) * (x : ℂ) ^ (-(s + 1))

private noncomputable def moebiusC : ℕ → ℂ := fun n => (ArithmeticFunction.moebius n : ℂ)

private noncomputable def mertensIndicator (x : ℝ) : ℂ :=
  if 1 < x then (mertens x : ℂ) else 0

private noncomputable def mellinMertensInv (s : ℂ) : ℂ :=
  if s = 1 then (riemannZeta 1)⁻¹ else mellinMertens s

private lemma mertens_cast_eq_sum_Icc (x : ℝ) :
    (mertens x : ℂ) = ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, moebiusC k := by
  dsimp [mertens, moebiusC]
  push_cast
  have hIic : Finset.Iic ⌊x⌋₊ = insert 0 (Finset.Icc 1 ⌊x⌋₊) := by
    ext k
    simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hIic, Finset.sum_insert (by simp)]
  simp

private lemma moebiusC_sum_norm_isBigO :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖moebiusC k‖) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
  have h_le : ∑ k ∈ Finset.Icc 1 n, ‖moebiusC k‖ ≤ (n : ℝ) := by
    calc ∑ k ∈ Finset.Icc 1 n, ‖moebiusC k‖
        ≤ ∑ _k ∈ Finset.Icc 1 n, (1 : ℝ) := by
          refine Finset.sum_le_sum fun k _ => ?_
          simpa [moebiusC, Complex.norm_intCast] using
            (show |(ArithmeticFunction.moebius k : ℝ)| ≤ 1 by
              exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k))
      _ = (Finset.Icc 1 n).card := by simp
      _ ≤ n := by
          norm_cast
          simp [Nat.card_Icc]
  have h_nn : 0 ≤ ∑ k ∈ Finset.Icc 1 n, ‖moebiusC k‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  simpa [Real.norm_of_nonneg h_nn, Real.rpow_one, Real.norm_natCast] using h_le

/-- On `1 < s.re`, Abel summation identifies `LSeries ↗μ s = mellinMertens s`, giving
`riemannZeta s * mellinMertens s = 1`. -/
theorem riemannZeta_mul_mellinMertens_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * mellinMertens s = 1 := by
  have h_int : LSeries moebiusC s = mellinMertens s := by
    rw [LSeries_eq_mul_integral' moebiusC zero_le_one hs moebiusC_sum_norm_isBigO]
    dsimp [mellinMertens]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [mertens_cast_eq_sum_Icc]
  have h_mul : riemannZeta s * LSeries moebiusC s = 1 := by
    have hz : LSeries (1 : ℕ → ℂ) s = riemannZeta s := LSeries_one_eq_riemannZeta hs
    have hmul : LSeries (1 : ℕ → ℂ) s * LSeries (↗ArithmeticFunction.moebius) s = 1 :=
      LSeries_one_mul_Lseries_moebius hs
    rw [hz] at hmul
    have h_congr : LSeries (↗ArithmeticFunction.moebius) s = LSeries moebiusC s :=
      LSeries_congr (fun _ => by simp [moebiusC]) s
    rwa [h_congr] at hmul
  rwa [← h_int]

private lemma mellinMertens_eq_mul_mellin (s : ℂ) :
    mellinMertens s = s * mellin mertensIndicator (-s) := by
  dsimp [mellinMertens, mellin]
  congr 1
  have h_eq : EqOn
      ((Set.Ioi 1).indicator fun t : ℝ => (mertens t : ℂ) * (t : ℂ) ^ (-(s + 1)))
      (fun t : ℝ => (t : ℂ) ^ ((-s) - 1) * mertensIndicator t)
      (Set.Ioi 0) := by
    intro t _ht
    by_cases ht1 : 1 < t
    · have h_exp : (-s - 1 : ℂ) = -(s + 1) := by ring
      simp [mertensIndicator, ht1, mul_comm, h_exp]
    · simp [mertensIndicator, ht1]
  rw [← setIntegral_congr_fun measurableSet_Ioi h_eq, setIntegral_indicator measurableSet_Ioi]
  have h_inter : Set.Ioi (0 : ℝ) ∩ Set.Ioi 1 = Set.Ioi 1 := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioi]
    exact ⟨fun h => h.2, fun h => ⟨zero_lt_one.trans h, h⟩⟩
  rw [h_inter]

private lemma locallyIntegrableOn_mertensIndicator :
    LocallyIntegrableOn mertensIndicator (Set.Ioi 0) := by
  have h_sum : LocallyIntegrableOn (fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, moebiusC k)
      (Set.Ici 0) := by
    simpa using locallyIntegrableOn_mul_sum_Icc (𝕜 := ℂ) (c := moebiusC) (m := 1)
      le_rfl (locallyIntegrableOn_const (1 : ℂ))
  have h_loc : LocallyIntegrableOn (fun t : ℝ => (mertens t : ℂ)) (Set.Ioi 0) := by
    have h_fn : (fun t : ℝ => (mertens t : ℂ)) =
        fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, moebiusC k :=
      funext mertens_cast_eq_sum_Icc
    rw [h_fn]
    exact h_sum.mono_set Set.Ioi_subset_Ici_self
  rw [locallyIntegrableOn_iff isLocallyClosed_Ioi]
  intro K hK_sub hK_cpt
  have h_ind : IntegrableOn ((Set.Ioi 1).indicator (fun t : ℝ => (mertens t : ℂ))) K :=
    (h_loc.integrableOn_compact_subset hK_sub hK_cpt).indicator measurableSet_Ioi
  refine h_ind.congr_fun (fun t _ => ?_) hK_cpt.measurableSet
  by_cases ht : 1 < t <;> simp [mertensIndicator, ht]

private lemma mertensIndicator_isBigO_atTop {ε : ℝ}
    (hO : (fun x : ℝ => (mertens x : ℝ)) =O[atTop] fun x : ℝ => x ^ ((1 / 2 : ℝ) + ε)) :
    mertensIndicator =O[atTop] fun x : ℝ => x ^ ((1 / 2 : ℝ) + ε) := by
  obtain ⟨C, hC⟩ := hO.bound
  refine IsBigO.of_bound C ?_
  filter_upwards [hC] with x hx
  by_cases hx1 : 1 < x
  · simpa [mertensIndicator, hx1, Complex.norm_intCast] using hx
  · simp only [mertensIndicator, hx1, ↓reduceIte, norm_zero]
    exact le_trans (norm_nonneg _) hx

private lemma mertensIndicator_isBigO_nhdsWithin_zero (b : ℝ) :
    mertensIndicator =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ (-b) := by
  refine (isBigO_zero (fun x : ℝ => x ^ (-b)) (𝓝[>] 0)).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds one_pos)] with x hx
  simp [mertensIndicator, not_lt.mpr (le_of_lt hx)]

/-- Under the `O(x ^ (1/2 + ε))` Mertens growth hypothesis, `mellinMertens` is
complex-differentiable at every point `s` with `1 / 2 < s.re`. -/
theorem mellinMertens_differentiableAt_of_isBigO
    (hM : ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => (mertens x : ℝ)) =O[atTop] fun x => x ^ ((1 / 2 : ℝ) + ε))
    {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ mellinMertens s := by
  have h_fn : mellinMertens = fun z : ℂ => z * mellin mertensIndicator (-z) :=
    funext mellinMertens_eq_mul_mellin
  rw [h_fn]
  set ε : ℝ := (s.re - 1 / 2) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  set a : ℝ := -((1 / 2 : ℝ) + ε)
  set b : ℝ := (-s).re - 1
  have hf_top : mertensIndicator =O[atTop] (· ^ (-a)) := by
    simpa [a, neg_neg] using mertensIndicator_isBigO_atTop (hM ε hε)
  have hs_top : (-s).re < a := by rw [neg_re]; dsimp [a, ε]; linarith
  have hs_bot : b < (-s).re := by dsimp [b]; linarith
  have hm_diff : DifferentiableAt ℂ (mellin mertensIndicator) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow locallyIntegrableOn_mertensIndicator
      hf_top hs_top (mertensIndicator_isBigO_nhdsWithin_zero b) hs_bot
  exact differentiableAt_id.mul (hm_diff.comp s differentiableAt_id.neg)

private lemma isOpen_re_gt (r : ℝ) : IsOpen {s : ℂ | r < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

private lemma convex_linear_gt (f : ℂ →ₗ[ℝ] ℝ) (r : ℝ) : Convex ℝ {s : ℂ | r < f s} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq, map_add, map_smul, smul_eq_mul] at hx hy ⊢
  by_cases ha0 : 0 < a
  · calc r = a * r + b * r := by rw [← add_mul, hab, one_mul]
      _ < a * f x + b * f y := add_lt_add_of_lt_of_le
          (mul_lt_mul_of_pos_left hx ha0) (mul_le_mul_of_nonneg_left hy.le hb)
  · have ha0' : a = 0 := le_antisymm (not_lt.mp ha0) ha
    have hb1 : b = 1 := by linarith
    rw [ha0', hb1]
    linarith

private lemma convex_linear_lt (f : ℂ →ₗ[ℝ] ℝ) (r : ℝ) : Convex ℝ {s : ℂ | f s < r} := by
  simpa [neg_lt_neg_iff] using convex_linear_gt (-f) (-r)

/-- Analytic continuation of `riemannZeta s * mellinMertens s = 1` to all `s` with
`1 / 2 < s.re` and `s ≠ 1`. -/
theorem riemannZeta_mul_mellinMertens_eq_one_of_isBigO
    (hM : ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => (mertens x : ℝ)) =O[atTop] fun x => x ^ ((1 / 2 : ℝ) + ε)) :
    ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s * mellinMertens s = 1 := by
  let F : ℂ → ℂ := fun s => riemannZeta s * mellinMertens s
  let U : Set ℂ := {s : ℂ | 1 / 2 < s.re} \ {1}
  have hU_open : IsOpen U := (isOpen_re_gt (1 / 2)).sdiff isClosed_singleton
  have hF_diff : DifferentiableOn ℂ F U := fun s hs =>
    ((differentiableAt_riemannZeta hs.2).mul
      (mellinMertens_differentiableAt_of_isBigO hM hs.1)).differentiableWithinAt
  have hF_ana : AnalyticOnNhd ℂ F U := hF_diff.analyticOnNhd hU_open
  let U_top : Set ℂ := {s : ℂ | 1 / 2 < s.re} ∩ {s : ℂ | 0 < s.im}
  let U_bot : Set ℂ := {s : ℂ | 1 / 2 < s.re} ∩ {s : ℂ | s.im < 0}
  let U_strip : Set ℂ := {s : ℂ | 1 / 2 < s.re} ∩ {s : ℂ | s.re < 1}
  have hU_top_sub : U_top ⊆ U := fun s hs => ⟨hs.1, fun h1 => by subst h1; simp [U_top] at hs⟩
  have hU_bot_sub : U_bot ⊆ U := fun s hs => ⟨hs.1, fun h1 => by subst h1; simp [U_bot] at hs⟩
  have hU_strip_sub : U_strip ⊆ U := fun s hs =>
    ⟨hs.1, fun h1 => by subst h1; simp [U_strip] at hs⟩
  have h_re_gt : Convex ℝ {s : ℂ | 1 / 2 < s.re} := convex_linear_gt Complex.reLm (1 / 2)
  have hU_top_pre : IsPreconnected U_top :=
    (h_re_gt.inter (convex_linear_gt Complex.imLm 0)).isPreconnected
  have hU_bot_pre : IsPreconnected U_bot :=
    (h_re_gt.inter (convex_linear_lt Complex.imLm 0)).isPreconnected
  have hU_strip_pre : IsPreconnected U_strip :=
    (h_re_gt.inter (convex_linear_lt Complex.reLm 1)).isPreconnected
  have h_one_ana : ∀ V : Set ℂ, AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) V :=
    fun _ => analyticOnNhd_const
  have h_eq_top : EqOn F (fun _ => (1 : ℂ)) U_top := by
    have hz0 : (2 : ℂ) + Complex.I ∈ U_top := by norm_num [U_top]
    have h_ev : F =ᶠ[𝓝 ((2 : ℂ) + Complex.I)] (fun _ => (1 : ℂ)) := by
      filter_upwards [(isOpen_re_gt 1).mem_nhds (by norm_num : 1 < ((2 : ℂ) + Complex.I).re)]
        with z hz
      exact riemannZeta_mul_mellinMertens_of_one_lt_re hz
    exact (hF_ana.mono hU_top_sub).eqOn_of_preconnected_of_eventuallyEq
      (h_one_ana U_top) hU_top_pre hz0 h_ev
  have h_eq_bot : EqOn F (fun _ => (1 : ℂ)) U_bot := by
    have hz0 : (2 : ℂ) - Complex.I ∈ U_bot := by norm_num [U_bot]
    have h_ev : F =ᶠ[𝓝 ((2 : ℂ) - Complex.I)] (fun _ => (1 : ℂ)) := by
      filter_upwards [(isOpen_re_gt 1).mem_nhds (by norm_num : 1 < ((2 : ℂ) - Complex.I).re)]
        with z hz
      exact riemannZeta_mul_mellinMertens_of_one_lt_re hz
    exact (hF_ana.mono hU_bot_sub).eqOn_of_preconnected_of_eventuallyEq
      (h_one_ana U_bot) hU_bot_pre hz0 h_ev
  have h_eq_strip : EqOn F (fun _ => (1 : ℂ)) U_strip := by
    have hz0 : ((3 / 4 : ℝ) : ℂ) + Complex.I ∈ U_strip := by norm_num [U_strip]
    have h_U_top_open : IsOpen U_top :=
      (isOpen_re_gt (1 / 2)).inter (isOpen_lt continuous_const Complex.continuous_im)
    have h_ev : F =ᶠ[𝓝 (((3 / 4 : ℝ) : ℂ) + Complex.I)] (fun _ => (1 : ℂ)) := by
      filter_upwards [h_U_top_open.mem_nhds
          (by norm_num [U_top] : ((3 / 4 : ℝ) : ℂ) + Complex.I ∈ U_top)]
        with z hz
      exact h_eq_top hz
    exact (hF_ana.mono hU_strip_sub).eqOn_of_preconnected_of_eventuallyEq
      (h_one_ana U_strip) hU_strip_pre hz0 h_ev
  intro s hs hne
  rcases lt_trichotomy s.re 1 with hlt | heq | hgt
  · exact h_eq_strip ⟨hs, hlt⟩
  · have him : s.im ≠ 0 := fun h0 => hne (Complex.ext (by simp [heq]) h0)
    rcases lt_or_gt_of_ne him with him_lt | him_gt
    · exact h_eq_bot ⟨hs, him_lt⟩
    · exact h_eq_top ⟨hs, him_gt⟩
  · exact riemannZeta_mul_mellinMertens_of_one_lt_re hgt

/-- Under `M(x) = O(x ^ (1 / 2 + ε))` for all `ε > 0`, `mellinMertensInv` furnishes a right
inverse to `riemannZeta` across the open half-plane `{s : ℂ | 1 / 2 < s.re}`. -/
theorem mertens_inversion_of_bound
    (hM : ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => (mertens x : ℝ)) =O[atTop] fun x => x ^ ((1 / 2 : ℝ) + ε)) :
    ∃ I_M : ℂ → ℂ, ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s * I_M s = 1 := by
  refine ⟨mellinMertensInv, fun s hs => ?_⟩
  by_cases h1 : s = 1
  · subst h1
    simp only [mellinMertensInv, ↓reduceIte]
    exact mul_inv_cancel₀ (riemannZeta_ne_zero_of_one_le_re (by norm_num))
  · simp only [mellinMertensInv, h1, ↓reduceIte]
    exact riemannZeta_mul_mellinMertens_eq_one_of_isBigO hM s hs h1

/-- Reflection symmetry for non-trivial zeros of `riemannZeta` across `Re(s) = 1 / 2`,
proved from the functional equation `riemannZeta_one_sub`. -/
theorem riemannZeta_zero_reflection {s : ℂ} (hz : riemannZeta s = 0)
    (h_not_triv : ¬∃ n : ℕ, s = -2 * (n + 1)) (h_not_one : s ≠ 1) (_hs_lt : s.re < 1 / 2) :
    riemannZeta (1 - s) = 0 ∧ 1 / 2 < (1 - s).re := by
  refine ⟨?_, by rw [Complex.sub_re, Complex.one_re]; linarith⟩
  have h_not_neg_nat : ∀ n : ℕ, s ≠ -(n : ℂ) := by
    intro n hn
    subst hn
    rcases n with _ | n
    · simp [riemannZeta_zero] at hz
    · rcases Nat.even_or_odd (n + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
      · refine h_not_triv ⟨m - 1, ?_⟩
        have h1 : n + 1 = 2 * ((m - 1) + 1) := by omega
        push_cast [h1]
        ring
      · let w : ℂ := ((2 * m + 2 : ℕ) : ℂ)
        have hw_not_neg : ∀ j : ℕ, w ≠ -(j : ℂ) := fun j h_eq => by
          have := congr_arg Complex.re h_eq
          simp [w] at this
          linarith
        have hw_ne_one : w ≠ 1 := fun h_eq => by
          have := congr_arg Complex.re h_eq
          simp [w] at this
          linarith
        have h_fe := riemannZeta_one_sub hw_not_neg hw_ne_one
        have h_1mw : 1 - w = -(↑(n + 1) : ℂ) := by dsimp [w]; push_cast [hm]; ring
        rw [h_1mw, hz] at h_fe
        have h_cpow_ne : (2 * (Real.pi : ℂ)) ^ (-w) ≠ 0 := by
          rw [Complex.cpow_ne_zero_iff]
          left
          exact_mod_cast (mul_ne_zero two_ne_zero Real.pi_ne_zero)
        have h_gamma_ne : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hw_not_neg
        have h_cos_ne : Complex.cos ((Real.pi : ℂ) * w / 2) ≠ 0 := by
          intro hcos
          rw [Complex.cos_eq_zero_iff] at hcos
          rcases hcos with ⟨k, hk⟩
          have hw2 : (Real.pi : ℂ) * w / 2 =
              ((((m + 1 : ℕ) : ℝ) * Real.pi : ℝ) : ℂ) := by dsimp [w]; push_cast; ring
          have hk2 : (2 * (k : ℂ) + 1) * (Real.pi : ℂ) / 2 =
              ((((2 * k + 1 : ℤ) / 2 : ℝ) * Real.pi : ℝ) : ℂ) := by push_cast; ring
          rw [hw2, hk2] at hk
          have hdiv : ((m + 1 : ℕ) : ℝ) = ((2 * k + 1 : ℤ) / 2 : ℝ) :=
            mul_right_cancel₀ Real.pi_ne_zero (Complex.ofReal_injective hk)
          have hdiv2 : (2 : ℝ) * ((m + 1 : ℕ) : ℝ) = ((2 * k + 1 : ℤ) : ℝ) := by linarith
          have hint : (2 * ((m : ℤ) + 1)) = 2 * k + 1 := by exact_mod_cast hdiv2
          omega
        have h_zeta_ne : riemannZeta w ≠ 0 :=
          riemannZeta_ne_zero_of_one_le_re (by dsimp [w]; norm_cast; omega)
        have h_rhs_ne : 2 * (2 * (Real.pi : ℂ)) ^ (-w) * Complex.Gamma w *
            Complex.cos ((Real.pi : ℂ) * w / 2) * riemannZeta w ≠ 0 :=
          mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h_cpow_ne)
            h_gamma_ne) h_cos_ne) h_zeta_ne
        exact h_rhs_ne h_fe.symm
  rw [riemannZeta_one_sub h_not_neg_nat h_not_one, hz, mul_zero]

/-- **Littlewood's (1912) Forward Theorem:** If `M(x) = O(x ^ (1 / 2 + ε))` as `x → ∞` for every
`ε > 0`, then `RiemannHypothesis` holds. -/
theorem RiemannHypothesis.of_mertens_isBigO
    (hM : ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => (mertens x : ℝ)) =O[atTop] fun x => x ^ ((1 / 2 : ℝ) + ε)) :
    RiemannHypothesis := by
  rcases mertens_inversion_of_bound hM with ⟨I_M, hI⟩
  have h_nz : ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0 := fun s hs h0 => by
    have h1 := hI s hs
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  intro s hs_zero hs_not_triv hs_not_one
  by_contra h_ne
  rcases lt_or_gt_of_ne h_ne with hs_lt | hs_gt
  · have ⟨h_refl_zero, h_refl_gt⟩ :=
      riemannZeta_zero_reflection hs_zero hs_not_triv hs_not_one hs_lt
    exact h_nz (1 - s) h_refl_gt h_refl_zero
  · exact h_nz s hs_gt hs_zero
