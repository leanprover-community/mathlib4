/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Vasyunin Diagonal and Báez-Duarte Projection Integrals
Exact `L^1(0, 1)` and `L^2(0, 1)` integrals: `∫₀¹ {1/x} dx = 1 - γ`,
`∫₀¹ {1/(kx)} dx = (ln k + 1 - γ) / k`, `∫₀¹ {1/x}² dx = ln(2π) - γ - 1`, and
`∫₀¹ {1/(kx)}² dx = (ln(2π) - γ - 1/k) / k`.
-/

@[expose] public section

open MeasureTheory Set Filter Finset

/-- The reciprocal fractional-part function `x ↦ {1 / x}`. -/
noncomputable def recipFract (x : ℝ) : ℝ := Int.fract (1 / x)

/-- The `k`-th dilated reciprocal fractional-part function `x ↦ {1 / (k * x)}`. -/
noncomputable def recipFractScaled (k : ℕ) (x : ℝ) : ℝ := Int.fract (1 / ((k : ℝ) * x))

/-- Linear Vasyunin RHS coefficient `b_k = (log k + 1 - γ) / k`. -/
noncomputable def bVasyunin (k : ℕ) (gamma_E : ℝ) : ℝ := (Real.log k + 1 - gamma_E) / (k : ℝ)

private lemma intervalIntegrable_recipFractScaled_pow (p k : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x => recipFractScaled k x ^ p) volume a b := by
  have hm : Measurable (fun x => recipFractScaled k x ^ p) :=
    (measurable_fract.comp (measurable_const.div (measurable_const.mul measurable_id))).pow_const p
  exact (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' hm.aestronglyMeasurable
    (ae_of_all _ fun x => by
      dsimp only [recipFractScaled]; rw [Real.norm_of_nonneg (pow_nonneg (Int.fract_nonneg _) p)]
      exact pow_le_one₀ (Int.fract_nonneg _) (Int.fract_lt_one _).le)

private lemma intervalIntegral_split_recip {f : ℝ → ℝ}
    (hf : ∀ a b : ℝ, IntervalIntegrable f volume a b) (L : ℕ) (hL : 1 ≤ L) :
    (∫ x in (1 / (L : ℝ))..1, f x) =
      ∑ n ∈ Ico 1 L, ∫ x in (1 / ((n : ℝ) + 1))..(1 / (n : ℝ)), f x := by
  induction L, hL using Nat.le_induction with
  | base => simp
  | succ k hk ih => push_cast; rw [← intervalIntegral.integral_add_adjacent_intervals
      (hf (1 / ((k : ℝ) + 1)) (1 / (k : ℝ))) (hf (1 / (k : ℝ)) 1), ih,
      sum_Ico_succ_top hk, add_comm]

private lemma intervalIntegral_zero_to_one_of_tendsto {f : ℝ → ℝ}
    (hf : ∀ a b : ℝ, IntervalIntegrable f volume a b) (hbd : ∀ x, ‖f x‖ ≤ (1 : ℝ))
    {L : ℝ} (hlim : Tendsto (fun M : ℕ => ∫ x in (1 / ((M : ℝ) + 1))..1, f x) atTop (nhds L)) :
    (∫ x in (0 : ℝ)..1, f x) = L := by
  have hzero : Tendsto (fun M : ℕ => ∫ x in (0 : ℝ)..(1 / ((M : ℝ) + 1)), f x)
      atTop (nhds 0) := by
    refine squeeze_zero_norm' (Eventually.of_forall fun M => ?_)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa [abs_of_pos (by positivity : (0 : ℝ) < (M : ℝ) + 1)] using
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ))
        (b := 1 / ((M : ℝ) + 1)) (fun x _ => hbd x)
  have hsum : Tendsto (fun _ : ℕ => ∫ x in (0 : ℝ)..1, f x) atTop (nhds (0 + L)) :=
    (hzero.add hlim).congr' (Eventually.of_forall fun M =>
      intervalIntegral.integral_add_adjacent_intervals (hf 0 _) (hf _ 1))
  simpa using tendsto_nhds_unique tendsto_const_nhds hsum

private lemma recipFract_ae_on_unit {n : ℕ} (hn : 1 ≤ n) (g : ℝ → ℝ) :
    (∫ x in (1 / ((n : ℝ) + 1))..(1 / (n : ℝ)), g (recipFract x)) =
      ∫ x in (1 / ((n : ℝ) + 1))..(1 / (n : ℝ)), g (1 / x - (n : ℝ)) := by
  have hle := one_div_le_one_div_of_le (Nat.cast_pos.mpr hn) (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)
  rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => congrArg g ?_
  have hxp : 0 < x := lt_trans (by positivity) hx.1
  have hfl : ⌊1 / x⌋ = (n : ℤ) := Int.floor_eq_iff.mpr
    ⟨by exact_mod_cast ((lt_one_div hxp (Nat.cast_pos.mpr hn)).mp hx.2).le,
     by exact_mod_cast (one_div_lt (by positivity) hxp).mp hx.1⟩
  rw [recipFract, Int.fract, hfl]; simp

private lemma continuousOn_inv_sub_pow {n : ℕ} (hn : 1 ≤ n) (p : ℕ) :
    ContinuousOn (fun x : ℝ => (1 / x - (n : ℝ)) ^ p)
      (uIcc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) := fun _ hx =>
  (((continuousAt_const.div continuousAt_id (lt_of_lt_of_le (by positivity) (uIcc_of_le
    (one_div_le_one_div_of_le (Nat.cast_pos.mpr hn) (by linarith : (n : ℝ) ≤ n + 1)) ▸
      hx).1).ne').sub continuousAt_const).pow p).continuousWithinAt

private lemma continuousOn_one_div_mul_pow {k : ℕ} (hk : 1 ≤ k) (p : ℕ) :
    ContinuousOn (fun x : ℝ => (1 / ((k : ℝ) * x)) ^ p) (uIcc (1 / (k : ℝ)) 1) := by
  have hkp : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hle : (1 : ℝ) / (k : ℝ) ≤ 1 := div_le_one_of_le₀ (Nat.one_le_cast.mpr hk) hkp.le
  exact fun _ hx => ((continuousAt_const.div (continuousAt_const.mul continuousAt_id)
    (mul_ne_zero hkp.ne' (lt_of_lt_of_le (div_pos one_pos hkp) (Set.uIcc_of_le hle ▸
      hx).1).ne')).pow p).continuousWithinAt

private lemma harmonic_succ_sub_one (M : ℕ) :
    ∑ n ∈ Ico 1 (M + 1), (1 : ℝ) / ((n : ℝ) + 1) = (harmonic (M + 1) : ℝ) - 1 := by
  induction M with | zero => simp [harmonic_succ, harmonic_zero] | succ k ih =>
    rw [sum_Ico_succ_top (Nat.succ_pos k), ih, harmonic_succ (k + 1), Rat.cast_add]
    push_cast; ring

private lemma tendsto_eulerMascheroniSeq_succ :
    Tendsto (fun M : ℕ => (harmonic (M + 1) : ℝ) - Real.log ((M + 1 : ℕ) : ℝ))
      atTop (nhds Real.eulerMascheroniConstant) :=
  (Real.tendsto_eulerMascheroniSeq'.comp (tendsto_add_atTop_nat 1)).congr'
    (Eventually.of_forall fun _ => by simp only [Function.comp_def,
      Real.eulerMascheroniSeq', Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte])

private lemma intervalIntegral_recipFractScaled_split (p : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    (∫ x in (0 : ℝ)..1, recipFractScaled k x ^ p) =
      (∫ y in (0 : ℝ)..1, recipFract y ^ p) / (k : ℝ) +
        ∫ x in (1 / (k : ℝ))..1, (1 / ((k : ℝ) * x)) ^ p := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hp := intervalIntegrable_recipFractScaled_pow p k
  have hc := intervalIntegral.integral_comp_mul_left (fun y => recipFract y ^ p)
    hk_pos.ne' (a := 0) (b := 1 / (k : ℝ))
  rw [mul_zero, mul_one_div_cancel hk_pos.ne'] at hc
  have h_hi : (∫ x in (1 / (k : ℝ))..1, recipFractScaled k x ^ p) =
      ∫ x in (1 / (k : ℝ))..1, (1 / ((k : ℝ) * x)) ^ p :=
    intervalIntegral.integral_congr_ae (ae_of_all _ fun x hx => by
      rw [uIoc_of_le (div_le_one_of_le₀ (Nat.one_le_cast.mpr hk) hk_pos.le)] at hx
      have hkx : 1 < (k : ℝ) * x := by
        have h1 := mul_lt_mul_of_pos_left hx.1 hk_pos; rwa [mul_one_div_cancel hk_pos.ne'] at h1
      rw [recipFractScaled, Int.fract_eq_self.mpr ⟨by positivity,
        (div_lt_one (by positivity)).mpr hkx⟩])
  rw [← intervalIntegral.integral_add_adjacent_intervals (hp 0 _) (hp _ 1), h_hi,
    show (fun x => recipFractScaled k x ^ p) = fun x => recipFract ((k : ℝ) * x) ^ p from rfl,
    hc, smul_eq_mul, inv_mul_eq_div]

/-- Exact value of the unscaled base integral `∫₀¹ {1/x} dx = 1 - γ`. -/
theorem intervalIntegral_recipFract_zero_to_one :
    (∫ x in (0 : ℝ)..1, recipFract x) = 1 - Real.eulerMascheroniConstant := by
  have hrf : ∀ a b, IntervalIntegrable recipFract volume a b := fun a b => by
    convert intervalIntegrable_recipFractScaled_pow 1 1 a b using 2 with x
    simp [recipFract, recipFractScaled]
  refine intervalIntegral_zero_to_one_of_tendsto hrf (fun x => by
      rw [recipFract, Real.norm_of_nonneg (Int.fract_nonneg _)]; exact (Int.fract_lt_one _).le) ?_
  have hunit : ∀ n : ℕ, 1 ≤ n → (∫ x in (1 / ((n : ℝ) + 1))..(1 / (n : ℝ)), recipFract x) =
      Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) - 1 / ((n : ℝ) + 1) := fun n hn => by
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hle := one_div_le_one_div_of_le hn_pos (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)
    have hd : ∀ x ∈ uIcc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)), HasDerivAt
        (fun y : ℝ => Real.log y - (n : ℝ) * y) (1 / x - (n : ℝ)) x := fun x hx => by
      convert (Real.hasDerivAt_log (lt_of_lt_of_le (by positivity)
        (uIcc_of_le hle ▸ hx).1).ne').sub ((hasDerivAt_id' x).const_mul (n : ℝ)) using 1
      simp [one_div]
    rw [recipFract_ae_on_unit hn (fun x => x), intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (by simpa [pow_one] using (continuousOn_inv_sub_pow hn 1).intervalIntegrable)]
    simp only [one_div, Real.log_inv]
    field_simp [hn_pos.ne', (by positivity : (n : ℝ) + 1 ≠ 0)]; ring
  refine (tendsto_const_nhds.sub tendsto_eulerMascheroniSeq_succ).congr'
    (Eventually.of_forall fun M => Eq.symm ?_)
  have hs := intervalIntegral_split_recip hrf (M + 1) (Nat.succ_pos M)
  have hlog := sum_Ico_sub (fun n : ℕ => Real.log (n : ℝ)) (Nat.succ_pos M); push_cast at hs hlog ⊢
  rw [hs, sum_congr rfl (fun n hn => hunit n (Finset.mem_Ico.mp hn).1), sum_sub_distrib,
    harmonic_succ_sub_one M, hlog]; simp only [Real.log_one, sub_zero]; ring

/-- Báez-Duarte target projection `∫₀¹ {1/(kx)} dx = (ln k + 1 - γ) / k` for `k ≥ 1`. -/
theorem intervalIntegral_recipFractScaled_eq_bVasyunin {k : ℕ} (hk : 1 ≤ k) :
    (∫ x in (0 : ℝ)..1, recipFractScaled k x) = bVasyunin k Real.eulerMascheroniConstant := by
  have hkp : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hd : ∀ x ∈ uIcc ((1 : ℝ) / (k : ℝ)) (1 : ℝ), HasDerivAt (fun y : ℝ => Real.log y / (k : ℝ))
      ((1 : ℝ) / ((k : ℝ) * x)) x := fun _ hx => by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using (Real.hasDerivAt_log
      (lt_of_lt_of_le (div_pos one_pos hkp) (Set.uIcc_of_le (div_le_one_of_le₀ (Nat.one_le_cast.mpr
        hk) hkp.le) ▸ hx).1).ne').div_const (k : ℝ)
  have hsp := intervalIntegral_recipFractScaled_split 1 hk; simp only [pow_one] at hsp
  rw [hsp, intervalIntegral_recipFract_zero_to_one, intervalIntegral.integral_eq_sub_of_hasDerivAt
    hd (by simpa [pow_one] using (continuousOn_one_div_mul_pow hk 1).intervalIntegrable),
    Real.log_one, zero_div, zero_sub, one_div, Real.log_inv, bVasyunin]; ring

/-- Exact value of the unscaled quadratic integral `∫₀¹ {1/x}² dx = ln(2π) - γ - 1`. -/
theorem intervalIntegral_sq_recipFract_zero_to_one :
    (∫ x in (0 : ℝ)..1, recipFract x ^ 2) =
      Real.log (2 * Real.pi) - Real.eulerMascheroniConstant - 1 := by
  have hrf2 : ∀ a b, IntervalIntegrable (fun x => recipFract x ^ 2) volume a b := fun a b => by
    simpa [recipFract, recipFractScaled, one_mul] using
      intervalIntegrable_recipFractScaled_pow 2 1 a b
  refine intervalIntegral_zero_to_one_of_tendsto hrf2 (fun x => by
      rw [recipFract, Real.norm_of_nonneg (sq_nonneg _)]
      nlinarith [Int.fract_nonneg (1 / x), Int.fract_lt_one (1 / x)]) ?_
  have hlogsum : ∀ M : ℕ, 1 ≤ M → ∑ n ∈ Ico 1 M, (n : ℝ) *
      (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) =
        (M : ℝ) * Real.log (M : ℝ) - Real.log ((Nat.factorial M : ℕ) : ℝ) := fun M hM => by
    induction M, hM using Nat.le_induction with | base => simp | succ k hk ih =>
      rw [sum_Ico_succ_top hk, ih, Nat.factorial_succ, Nat.cast_mul, Real.log_mul
        (Nat.cast_ne_zero.mpr k.succ_ne_zero) (Nat.cast_ne_zero.mpr k.factorial_ne_zero),
        Nat.cast_add, Nat.cast_one]; ring
  have hunit : ∀ n : ℕ, 1 ≤ n → (∫ x in (1 / ((n : ℝ) + 1))..(1 / (n : ℝ)), recipFract x ^ 2) =
      2 - 1 / ((n : ℝ) + 1) -
        2 * ((n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ))) := fun n hn => by
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hle := one_div_le_one_div_of_le hn_pos (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)
    have hd : ∀ x ∈ uIcc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)),
        HasDerivAt (fun y : ℝ => -y⁻¹ - 2 * (n : ℝ) * Real.log y + (n : ℝ) ^ 2 * y)
          ((1 / x - (n : ℝ)) ^ 2) x := fun x hx => by
      have hxp := lt_of_lt_of_le (by positivity) (uIcc_of_le hle ▸ hx).1
      convert (((hasDerivAt_inv hxp.ne').neg).sub
        ((Real.hasDerivAt_log hxp.ne').const_mul (2 * (n : ℝ)))).add
        ((hasDerivAt_id' x).const_mul ((n : ℝ) ^ 2)) using 1; field_simp [hxp.ne']; ring
    rw [recipFract_ae_on_unit hn (· ^ 2), intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (continuousOn_inv_sub_pow hn 2).intervalIntegrable]
    simp only [one_div, inv_inv, Real.log_inv]
    field_simp [hn_pos.ne', (by positivity : (n : ℝ) + 1 ≠ 0)]; ring
  have h_st : Tendsto (fun M : ℕ => Real.log ((Nat.factorial (M + 1) : ℕ) : ℝ) -
      ((M + 1 : ℕ) : ℝ) * Real.log ((M + 1 : ℕ) : ℝ) + ((M + 1 : ℕ) : ℝ) -
      (1 / 2 : ℝ) * Real.log ((M + 1 : ℕ) : ℝ))
      atTop (nhds ((1 / 2 : ℝ) * Real.log (2 * Real.pi))) := by
    rw [← show Real.log √Real.pi + (1 / 2 : ℝ) * Real.log 2 = (1 / 2 : ℝ) * Real.log (2 * Real.pi)
      by rw [Real.sqrt_eq_rpow, Real.log_rpow Real.pi_pos, Real.log_mul (by norm_num)
        Real.pi_pos.ne']; ring]
    refine (((Real.continuousAt_log (Real.sqrt_pos.mpr Real.pi_pos).ne').tendsto.comp
      Stirling.tendsto_stirlingSeq_sqrt_pi).comp (tendsto_add_atTop_nat 1) |>.add
      tendsto_const_nhds).congr' (Eventually.of_forall fun M => ?_)
    have hM1 : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
    dsimp [Function.comp_def, Stirling.stirlingSeq]
    rw [Real.log_div (Nat.cast_pos.mpr (M + 1).factorial_pos).ne' (by positivity),
      Real.log_mul (Real.sqrt_pos.mpr (by positivity)).ne' (by positivity), Real.log_pow,
      Real.log_div hM1.ne' (Real.exp_pos 1).ne', Real.log_exp, Real.sqrt_eq_rpow, Real.log_rpow
        (by positivity : 0 < 2 * ((M + 1 : ℕ) : ℝ)), Real.log_mul (by norm_num) hM1.ne']
    push_cast; ring
  refine (show Tendsto _ atTop (nhds (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant - 1))
    from by have h2 := ((h_st.const_mul 2).sub tendsto_eulerMascheroniSeq_succ).sub
              (tendsto_const_nhds (x := (1 : ℝ)))
            rwa [show 2 * ((1 / 2 : ℝ) * Real.log (2 * Real.pi)) - Real.eulerMascheroniConstant -
              1 = Real.log (2 * Real.pi) - Real.eulerMascheroniConstant - 1 by ring] at h2).congr'
    (Eventually.of_forall fun M => Eq.symm ?_)
  have hs := intervalIntegral_split_recip hrf2 (M + 1) (Nat.succ_pos M); push_cast at hs ⊢
  rw [hs, sum_congr rfl (fun n hn => hunit n (Finset.mem_Ico.mp hn).1), sum_sub_distrib,
    sum_sub_distrib, sum_const, Nat.card_Ico, nsmul_eq_mul, harmonic_succ_sub_one M, ← mul_sum,
    hlogsum (M + 1) (Nat.succ_pos M), Nat.add_sub_cancel]; push_cast; ring

/-- Exact diagonal integral `∫₀¹ {1 / (k x)}² dx = (ln(2π) - γ - 1 / k) / k` for `k ≥ 1`. -/
theorem intervalIntegral_sq_recipFractScaled_zero_to_one {k : ℕ} (hk : 1 ≤ k) :
    (∫ x in (0 : ℝ)..1, (recipFractScaled k x) ^ 2) =
      (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant - 1 / (k : ℝ)) / (k : ℝ) := by
  have hkp : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hd : ∀ x ∈ uIcc ((1 : ℝ) / (k : ℝ)) (1 : ℝ), HasDerivAt (fun y : ℝ =>
      -(1 : ℝ) / (k : ℝ) ^ 2 * y⁻¹) (((1 : ℝ) / ((k : ℝ) * x)) ^ 2) x := fun _ hx => by
    convert (hasDerivAt_inv (lt_of_lt_of_le (div_pos one_pos hkp) (uIcc_of_le (div_le_one_of_le₀
      (Nat.one_le_cast.mpr hk) hkp.le) ▸ hx).1).ne').const_mul (-(1 : ℝ) / (k : ℝ) ^ 2) using 1
    field_simp [hkp.ne']
  rw [intervalIntegral_recipFractScaled_split 2 hk, intervalIntegral_sq_recipFract_zero_to_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd (continuousOn_one_div_mul_pow hk
      2).intervalIntegrable]; field_simp [hkp.ne']; ring
