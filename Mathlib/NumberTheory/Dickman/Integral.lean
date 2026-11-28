/-
Copyright (c) 2026 Krishnan Adaikkappan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krishnan Adaikkappan
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.NumberTheory.Dickman.Basic
public import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
# The Dickman function: decay and the integral `∫₀^∞ ρ = exp γ`

This file continues `Mathlib.NumberTheory.Dickman.Basic`. It proves the exponential decay bound
`ρ u ≤ 4 * exp (-log 2 * u)` for `u ≥ 0`, hence integrability of `ρ` on `(0, ∞)`, and the value
of the integral:

* `Real.dickmanRho_le_exp`: the decay bound.
* `Real.integrableOn_dickmanRho_Ioi`: `ρ` is integrable on `(0, ∞)`.
* `Real.integral_dickmanRho_Ioi`: `∫ u in (0, ∞), ρ u = exp γ`, where `γ` is the
  Euler–Mascheroni constant.

The proof uses the Laplace transform `s ↦ ∫ e^{-su} ρ(u) du`, the integral form of `γ`
(`Real.tendsto_integral_one_sub_exp_div_sub_log_atTop`, from `GammaDeriv`), and dominated
convergence.
-/

public section

open Set intervalIntegral MeasureTheory Filter Topology

namespace Real

/-- For `u ≥ 2`: `u ρ(u) ≤ ρ(u - 1)`, from the integral identity and antitonicity. -/
theorem mul_dickmanRho_le {u : ℝ} (hu : 2 ≤ u) : u * dickmanRho u ≤ dickmanRho (u - 1) := by
  rw [mul_dickmanRho_eq_integral (by linarith)]
  have hmono : (∫ t in (u - 1)..u, dickmanRho t) ≤
      ∫ t in (u - 1)..u, dickmanRho (u - 1) := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (dickmanRho_continuous.intervalIntegrable _ _)
    · exact intervalIntegrable_const
    · intro x hx
      exact dickmanRho_antitoneOn_Ici_one (show u - 1 ∈ Ici (1 : ℝ) by
          simp only [mem_Ici]; linarith)
        (show x ∈ Ici (1 : ℝ) by simp only [mem_Ici]; linarith [hx.1]) hx.1
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  linarith

/-- Induction step for the exponential bound on `[0, n)`. -/
private lemma dickmanRho_le_exp_aux :
    ∀ n : ℕ, 2 ≤ n → ∀ u : ℝ, 0 ≤ u → u < (n : ℝ) →
      dickmanRho u ≤ 4 * Real.exp (-Real.log 2 * u) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro u hu0 hu2
    have hE : 0 < Real.exp (Real.log 2 * u) := Real.exp_pos _
    have hlog4 : Real.log 2 * u ≤ Real.log 4 := by
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      rw [this]
      have hl : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
      push_cast at hu2
      nlinarith
    have hexp4 : Real.exp (Real.log 2 * u) ≤ 4 := by
      calc Real.exp (Real.log 2 * u) ≤ Real.exp (Real.log 4) := Real.exp_le_exp.mpr hlog4
        _ = 4 := Real.exp_log (by norm_num)
    have hneg : Real.exp (-Real.log 2 * u) = (Real.exp (Real.log 2 * u))⁻¹ := by
      rw [neg_mul, Real.exp_neg]
    have hone : (1 : ℝ) ≤ 4 * Real.exp (-Real.log 2 * u) := by
      rw [hneg, ← div_eq_mul_inv, le_div_iff₀ hE]
      linarith
    exact (dickmanRho_le_one u).trans hone
  | succ n hn ih =>
    intro u hu0 hu
    by_cases hlt : u < (n : ℝ)
    · exact ih u hu0 hlt
    · have hu2 : (2 : ℝ) ≤ u := by
        have : (2 : ℝ) ≤ n := by exact_mod_cast hn
        linarith [not_lt.mp hlt]
      have hB := mul_dickmanRho_le hu2
      have hI := ih (u - 1) (by linarith) (by push_cast at hu; linarith)
      have hE : 0 < Real.exp (-Real.log 2 * u) := Real.exp_pos _
      have hshift : Real.exp (-Real.log 2 * (u - 1)) = 2 * Real.exp (-Real.log 2 * u) := by
        have : -Real.log 2 * (u - 1) = -Real.log 2 * u + Real.log 2 := by ring
        rw [this, Real.exp_add, Real.exp_log (by norm_num)]
        ring
      rw [hshift] at hI
      have h8 : u * dickmanRho u ≤ 8 * Real.exp (-Real.log 2 * u) := by linarith
      nlinarith

/-- The exponential bound `ρ(u) ≤ 4 · 2^{-u}` on `[0, ∞)`. -/
theorem dickmanRho_le_exp {u : ℝ} (hu : 0 ≤ u) :
    dickmanRho u ≤ 4 * Real.exp (-Real.log 2 * u) := by
  obtain ⟨n, hn⟩ := exists_nat_gt u
  exact dickmanRho_le_exp_aux (n + 2) (by omega) u hu (by push_cast; linarith)

/-- The Dickman function is integrable on `(0, ∞)`. -/
theorem integrableOn_dickmanRho_Ioi : IntegrableOn dickmanRho (Ioi 0) := by
  have hg : IntegrableOn (fun x : ℝ => 4 * Real.exp (-Real.log 2 * x)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (Real.log_pos one_lt_two)).const_mul 4
  refine Integrable.mono' hg dickmanRho_continuous.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (dickmanRho_pos x)]
  exact dickmanRho_le_exp (le_of_lt hx)

/-! ### The primitive `G(v) = ∫₀^{max v 0} ρ` and the Laplace transform -/

/-- The primitive of `ρ` extended by `0` to negative arguments. -/
private noncomputable def dickmanPrim (v : ℝ) : ℝ := ∫ t in (0 : ℝ)..max v 0, dickmanRho t

private lemma dickmanPrim_of_nonpos {v : ℝ} (hv : v ≤ 0) : dickmanPrim v = 0 := by
  simp [dickmanPrim, max_eq_right hv]

private lemma dickmanPrim_of_nonneg {v : ℝ} (hv : 0 ≤ v) :
    dickmanPrim v = ∫ t in (0 : ℝ)..v, dickmanRho t := by
  simp [dickmanPrim, max_eq_left hv]

private lemma dickmanPrim_nonneg (v : ℝ) : 0 ≤ dickmanPrim v := by
  apply intervalIntegral.integral_nonneg (le_max_right v 0)
  intro t ht
  exact (dickmanRho_pos t).le

private lemma dickmanPrim_le (v : ℝ) : dickmanPrim v ≤ max v 0 := by
  have h := intervalIntegral.integral_mono_on (a := 0) (b := max v 0) (le_max_right v 0)
    (dickmanRho_continuous.intervalIntegrable _ _)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume
      0 (max v 0))
    (fun t _ => dickmanRho_le_one t)
  simpa [dickmanPrim] using h

private lemma continuous_dickmanPrim : Continuous dickmanPrim := by
  have hc' := continuous_primitive (μ := MeasureTheory.volume)
    (fun a b => dickmanRho_continuous.intervalIntegrable a b) 0
  exact hc'.comp (continuous_id.max continuous_const)

/-- The pointwise identity `u ρ(u) = G(u) - G(u - 1)` for `u > 0`. -/
private lemma mul_dickmanRho_eq_dickmanPrim_sub {u : ℝ} (hu : 0 < u) :
    u * dickmanRho u = dickmanPrim u - dickmanPrim (u - 1) := by
  rcases le_or_gt 1 u with h1 | h1
  · rw [dickmanPrim_of_nonneg hu.le, dickmanPrim_of_nonneg (by linarith : (0 : ℝ) ≤ u - 1),
      mul_dickmanRho_eq_integral h1, ← intervalIntegral.integral_interval_sub_left
        (dickmanRho_continuous.intervalIntegrable _ _)
        (dickmanRho_continuous.intervalIntegrable _ _)]
  · rw [dickmanPrim_of_nonpos (by linarith : u - 1 ≤ 0), sub_zero, dickmanPrim_of_nonneg hu.le,
      intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))]
    · simp [dickmanRho_of_le_one h1.le]
    · intro t ht
      rw [Set.uIcc_of_le hu.le] at ht
      exact dickmanRho_of_le_one (by linarith [ht.2])

/-- The Laplace transform of `ρ` on `(0, ∞)`. -/
noncomputable def dickmanLaplace (s : ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), exp (-s * u) * dickmanRho u

private lemma tendsto_mul_exp_neg_atTop {s : ℝ} (hs : 0 < s) :
    Tendsto (fun x : ℝ => x * exp (-s * x)) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    (tendsto_id.const_mul_atTop hs)
  have h' : Tendsto (fun x : ℝ => (1 / s) * ((s * x) ^ 1 * exp (-(s * x)))) atTop (𝓝 0) := by
    simpa using h.const_mul (1 / s)
  refine h'.congr' ?_
  filter_upwards with x
  field_simp

private lemma integrableOn_mul_exp_neg {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun x : ℝ => x * exp (-s * x)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := s)
    (by norm_num) one_pos hs
  simpa [Real.rpow_one] using h

private lemma integrableOn_exp_mul_dickmanRho {s : ℝ} (hs : 0 ≤ s) :
    IntegrableOn (fun u : ℝ => exp (-s * u) * dickmanRho u) (Ioi 0) := by
  refine Integrable.mono' integrableOn_dickmanRho_Ioi
    (((by fun_prop : Continuous fun u : ℝ => exp (-s * u)).aestronglyMeasurable).mul
      dickmanRho_continuous.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : (0 : ℝ) < x := hx
  have he : exp (-s * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (exp_pos _).le (dickmanRho_pos x).le)]
  exact mul_le_of_le_one_left (dickmanRho_pos x).le he

private lemma hasDerivAt_dickmanPrim {x : ℝ} (hx : 0 < x) :
    HasDerivAt dickmanPrim (dickmanRho x) x := by
  have hloc : dickmanPrim =ᶠ[nhds x] fun v => ∫ t in (0 : ℝ)..v, dickmanRho t := by
    filter_upwards [Ioi_mem_nhds hx] with v hv
    exact dickmanPrim_of_nonneg (le_of_lt hv)
  exact ((dickmanRho_continuous.integral_hasStrictDerivAt 0 x).hasDerivAt).congr_of_eventuallyEq
    hloc

private lemma integrableOn_exp_mul_dickmanPrim {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun x : ℝ => exp (-s * x) * dickmanPrim x) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_mul_exp_neg hs)
    (((by fun_prop : Continuous fun x : ℝ => exp (-s * x)).aestronglyMeasurable).mul
      continuous_dickmanPrim.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : (0 : ℝ) < x := hx
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (exp_pos _).le (dickmanPrim_nonneg x))]
  have hGx : dickmanPrim x ≤ x := by
    have := dickmanPrim_le x
    rwa [max_eq_left hx0.le] at this
  have := mul_le_mul_of_nonneg_left hGx (exp_pos (-s * x)).le
  linarith

/-- Integration by parts: `∫₀^∞ e^{-su} G(u) du = L(s) / s` for `s > 0`. -/
private lemma integral_exp_mul_dickmanPrim {s : ℝ} (hs : 0 < s) :
    ∫ u in Ioi (0 : ℝ), exp (-s * u) * dickmanPrim u = dickmanLaplace s / s := by
  set f : ℝ → ℝ := fun x => -(exp (-s * x) * dickmanPrim x) / s with hf
  set f' : ℝ → ℝ := fun x => exp (-s * x) * dickmanPrim x - exp (-s * x) * dickmanRho x / s
    with hf'
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt f (f' x) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hG := hasDerivAt_dickmanPrim hx0
    have he : HasDerivAt (fun y : ℝ => exp (-s * y)) (exp (-s * x) * (-s)) x := by
      have := ((hasDerivAt_id x).const_mul (-s)).exp
      simpa [mul_comm] using this
    have hprod := (he.mul hG).neg.div_const s
    convert hprod using 1
    simp only [hf']
    field_simp
    ring
  have hcont : ContinuousWithinAt f (Ici 0) 0 := by
    have hc : Continuous f := by
      apply Continuous.div_const
      apply Continuous.neg
      exact (by fun_prop : Continuous fun x : ℝ => exp (-s * x)).mul continuous_dickmanPrim
    exact hc.continuousWithinAt
  have hr := integrableOn_exp_mul_dickmanRho hs.le
  have hG := integrableOn_exp_mul_dickmanPrim hs
  have hf'int : IntegrableOn f' (Ioi 0) := hG.sub (hr.div_const s)
  have hlim : Tendsto f atTop (𝓝 0) := by
    have hz : Tendsto (fun x : ℝ => x * exp (-s * x) / s) atTop (𝓝 0) := by
      simpa using (tendsto_mul_exp_neg_atTop hs).div_const s
    refine squeeze_zero_norm' ?_ hz
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hGx : 0 ≤ dickmanPrim x := dickmanPrim_nonneg x
    have hGx' : dickmanPrim x ≤ x := by
      have := dickmanPrim_le x
      rwa [max_eq_left hx.le] at this
    rw [hf, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hs,
      abs_of_nonneg (mul_nonneg (exp_pos _).le hGx)]
    apply div_le_div_of_nonneg_right _ hs.le
    have := mul_le_mul_of_nonneg_left hGx' (exp_pos (-s * x)).le
    linarith
  have key := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hf'int hlim
  have hf0 : f 0 = 0 := by simp [hf, dickmanPrim_of_nonpos le_rfl]
  have hsplit : ∫ x in Ioi (0 : ℝ), f' x =
      (∫ x in Ioi (0 : ℝ), exp (-s * x) * dickmanPrim x) -
        (∫ x in Ioi (0 : ℝ), exp (-s * x) * dickmanRho x) / s := by
    simp only [hf']
    rw [integral_sub hG (hr.div_const s), MeasureTheory.integral_div]
  rw [hf0, sub_zero, hsplit] at key
  simp only [dickmanLaplace]
  linarith

private lemma integrableOn_exp_mul_dickmanPrim_sub_one {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun u : ℝ => exp (-s * u) * dickmanPrim (u - 1)) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_mul_exp_neg hs)
    (((by fun_prop : Continuous fun u : ℝ => exp (-s * u)).aestronglyMeasurable).mul
      (continuous_dickmanPrim.comp (continuous_id.sub continuous_const)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : (0 : ℝ) < x := hx
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (exp_pos _).le (dickmanPrim_nonneg _))]
  have hG : dickmanPrim (x - 1) ≤ x := by
    have := dickmanPrim_le (x - 1)
    have hm : max (x - 1) 0 ≤ x := max_le (by linarith) hx0.le
    linarith
  have := mul_le_mul_of_nonneg_left hG (exp_pos (-s * x)).le
  linarith

/-- The shift identity `∫₀^∞ e^{-su} G(u - 1) du = e^{-s} ∫₀^∞ e^{-su} G(u) du`. -/
private lemma shift_dickmanPrim {s : ℝ} :
    ∫ u in Ioi (0 : ℝ), exp (-s * u) * dickmanPrim (u - 1) =
      exp (-s) * ∫ u in Ioi (0 : ℝ), exp (-s * u) * dickmanPrim u := by
  set φ : ℝ → ℝ := fun u => exp (-s * u) * dickmanPrim (u - 1) with hφ
  set ψ : ℝ → ℝ := fun v => exp (-s * v) * dickmanPrim v with hψ
  have hpt : ∀ v : ℝ, (Ioi (0 : ℝ)).indicator φ (v + 1) =
      exp (-s) * (Ioi (0 : ℝ)).indicator ψ v := by
    intro v
    by_cases hv : 0 < v
    · have hv1 : (0 : ℝ) < v + 1 := by linarith
      simp only [indicator, mem_Ioi, hv, hv1, ite_true, hφ, hψ, add_sub_cancel_right]
      rw [show -s * (v + 1) = -s + -s * v by ring, Real.exp_add]
      ring
    · have hG0 : dickmanPrim v = 0 := dickmanPrim_of_nonpos (not_lt.mp hv)
      simp only [indicator, mem_Ioi, hv, ite_false, hφ, hψ, add_sub_cancel_right, mul_zero]
      split_ifs <;> simp [hG0]
  have h1 : ∫ u in Ioi (0 : ℝ), φ u = ∫ u, (Ioi (0 : ℝ)).indicator φ u := by
    rw [MeasureTheory.integral_indicator measurableSet_Ioi]
  have h2 : ∫ u in Ioi (0 : ℝ), ψ u = ∫ v, (Ioi (0 : ℝ)).indicator ψ v := by
    rw [MeasureTheory.integral_indicator measurableSet_Ioi]
  rw [h1, h2, ← integral_add_right_eq_self (fun u => (Ioi (0 : ℝ)).indicator φ u) (1 : ℝ)]
  simp only [hpt]
  rw [MeasureTheory.integral_const_mul]

/-- The Laplace-side identity `∫₀^∞ u e^{-su} ρ(u) du = (1 - e^{-s}) L(s) / s` for `s > 0`. -/
private lemma integral_mul_exp_mul_dickmanRho {s : ℝ} (hs : 0 < s) :
    ∫ u in Ioi (0 : ℝ), u * exp (-s * u) * dickmanRho u =
      (1 - exp (-s)) * dickmanLaplace s / s := by
  have hpt : EqOn (fun u : ℝ => u * exp (-s * u) * dickmanRho u)
      (fun u => exp (-s * u) * dickmanPrim u - exp (-s * u) * dickmanPrim (u - 1)) (Ioi 0) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    have := mul_dickmanRho_eq_dickmanPrim_sub hu0
    simp only
    linear_combination (exp (-s * u)) * this
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  rw [integral_sub (integrableOn_exp_mul_dickmanPrim hs)
      (integrableOn_exp_mul_dickmanPrim_sub_one hs),
    shift_dickmanPrim, integral_exp_mul_dickmanPrim hs]
  ring

/-- The Laplace transform has derivative `-∫ u e^{-su} ρ(u) du` at every `s > 0`. -/
private lemma hasDerivAt_dickmanLaplace {s : ℝ} (hs : 0 < s) :
    HasDerivAt dickmanLaplace (-∫ u in Ioi (0 : ℝ), u * exp (-s * u) * dickmanRho u) s := by
  set F : ℝ → ℝ → ℝ := fun x u => exp (-x * u) * dickmanRho u with hF
  set F' : ℝ → ℝ → ℝ := fun x u => -(u * exp (-x * u) * dickmanRho u) with hF'
  have hcont : ∀ x : ℝ, Continuous (F x) := fun x =>
    (by fun_prop : Continuous fun u : ℝ => exp (-x * u)).mul dickmanRho_continuous
  have hs2 : (0 : ℝ) < s / 2 := by linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume.restrict (Ioi (0 : ℝ))) (F := F) (F' := F') (x₀ := s)
    (bound := fun u => u * exp (-(s / 2) * u)) (Metric.ball_mem_nhds s hs2)
    (Filter.Eventually.of_forall fun x => (hcont x).aestronglyMeasurable)
    (integrableOn_exp_mul_dickmanRho hs.le)
    (((continuous_id.mul (by fun_prop : Continuous fun u : ℝ => exp (-s * u))).mul
      dickmanRho_continuous).neg.aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      intro x hx
      have hu0 : (0 : ℝ) < u := hu
      have hxs : s / 2 < x := by
        have := Metric.mem_ball.mp hx
        rw [Real.dist_eq, abs_lt] at this
        linarith [this.1]
      have hexp : exp (-x * u) ≤ exp (-(s / 2) * u) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have hr := dickmanRho_pos u
      have hr1 := dickmanRho_le_one u
      rw [hF', Real.norm_eq_abs, abs_neg, abs_of_nonneg (by
        exact mul_nonneg (mul_nonneg hu0.le (exp_pos _).le) hr.le)]
      calc u * exp (-x * u) * dickmanRho u ≤ u * exp (-(s / 2) * u) * 1 := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hexp hu0.le) hr1 hr.le
            exact mul_nonneg hu0.le (exp_pos _).le
        _ = u * exp (-(s / 2) * u) := mul_one _)
    (integrableOn_mul_exp_neg hs2)
    (Filter.Eventually.of_forall fun u x _ => by
      have hlin : HasDerivAt (fun y : ℝ => -y * u) (-u) x := by
        have := (hasDerivAt_id x).neg.mul_const u
        simpa using this
      have h2 := (hlin.exp).mul_const (dickmanRho u)
      exact h2.congr_deriv (by simp only [hF']; ring))
  have hint := key.2
  have hF's : ∫ a, F' s a ∂(MeasureTheory.volume.restrict (Ioi (0 : ℝ))) =
      -∫ u in Ioi (0 : ℝ), u * exp (-s * u) * dickmanRho u := by
    simp only [hF']
    exact MeasureTheory.integral_neg _
  rw [hF's] at hint
  exact hint

/-! ### The Euler-type primitive `E(s) = ∫₀ˢ (1 - e^{-w}) / w dw` -/

private lemma intervalIntegrable_einD {x : ℝ} (hx : 0 ≤ x) :
    IntervalIntegrable (fun w : ℝ => (1 - exp (-w)) / w) MeasureTheory.volume 0 x := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1) (by simp)
    (by fun_prop : Measurable fun w : ℝ => (1 - exp (-w)) / w).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
  have h0 : 0 < w := hw.1
  have hnn : 0 ≤ 1 - exp (-w) := by
    have : exp (-w) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have hle : 1 - exp (-w) ≤ w := by
    have := Real.one_sub_le_exp_neg w
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnn h0.le), div_le_one h0]
  exact hle

private lemma hasDerivAt_einD {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => ∫ w in (0 : ℝ)..y, (1 - exp (-w)) / w) ((1 - exp (-x)) / x) x := by
  have hnum : Continuous fun w : ℝ => 1 - exp (-w) :=
    continuous_const.sub (continuous_exp.comp continuous_neg)
  have hgc : ContinuousOn (fun w : ℝ => (1 - exp (-w)) / w) (Ioi 0) :=
    ContinuousOn.div hnum.continuousOn continuousOn_id (fun w (hw : w ∈ Ioi 0) => hw.ne')
  have hsm := hgc.stronglyMeasurableAtFilter (μ := MeasureTheory.volume) isOpen_Ioi x hx
  have hcont : ContinuousAt (fun w : ℝ => (1 - exp (-w)) / w) x :=
    hgc.continuousAt (Ioi_mem_nhds hx)
  exact intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_einD hx.le) hsm hcont

private lemma tendsto_einD_zero :
    Tendsto (fun y : ℝ => ∫ w in (0 : ℝ)..y, (1 - exp (-w)) / w) (𝓝[>] 0) (𝓝 0) := by
  have hnum : MeasureTheory.IntegrableOn (fun w : ℝ => (1 - exp (-w)) / w) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
      (intervalIntegrable_einD zero_le_one)
  have hc : ContinuousOn (fun y : ℝ => ∫ w in (0 : ℝ)..y, (1 - exp (-w)) / w) (uIcc 0 1) :=
    intervalIntegral.continuousOn_primitive_interval hnum
  have hmem : uIcc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
    rw [uIcc_of_le zero_le_one]; exact Icc_mem_nhdsGT zero_lt_one
  have h := (hc 0 (left_mem_uIcc)).tendsto.mono_left (nhdsWithin_le_of_mem hmem)
  simpa using h

/-- The function `Φ(s) = L(s) · exp(E(s))` has derivative `0` on `(0, ∞)`. -/
private lemma hasDerivAt_dickmanPhi {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun y : ℝ => dickmanLaplace y *
      exp (∫ w in (0 : ℝ)..y, (1 - exp (-w)) / w)) 0 s := by
  have hL := hasDerivAt_dickmanLaplace hs
  have hE := hasDerivAt_einD hs
  have hLF : -∫ u in Ioi (0 : ℝ), u * exp (-s * u) * dickmanRho u =
      -((1 - exp (-s)) * dickmanLaplace s / s) := by
    rw [integral_mul_exp_mul_dickmanRho hs]
  have hexp := hE.exp
  have hprod := hL.mul hexp
  convert hprod using 1
  rw [hLF]
  unfold dickmanLaplace
  field_simp
  ring

/-- `Φ(s) = L(s) · exp(E(s))`. -/
private noncomputable def dickmanPhi (s : ℝ) : ℝ :=
  dickmanLaplace s * exp (∫ w in (0 : ℝ)..s, (1 - exp (-w)) / w)

/-- `Φ` is constant on `(0, ∞)`. -/
private lemma dickmanPhi_eq_of_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    dickmanPhi b = dickmanPhi a := by
  have key := constant_of_has_deriv_right_zero (f := dickmanPhi) (a := a) (b := b)
    (fun y hy =>
      ((hasDerivAt_dickmanPhi (by linarith [hy.1]) :
        HasDerivAt dickmanPhi 0 y)).continuousAt.continuousWithinAt)
    (fun y hy =>
      ((hasDerivAt_dickmanPhi (by linarith [hy.1]) : HasDerivAt dickmanPhi 0 y)).hasDerivWithinAt)
  exact key b ⟨hab, le_rfl⟩

/-- `|s L(s) - 1| ≤ e^{-s}` for `s > 0`, since `ρ = 1` on `[0, 1]` and `0 < ρ ≤ 1`. -/
private lemma abs_mul_dickmanLaplace_sub_one_le {s : ℝ} (hs : 0 < s) :
    |s * dickmanLaplace s - 1| ≤ exp (-s) := by
  have hone : ∫ u in Ioi (0 : ℝ), s * exp (-s * u) = 1 := by
    rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (by linarith : -s < 0) 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp
  have hint1 : IntegrableOn (fun u : ℝ => s * (exp (-s * u) * dickmanRho u)) (Ioi 0) :=
    (integrableOn_exp_mul_dickmanRho hs.le).const_mul s
  have hint2 : IntegrableOn (fun u : ℝ => s * exp (-s * u)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hs).const_mul s
  have hL : s * dickmanLaplace s = ∫ u in Ioi (0 : ℝ), s * (exp (-s * u) * dickmanRho u) := by
    unfold dickmanLaplace
    rw [MeasureTheory.integral_const_mul]
  have hsub : s * dickmanLaplace s - 1 =
      ∫ u in Ioi (0 : ℝ), s * exp (-s * u) * (dickmanRho u - 1) := by
    have e1 : ∫ u in Ioi (0 : ℝ), s * exp (-s * u) * (dickmanRho u - 1) =
        ∫ u in Ioi (0 : ℝ), (s * (exp (-s * u) * dickmanRho u) - s * exp (-s * u)) := by
      congr 1
      ext u
      ring
    rw [e1, MeasureTheory.integral_sub hint1 hint2, ← hL, hone]
  rw [hsub]
  have hbound := MeasureTheory.norm_integral_le_of_norm_le
    (μ := MeasureTheory.volume.restrict (Ioi (0 : ℝ)))
    (f := fun u : ℝ => s * exp (-s * u) * (dickmanRho u - 1))
    (g := (Ioi (1 : ℝ)).indicator (fun u => s * exp (-s * u)))
    (hint2.indicator measurableSet_Ioi) ?_
  · have hI : ∫ u in Ioi (0 : ℝ), (Ioi (1 : ℝ)).indicator (fun u => s * exp (-s * u)) u
        = exp (-s) := by
      rw [MeasureTheory.integral_indicator measurableSet_Ioi,
        Measure.restrict_restrict measurableSet_Ioi]
      rw [show Ioi (1 : ℝ) ∩ Ioi 0 = Ioi 1 by simp, MeasureTheory.integral_const_mul,
        integral_exp_mul_Ioi (by linarith : -s < 0) 1]
      field_simp
    rw [hI] at hbound
    rw [Real.norm_eq_abs] at hbound
    exact hbound
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := hu
    rw [Real.norm_eq_abs]
    by_cases hu1 : u ≤ 1
    · rw [dickmanRho_of_le_one hu1]
      simp only [sub_self, mul_zero, abs_zero]
      exact Set.indicator_nonneg (fun x _ => (mul_pos hs (exp_pos _)).le) u
    · have hu1' : (1 : ℝ) < u := lt_of_not_ge hu1
      rw [Set.indicator_of_mem (show u ∈ Ioi (1 : ℝ) from hu1')]
      have hr := dickmanRho_pos u
      have hr1 := dickmanRho_le_one u
      have hpos : 0 ≤ s * exp (-s * u) := (mul_pos hs (exp_pos _)).le
      rw [show s * exp (-s * u) * (dickmanRho u - 1) = (s * exp (-s * u)) * (dickmanRho u - 1)
        from rfl, abs_mul, abs_of_nonneg hpos]
      apply mul_le_of_le_one_right hpos
      rw [abs_le]
      constructor <;> linarith


/-- `s L(s) → 1` as `s → ∞`. -/
private lemma tendsto_mul_dickmanLaplace_atTop :
    Tendsto (fun s : ℝ => s * dickmanLaplace s) atTop (𝓝 1) := by
  have h : Tendsto (fun s : ℝ => s * dickmanLaplace s - 1) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (Real.tendsto_exp_neg_atTop_nhds_zero)
    filter_upwards [eventually_gt_atTop 0] with s hs
    rw [Real.norm_eq_abs]
    exact abs_mul_dickmanLaplace_sub_one_le hs
  have h2 := h.add (tendsto_const_nhds (x := (1 : ℝ)))
  simpa using h2

/-- The Laplace transform is continuous from the right at `0`, by dominated convergence. -/
private lemma tendsto_dickmanLaplace_nhdsWithin_zero :
    Tendsto dickmanLaplace (𝓝[>] 0) (𝓝 (dickmanLaplace 0)) := by
  unfold dickmanLaplace
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun u : ℝ => dickmanRho u) ?_ ?_ integrableOn_dickmanRho_Ioi ?_
  · exact Filter.Eventually.of_forall fun s =>
      ((by fun_prop : Continuous fun u : ℝ => exp (-s * u)).aestronglyMeasurable).mul
        dickmanRho_continuous.aestronglyMeasurable
  · refine eventually_nhdsWithin_of_forall fun s hs => ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hs0 : (0 : ℝ) ≤ s := le_of_lt hs
    have hu0 : (0 : ℝ) < u := hu
    have he : exp (-s * u) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (exp_pos _).le (dickmanRho_pos u).le)]
    exact mul_le_of_le_one_left (dickmanRho_pos u).le he
  · refine Filter.Eventually.of_forall fun u => ?_
    have hc : Continuous fun s : ℝ => exp (-s * u) * dickmanRho u := by fun_prop
    have h0 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using h0

/-- **Dickman's integral.** `∫₀^∞ ρ(u) du = e^γ`, where `γ` is the Euler–Mascheroni constant. -/
theorem integral_dickmanRho_Ioi :
    ∫ u in Ioi (0 : ℝ), dickmanRho u = Real.exp Real.eulerMascheroniConstant := by
  have hEuler := Real.tendsto_integral_one_sub_exp_div_sub_log_atTop
  have hPhi_top : Tendsto dickmanPhi atTop (𝓝 (Real.exp Real.eulerMascheroniConstant)) := by
    have h := tendsto_mul_dickmanLaplace_atTop.mul
      ((Real.continuous_exp.tendsto _).comp hEuler)
    rw [one_mul] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with s hs
    unfold dickmanPhi
    simp only [Function.comp_apply]
    rw [Real.exp_sub, Real.exp_log hs]
    field_simp
  have hconst : dickmanPhi 1 = Real.exp Real.eulerMascheroniConstant := by
    have h2 : Tendsto dickmanPhi atTop (𝓝 (dickmanPhi 1)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
      exact (dickmanPhi_eq_of_le one_pos hs).symm
    exact tendsto_nhds_unique h2 hPhi_top
  have hE0 : Tendsto (fun s : ℝ => exp (∫ w in (0 : ℝ)..s, (1 - exp (-w)) / w)) (𝓝[>] 0)
      (𝓝 1) := by
    have h : Tendsto (fun s : ℝ => exp (∫ w in (0 : ℝ)..s, (1 - exp (-w)) / w)) (𝓝[>] 0)
        (𝓝 (exp 0)) := (Real.continuous_exp.tendsto 0).comp tendsto_einD_zero
    simpa using h
  have hzero : Tendsto dickmanPhi (𝓝[>] 0) (𝓝 (∫ u in Ioi (0 : ℝ), dickmanRho u)) := by
    have h := (tendsto_dickmanLaplace_nhdsWithin_zero).mul hE0
    rw [mul_one] at h
    have hL0 : dickmanLaplace 0 = ∫ u in Ioi (0 : ℝ), dickmanRho u := by
      simp [dickmanLaplace]
    rw [hL0] at h
    exact h
  have hzero' : Tendsto dickmanPhi (𝓝[>] 0) (𝓝 (Real.exp Real.eulerMascheroniConstant)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with s hs
    have := dickmanPhi_eq_of_le hs.1 hs.2.le
    rw [hconst] at this
    exact this
  exact tendsto_nhds_unique hzero hzero'

end Real

end
