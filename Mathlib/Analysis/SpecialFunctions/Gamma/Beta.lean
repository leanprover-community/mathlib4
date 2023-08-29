/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Analytic.IsolatedZeros

#align_import analysis.special_functions.gamma.beta from "leanprover-community/mathlib"@"a3209ddf94136d36e5e5c624b10b2a347cc9d090"

/-!
# The Beta function, and further properties of the Gamma function

In this file we define the Beta integral, relate Beta and Gamma functions, and prove some
refined properties of the Gamma function using these relations.

## Results on the Beta function

* `Complex.betaIntegral`: the Beta function `Β(u, v)`, where `u`, `v` are complex with positive
  real part.
* `Complex.Gamma_mul_Gamma_eq_betaIntegral`: the formula
  `Gamma u * Gamma v = Gamma (u + v) * betaIntegral u v`.

## Results on the Gamma function

* `Complex.Gamma_ne_zero`: for all `s : ℂ` with `s ∉ {-n : n ∈ ℕ}` we have `Γ s ≠ 0`.
* `Complex.GammaSeq_tendsto_Gamma`: for all `s`, the limit as `n → ∞` of the sequence
  `n ↦ n ^ s * n! / (s * (s + 1) * ... * (s + n))` is `Γ(s)`.
* `Complex.Gamma_mul_Gamma_one_sub`: Euler's reflection formula
  `Gamma s * Gamma (1 - s) = π / sin π s`.
* `Complex.differentiable_one_div_Gamma`: the function `1 / Γ(s)` is differentiable everywhere.
* `Complex.Gamma_mul_Gamma_add_half`: Legendre's duplication formula
  `Gamma s * Gamma (s + 1 / 2) = Gamma (2 * s) * 2 ^ (1 - 2 * s) * sqrt π`.
* `Real.Gamma_ne_zero`, `Real.GammaSeq_tendsto_Gamma`,
  `Real.Gamma_mul_Gamma_one_sub`, `Real.Gamma_mul_Gamma_add_half`: real versions of the above.
-/


noncomputable section

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

set_option linter.uppercaseLean3 false

open Filter intervalIntegral Set Real MeasureTheory

open scoped Nat Topology BigOperators Real

section BetaIntegral

/-! ## The Beta function -/


namespace Complex

notation "cexp" => Complex.exp

/-- The Beta function `Β (u, v)`, defined as `∫ x:ℝ in 0..1, x ^ (u - 1) * (1 - x) ^ (v - 1)`. -/
noncomputable def betaIntegral (u v : ℂ) : ℂ :=
  ∫ x : ℝ in (0)..1, (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1)
#align complex.beta_integral Complex.betaIntegral

/-- Auxiliary lemma for `betaIntegral_convergent`, showing convergence at the left endpoint. -/
theorem betaIntegral_convergent_left {u : ℂ} (hu : 0 < re u) (v : ℂ) :
    IntervalIntegrable (fun x =>
      (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1) : ℝ → ℂ) volume 0 (1 / 2) := by
  apply IntervalIntegrable.mul_continuousOn
  -- ⊢ IntervalIntegrable (fun x => ↑x ^ (u - 1)) volume 0 (1 / 2)
  · refine' intervalIntegral.intervalIntegrable_cpow' _
    -- ⊢ -1 < (u - 1).re
    rwa [sub_re, one_re, ← zero_sub, sub_lt_sub_iff_right]
    -- 🎉 no goals
  · apply ContinuousAt.continuousOn
    -- ⊢ ∀ (x : ℝ), x ∈ uIcc 0 (1 / 2) → ContinuousAt (fun x => (1 - ↑x) ^ (v - 1)) x
    intro x hx
    -- ⊢ ContinuousAt (fun x => (1 - ↑x) ^ (v - 1)) x
    rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ 1 / 2)] at hx
    -- ⊢ ContinuousAt (fun x => (1 - ↑x) ^ (v - 1)) x
    apply ContinuousAt.cpow
    · exact (continuous_const.sub continuous_ofReal).continuousAt
      -- 🎉 no goals
    · exact continuousAt_const
      -- 🎉 no goals
    · rw [sub_re, one_re, ofReal_re, sub_pos]
      -- ⊢ x < 1 ∨ (1 - ↑x).im ≠ 0
      exact Or.inl (hx.2.trans_lt (by norm_num : (1 / 2 : ℝ) < 1))
      -- 🎉 no goals
#align complex.beta_integral_convergent_left Complex.betaIntegral_convergent_left

/-- The Beta integral is convergent for all `u, v` of positive real part. -/
theorem betaIntegral_convergent {u v : ℂ} (hu : 0 < re u) (hv : 0 < re v) :
    IntervalIntegrable (fun x =>
      (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1) : ℝ → ℂ) volume 0 1 := by
  refine' (betaIntegral_convergent_left hu v).trans _
  -- ⊢ IntervalIntegrable (fun x => ↑x ^ (u - 1) * (1 - ↑x) ^ (v - 1)) volume (1 /  …
  rw [IntervalIntegrable.iff_comp_neg]
  -- ⊢ IntervalIntegrable (fun x => ↑(-x) ^ (u - 1) * (1 - ↑(-x)) ^ (v - 1)) volume …
  convert ((betaIntegral_convergent_left hv u).comp_add_right 1).symm using 1
  · ext1 x
    -- ⊢ ↑(-x) ^ (u - 1) * (1 - ↑(-x)) ^ (v - 1) = ↑(x + 1) ^ (v - 1) * (1 - ↑(x + 1) …
    conv_lhs => rw [mul_comm]
    -- ⊢ (1 - ↑(-x)) ^ (v - 1) * ↑(-x) ^ (u - 1) = ↑(x + 1) ^ (v - 1) * (1 - ↑(x + 1) …
    congr 2 <;> · push_cast; ring
    -- ⊢ 1 - ↑(-x) = ↑(x + 1)
                  -- ⊢ 1 - -↑x = ↑x + 1
                             -- 🎉 no goals
                  -- ⊢ -↑x = 1 - (↑x + 1)
                             -- 🎉 no goals
  · norm_num
    -- 🎉 no goals
  · norm_num
    -- 🎉 no goals
#align complex.beta_integral_convergent Complex.betaIntegral_convergent

theorem betaIntegral_symm (u v : ℂ) : betaIntegral v u = betaIntegral u v := by
  rw [betaIntegral, betaIntegral]
  -- ⊢ ∫ (x : ℝ) in 0 ..1, ↑x ^ (v - 1) * (1 - ↑x) ^ (u - 1) = ∫ (x : ℝ) in 0 ..1,  …
  have := intervalIntegral.integral_comp_mul_add (a := 0) (b := 1) (c := -1)
    (fun x : ℝ => (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1)) neg_one_lt_zero.ne 1
  rw [inv_neg, inv_one, neg_one_smul, ← intervalIntegral.integral_symm] at this
  -- ⊢ ∫ (x : ℝ) in 0 ..1, ↑x ^ (v - 1) * (1 - ↑x) ^ (u - 1) = ∫ (x : ℝ) in 0 ..1,  …
  simp at this
  -- ⊢ ∫ (x : ℝ) in 0 ..1, ↑x ^ (v - 1) * (1 - ↑x) ^ (u - 1) = ∫ (x : ℝ) in 0 ..1,  …
  conv_lhs at this => arg 1; intro x; rw [add_comm, ← sub_eq_add_neg, mul_comm]
  -- ⊢ ∫ (x : ℝ) in 0 ..1, ↑x ^ (v - 1) * (1 - ↑x) ^ (u - 1) = ∫ (x : ℝ) in 0 ..1,  …
  exact this
  -- 🎉 no goals
#align complex.beta_integral_symm Complex.betaIntegral_symm

theorem betaIntegral_eval_one_right {u : ℂ} (hu : 0 < re u) : betaIntegral u 1 = 1 / u := by
  simp_rw [betaIntegral, sub_self, cpow_zero, mul_one]
  -- ⊢ ∫ (x : ℝ) in 0 ..1, ↑x ^ (u - 1) = 1 / u
  rw [integral_cpow (Or.inl _)]
  -- ⊢ (↑1 ^ (u - 1 + 1) - ↑0 ^ (u - 1 + 1)) / (u - 1 + 1) = 1 / u
  · rw [ofReal_zero, ofReal_one, one_cpow, zero_cpow, sub_zero, sub_add_cancel]
    -- ⊢ u - 1 + 1 ≠ 0
    rw [sub_add_cancel]
    -- ⊢ u ≠ 0
    contrapose! hu; rw [hu, zero_re]
    -- ⊢ u.re ≤ 0
                    -- 🎉 no goals
  · rwa [sub_re, one_re, ← sub_pos, sub_neg_eq_add, sub_add_cancel]
    -- 🎉 no goals
#align complex.beta_integral_eval_one_right Complex.betaIntegral_eval_one_right

theorem betaIntegral_scaled (s t : ℂ) {a : ℝ} (ha : 0 < a) :
    ∫ x in (0)..a, (x : ℂ) ^ (s - 1) * ((a : ℂ) - x) ^ (t - 1) =
    (a : ℂ) ^ (s + t - 1) * betaIntegral s t := by
  have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  -- ⊢ ∫ (x : ℝ) in 0 ..a, ↑x ^ (s - 1) * (↑a - ↑x) ^ (t - 1) = ↑a ^ (s + t - 1) *  …
  rw [betaIntegral]
  -- ⊢ ∫ (x : ℝ) in 0 ..a, ↑x ^ (s - 1) * (↑a - ↑x) ^ (t - 1) = ↑a ^ (s + t - 1) *  …
  have A : (a : ℂ) ^ (s + t - 1) = a * ((a : ℂ) ^ (s - 1) * (a : ℂ) ^ (t - 1)) := by
    rw [(by abel : s + t - 1 = 1 + (s - 1) + (t - 1)), cpow_add _ _ ha', cpow_add 1 _ ha', cpow_one,
      mul_assoc]
  rw [A, mul_assoc, ← intervalIntegral.integral_const_mul, ← real_smul, ← zero_div a, ←
    div_self ha.ne', ← intervalIntegral.integral_comp_div _ ha.ne', zero_div]
  simp_rw [intervalIntegral.integral_of_le ha.le]
  -- ⊢ ∫ (x : ℝ) in Ioc 0 a, ↑x ^ (s - 1) * (↑a - ↑x) ^ (t - 1) = ∫ (x : ℝ) in Ioc  …
  refine' set_integral_congr measurableSet_Ioc fun x hx => _
  -- ⊢ ↑x ^ (s - 1) * (↑a - ↑x) ^ (t - 1) = ↑a ^ (s - 1) * ↑a ^ (t - 1) * (↑(x / a) …
  rw [mul_mul_mul_comm]
  -- ⊢ ↑x ^ (s - 1) * (↑a - ↑x) ^ (t - 1) = ↑a ^ (s - 1) * ↑(x / a) ^ (s - 1) * (↑a …
  congr 1
  -- ⊢ ↑x ^ (s - 1) = ↑a ^ (s - 1) * ↑(x / a) ^ (s - 1)
  · rw [← mul_cpow_ofReal_nonneg ha.le (div_pos hx.1 ha).le, ofReal_div, mul_div_cancel' _ ha']
    -- 🎉 no goals
  · rw [(by norm_cast : (1 : ℂ) - ↑(x / a) = ↑(1 - x / a)), ←
      mul_cpow_ofReal_nonneg ha.le (sub_nonneg.mpr <| (div_le_one ha).mpr hx.2)]
    push_cast
    -- ⊢ (↑a - ↑x) ^ (t - 1) = (↑a * (1 - ↑x / ↑a)) ^ (t - 1)
    rw [mul_sub, mul_one, mul_div_cancel' _ ha']
    -- 🎉 no goals
#align complex.beta_integral_scaled Complex.betaIntegral_scaled

/-- Relation between Beta integral and Gamma function.  -/
theorem Gamma_mul_Gamma_eq_betaIntegral {s t : ℂ} (hs : 0 < re s) (ht : 0 < re t) :
    Gamma s * Gamma t = Gamma (s + t) * betaIntegral s t := by
  -- Note that we haven't proved (yet) that the Gamma function has no zeroes, so we can't formulate
  -- this as a formula for the Beta function.
  have conv_int := integral_posConvolution
    (GammaIntegral_convergent hs) (GammaIntegral_convergent ht) (ContinuousLinearMap.mul ℝ ℂ)
  simp_rw [ContinuousLinearMap.mul_apply'] at conv_int
  -- ⊢ Gamma s * Gamma t = Gamma (s + t) * betaIntegral s t
  have hst : 0 < re (s + t) := by rw [add_re]; exact add_pos hs ht
  -- ⊢ Gamma s * Gamma t = Gamma (s + t) * betaIntegral s t
  rw [Gamma_eq_integral hs, Gamma_eq_integral ht, Gamma_eq_integral hst, GammaIntegral,
    GammaIntegral, GammaIntegral, ← conv_int, ← integral_mul_right (betaIntegral _ _)]
  refine' set_integral_congr measurableSet_Ioi fun x hx => _
  -- ⊢ ∫ (t_1 : ℝ) in 0 ..x, ↑(rexp (-t_1)) * ↑t_1 ^ (s - 1) * (↑(rexp (-(x - t_1)) …
  rw [mul_assoc, ← betaIntegral_scaled s t hx, ← intervalIntegral.integral_const_mul]
  -- ⊢ ∫ (t_1 : ℝ) in 0 ..x, ↑(rexp (-t_1)) * ↑t_1 ^ (s - 1) * (↑(rexp (-(x - t_1)) …
  congr 1 with y : 1
  -- ⊢ ↑(rexp (-y)) * ↑y ^ (s - 1) * (↑(rexp (-(x - y))) * ↑(x - y) ^ (t - 1)) = ↑( …
  push_cast
  -- ⊢ cexp (-↑y) * ↑y ^ (s - 1) * (cexp (-(↑x - ↑y)) * (↑x - ↑y) ^ (t - 1)) = cexp …
  suffices Complex.exp (-x) = Complex.exp (-y) * Complex.exp (-(x - y)) by rw [this]; ring
  -- ⊢ cexp (-↑x) = cexp (-↑y) * cexp (-(↑x - ↑y))
  · rw [← Complex.exp_add]; congr 1; abel
    -- ⊢ cexp (-↑x) = cexp (-↑y + -(↑x - ↑y))
                            -- ⊢ -↑x = -↑y + -(↑x - ↑y)
                                     -- 🎉 no goals
                                     -- 🎉 no goals
#align complex.Gamma_mul_Gamma_eq_beta_integral Complex.Gamma_mul_Gamma_eq_betaIntegral

/-- Recurrence formula for the Beta function. -/
theorem betaIntegral_recurrence {u v : ℂ} (hu : 0 < re u) (hv : 0 < re v) :
    u * betaIntegral u (v + 1) = v * betaIntegral (u + 1) v := by
  -- NB: If we knew `Gamma (u + v + 1) ≠ 0` this would be an easy consequence of
  -- `Gamma_mul_Gamma_eq_betaIntegral`; but we don't know that yet. We will prove it later, but
  -- this lemma is needed in the proof. So we give a (somewhat laborious) direct argument.
  let F : ℝ → ℂ := fun x => (x : ℂ) ^ u * (1 - (x : ℂ)) ^ v
  -- ⊢ u * betaIntegral u (v + 1) = v * betaIntegral (u + 1) v
  have hu' : 0 < re (u + 1) := by rw [add_re, one_re]; positivity
  -- ⊢ u * betaIntegral u (v + 1) = v * betaIntegral (u + 1) v
  have hv' : 0 < re (v + 1) := by rw [add_re, one_re]; positivity
  -- ⊢ u * betaIntegral u (v + 1) = v * betaIntegral (u + 1) v
  have hc : ContinuousOn F (Icc 0 1) := by
    refine' (ContinuousAt.continuousOn fun x hx => _).mul (ContinuousAt.continuousOn fun x hx => _)
    · refine' (continuousAt_cpow_const_of_re_pos (Or.inl _) hu).comp continuous_ofReal.continuousAt
      rw [ofReal_re]; exact hx.1
    · refine' (continuousAt_cpow_const_of_re_pos (Or.inl _) hv).comp
        (continuous_const.sub continuous_ofReal).continuousAt
      rw [sub_re, one_re, ofReal_re, sub_nonneg]
      exact hx.2
  have hder : ∀ x : ℝ, x ∈ Ioo (0 : ℝ) 1 →
      HasDerivAt F (u * ((x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ v) -
        v * ((x : ℂ) ^ u * (1 - (x : ℂ)) ^ (v - 1))) x := by
    intro x hx
    have U : HasDerivAt (fun y : ℂ => y ^ u) (u * (x : ℂ) ^ (u - 1)) ↑x := by
      have := @HasDerivAt.cpow_const _ _ _ u (hasDerivAt_id (x : ℂ)) (Or.inl ?_)
      simp only [id_eq, mul_one] at this
      · exact this
      · rw [id_eq, ofReal_re]; exact hx.1
    have V : HasDerivAt (fun y : ℂ => (1 - y) ^ v) (-v * (1 - (x : ℂ)) ^ (v - 1)) ↑x := by
      have A := @HasDerivAt.cpow_const _ _ _ v (hasDerivAt_id (1 - (x : ℂ))) (Or.inl ?_)
      swap; · rw [id.def, sub_re, one_re, ofReal_re, sub_pos]; exact hx.2
      simp_rw [id.def] at A
      have B : HasDerivAt (fun y : ℂ => 1 - y) (-1) ↑x := by
        apply HasDerivAt.const_sub; apply hasDerivAt_id
      convert HasDerivAt.comp (↑x) A B using 1
      ring
    convert (U.mul V).comp_ofReal using 1
    ring
  have h_int := ((betaIntegral_convergent hu hv').const_mul u).sub
    ((betaIntegral_convergent hu' hv).const_mul v)
  rw [add_sub_cancel, add_sub_cancel] at h_int
  -- ⊢ u * betaIntegral u (v + 1) = v * betaIntegral (u + 1) v
  have int_ev := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hc hder h_int
  -- ⊢ u * betaIntegral u (v + 1) = v * betaIntegral (u + 1) v
  have hF0 : F 0 = 0 := by
    simp only [mul_eq_zero, ofReal_zero, cpow_eq_zero_iff, eq_self_iff_true, Ne.def, true_and_iff,
      sub_zero, one_cpow, one_ne_zero, or_false_iff]
    contrapose! hu; rw [hu, zero_re]
  have hF1 : F 1 = 0 := by
    simp only [mul_eq_zero, ofReal_one, one_cpow, one_ne_zero, sub_self, cpow_eq_zero_iff,
      eq_self_iff_true, Ne.def, true_and_iff, false_or_iff]
    contrapose! hv; rw [hv, zero_re]
  rw [hF0, hF1, sub_zero, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at int_ev
  · rw [betaIntegral, betaIntegral, ← sub_eq_zero]
    -- ⊢ (u * ∫ (x : ℝ) in 0 ..1, ↑x ^ (u - 1) * (1 - ↑x) ^ (v + 1 - 1)) - v * ∫ (x : …
    convert int_ev <;> ring
    -- ⊢ v + 1 - 1 = v
                       -- 🎉 no goals
                       -- 🎉 no goals
  · apply IntervalIntegrable.const_mul
    -- ⊢ IntervalIntegrable (fun x => ↑x ^ (u - 1) * (1 - ↑x) ^ v) volume 0 1
    convert betaIntegral_convergent hu hv'; ring
    -- ⊢ v = v + 1 - 1
                                            -- 🎉 no goals
  · apply IntervalIntegrable.const_mul
    -- ⊢ IntervalIntegrable (fun x => ↑x ^ u * (1 - ↑x) ^ (v - 1)) volume 0 1
    convert betaIntegral_convergent hu' hv; ring
    -- ⊢ u = u + 1 - 1
                                            -- 🎉 no goals
#align complex.beta_integral_recurrence Complex.betaIntegral_recurrence

/-- Explicit formula for the Beta function when second argument is a positive integer. -/
theorem betaIntegral_eval_nat_add_one_right {u : ℂ} (hu : 0 < re u) (n : ℕ) :
    betaIntegral u (n + 1) = n ! / ∏ j : ℕ in Finset.range (n + 1), (u + j) := by
  induction' n with n IH generalizing u
  -- ⊢ betaIntegral u (↑Nat.zero + 1) = ↑Nat.zero ! / ∏ j in Finset.range (Nat.zero …
  · rw [Nat.cast_zero, zero_add, betaIntegral_eval_one_right hu, Nat.factorial_zero, Nat.cast_one]
    -- ⊢ 1 / u = 1 / ∏ j in Finset.range (Nat.zero + 1), (u + ↑j)
    simp
    -- 🎉 no goals
  · have := betaIntegral_recurrence hu (?_ : 0 < re n.succ)
    -- ⊢ betaIntegral u (↑(Nat.succ n) + 1) = ↑(Nat.succ n)! / ∏ j in Finset.range (N …
    swap; · rw [← ofReal_nat_cast, ofReal_re]; positivity
    -- ⊢ 0 < (↑(Nat.succ n)).re
            -- ⊢ 0 < ↑(Nat.succ n)
                                               -- 🎉 no goals
    rw [mul_comm u _, ← eq_div_iff] at this
    -- ⊢ betaIntegral u (↑(Nat.succ n) + 1) = ↑(Nat.succ n)! / ∏ j in Finset.range (N …
    swap; · contrapose! hu; rw [hu, zero_re]
    -- ⊢ u ≠ 0
            -- ⊢ u.re ≤ 0
                            -- 🎉 no goals
    rw [this, Finset.prod_range_succ', Nat.cast_succ, IH]
    -- ⊢ (↑n + 1) * (↑n ! / ∏ j in Finset.range (n + 1), (u + 1 + ↑j)) / u = ↑(Nat.su …
    swap; · rw [add_re, one_re]; positivity
    -- ⊢ 0 < (u + 1).re
            -- ⊢ 0 < u.re + 1
                                 -- 🎉 no goals
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, ←
      mul_div_assoc, ← div_div]
    congr 3 with j : 1
    -- ⊢ u + 1 + ↑j = u + ↑(j + 1)
    push_cast; abel
    -- ⊢ u + 1 + ↑j = u + (↑j + 1)
               -- 🎉 no goals
               -- 🎉 no goals
#align complex.beta_integral_eval_nat_add_one_right Complex.betaIntegral_eval_nat_add_one_right

end Complex

end BetaIntegral

section LimitFormula

/-! ## The Euler limit formula -/


namespace Complex

/-- The sequence with `n`-th term `n ^ s * n! / (s * (s + 1) * ... * (s + n))`, for complex `s`.
We will show that this tends to `Γ(s)` as `n → ∞`. -/
noncomputable def GammaSeq (s : ℂ) (n : ℕ) :=
  (n : ℂ) ^ s * n ! / ∏ j : ℕ in Finset.range (n + 1), (s + j)
#align complex.Gamma_seq Complex.GammaSeq

theorem GammaSeq_eq_betaIntegral_of_re_pos {s : ℂ} (hs : 0 < re s) (n : ℕ) :
    GammaSeq s n = (n : ℂ) ^ s * betaIntegral s (n + 1) := by
  rw [GammaSeq, betaIntegral_eval_nat_add_one_right hs n, ← mul_div_assoc]
  -- 🎉 no goals
#align complex.Gamma_seq_eq_beta_integral_of_re_pos Complex.GammaSeq_eq_betaIntegral_of_re_pos

theorem GammaSeq_add_one_left (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    GammaSeq (s + 1) n / s = n / (n + 1 + s) * GammaSeq s n := by
  conv_lhs => rw [GammaSeq, Finset.prod_range_succ, div_div]
  -- ⊢ ↑n ^ (s + 1) * ↑n ! / ((∏ x in Finset.range n, (s + 1 + ↑x)) * (s + 1 + ↑n)  …
  conv_rhs =>
    rw [GammaSeq, Finset.prod_range_succ', Nat.cast_zero, add_zero, div_mul_div_comm, ← mul_assoc,
      ← mul_assoc, mul_comm _ (Finset.prod _ _)]
  congr 3
  · rw [cpow_add _ _ (Nat.cast_ne_zero.mpr hn), cpow_one, mul_comm]
    -- 🎉 no goals
  · refine' Finset.prod_congr (by rfl) fun x _ => _
    -- ⊢ s + 1 + ↑x = s + ↑(x + 1)
    push_cast; ring
    -- ⊢ s + 1 + ↑x = s + (↑x + 1)
               -- 🎉 no goals
  · abel
    -- 🎉 no goals
    -- 🎉 no goals
#align complex.Gamma_seq_add_one_left Complex.GammaSeq_add_one_left

theorem GammaSeq_eq_approx_Gamma_integral {s : ℂ} (hs : 0 < re s) {n : ℕ} (hn : n ≠ 0) :
    GammaSeq s n = ∫ x : ℝ in (0)..n, ↑((1 - x / n) ^ n) * (x : ℂ) ^ (s - 1) := by
  have : ∀ x : ℝ, x = x / n * n := by intro x; rw [div_mul_cancel]; exact Nat.cast_ne_zero.mpr hn
  -- ⊢ GammaSeq s n = ∫ (x : ℝ) in 0 ..↑n, ↑((1 - x / ↑n) ^ n) * ↑x ^ (s - 1)
  conv_rhs => enter [1, x, 2, 1]; rw [this x]
  -- ⊢ GammaSeq s n = ∫ (x : ℝ) in 0 ..↑n, ↑((1 - x / ↑n) ^ n) * ↑(x / ↑n * ↑n) ^ ( …
  rw [GammaSeq_eq_betaIntegral_of_re_pos hs]
  -- ⊢ ↑n ^ s * betaIntegral s (↑n + 1) = ∫ (x : ℝ) in 0 ..↑n, ↑((1 - x / ↑n) ^ n)  …
  have := intervalIntegral.integral_comp_div (a := 0) (b := n)
    (fun x => ↑((1 - x) ^ n) * ↑(x * ↑n) ^ (s - 1) : ℝ → ℂ) (Nat.cast_ne_zero.mpr hn)
  dsimp only at this
  -- ⊢ ↑n ^ s * betaIntegral s (↑n + 1) = ∫ (x : ℝ) in 0 ..↑n, ↑((1 - x / ↑n) ^ n)  …
  rw [betaIntegral, this, real_smul, zero_div, div_self, add_sub_cancel,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  swap; · exact Nat.cast_ne_zero.mpr hn
  -- ⊢ ↑n ≠ 0
          -- 🎉 no goals
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  -- ⊢ ∫ (x : ℝ) in Ioc 0 1, ↑n ^ s * (↑x ^ (s - 1) * (1 - ↑x) ^ ↑n) = ∫ (x : ℝ) in …
  refine' set_integral_congr measurableSet_Ioc fun x hx => _
  -- ⊢ ↑n ^ s * (↑x ^ (s - 1) * (1 - ↑x) ^ ↑n) = ↑↑n * (↑((1 - x) ^ n) * ↑(x * ↑n)  …
  push_cast
  -- ⊢ ↑n ^ s * (↑x ^ (s - 1) * (1 - ↑x) ^ ↑n) = ↑n * ((1 - ↑x) ^ n * (↑x * ↑n) ^ ( …
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  -- ⊢ ↑n ^ s * (↑x ^ (s - 1) * (1 - ↑x) ^ ↑n) = ↑n * ((1 - ↑x) ^ n * (↑x * ↑n) ^ ( …
  have A : (n : ℂ) ^ s = (n : ℂ) ^ (s - 1) * n := by
    conv_lhs => rw [(by ring : s = s - 1 + 1), cpow_add _ _ hn']
    simp
  have B : ((x : ℂ) * ↑n) ^ (s - 1) = (x : ℂ) ^ (s - 1) * (n : ℂ) ^ (s - 1) := by
    rw [← ofReal_nat_cast,
      mul_cpow_ofReal_nonneg hx.1.le (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)).le]
  rw [A, B, cpow_nat_cast]; ring
  -- ⊢ ↑n ^ (s - 1) * ↑n * (↑x ^ (s - 1) * (1 - ↑x) ^ n) = ↑n * ((1 - ↑x) ^ n * (↑x …
                            -- 🎉 no goals
#align complex.Gamma_seq_eq_approx_Gamma_integral Complex.GammaSeq_eq_approx_Gamma_integral

/-- The main techical lemma for `GammaSeq_tendsto_Gamma`, expressing the integral defining the
Gamma function for `0 < re s` as the limit of a sequence of integrals over finite intervals. -/
theorem approx_Gamma_integral_tendsto_Gamma_integral {s : ℂ} (hs : 0 < re s) :
    Tendsto (fun n : ℕ => ∫ x : ℝ in (0)..n, ↑((1 - x / n) ^ n) * (x : ℂ) ^ (s - 1)) atTop
      (𝓝 <| Gamma s) := by
  rw [Gamma_eq_integral hs]
  -- ⊢ Tendsto (fun n => ∫ (x : ℝ) in 0 ..↑n, ↑((1 - x / ↑n) ^ n) * ↑x ^ (s - 1)) a …
  -- We apply dominated convergence to the following function, which we will show is uniformly
  -- bounded above by the Gamma integrand `exp (-x) * x ^ (re s - 1)`.
  let f : ℕ → ℝ → ℂ := fun n =>
    indicator (Ioc 0 (n : ℝ)) fun x : ℝ => ↑((1 - x / n) ^ n) * (x : ℂ) ^ (s - 1)
  -- integrability of f
  have f_ible : ∀ n : ℕ, Integrable (f n) (volume.restrict (Ioi 0)) := by
    intro n
    rw [integrable_indicator_iff (measurableSet_Ioc : MeasurableSet (Ioc (_ : ℝ) _)), IntegrableOn,
      Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self, ← IntegrableOn, ←
      intervalIntegrable_iff_integrable_Ioc_of_le (by positivity : (0 : ℝ) ≤ n)]
    apply IntervalIntegrable.continuousOn_mul
    · refine' intervalIntegral.intervalIntegrable_cpow' _
      rwa [sub_re, one_re, ← zero_sub, sub_lt_sub_iff_right]
    · apply Continuous.continuousOn
      exact IsROrC.continuous_ofReal.comp -- Porting note: was `continuity`
        ((continuous_const.sub (continuous_id'.div_const ↑n)).pow n)
  -- pointwise limit of f
  have f_tends : ∀ x : ℝ, x ∈ Ioi (0 : ℝ) →
      Tendsto (fun n : ℕ => f n x) atTop (𝓝 <| ↑(Real.exp (-x)) * (x : ℂ) ^ (s - 1)) := by
    intro x hx
    apply Tendsto.congr'
    show ∀ᶠ n : ℕ in atTop, ↑((1 - x / n) ^ n) * (x : ℂ) ^ (s - 1) = f n x
    · refine' Eventually.mp (eventually_ge_atTop ⌈x⌉₊) (eventually_of_forall fun n hn => _)
      rw [Nat.ceil_le] at hn
      dsimp only
      rw [indicator_of_mem]
      exact ⟨hx, hn⟩
    · simp_rw [mul_comm]
      refine' (Tendsto.comp (continuous_ofReal.tendsto _) _).const_mul _
      convert tendsto_one_plus_div_pow_exp (-x) using 1
      ext1 n
      rw [neg_div, ← sub_eq_add_neg]; norm_cast
  -- let `convert` identify the remaining goals
  convert tendsto_integral_of_dominated_convergence _ (fun n => (f_ible n).1)
    (Real.GammaIntegral_convergent hs) _
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ f_tends)) using 1
  -- limit of f is the integrand we want
  · ext1 n
    -- ⊢ ∫ (x : ℝ) in 0 ..↑n, ↑((1 - x / ↑n) ^ n) * ↑x ^ (s - 1) = ∫ (a : ℝ) in Ioi 0 …
    rw [integral_indicator (measurableSet_Ioc : MeasurableSet (Ioc (_ : ℝ) _)),
      intervalIntegral.integral_of_le (by positivity : 0 ≤ (n : ℝ)),
      Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]
  -- f is uniformly bounded by the Gamma integrand
  · intro n
    -- ⊢ ∀ᵐ (a : ℝ) ∂Measure.restrict volume (Ioi 0), ‖f n a‖ ≤ rexp (-a) * a ^ (s.re …
    refine' (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => _)
    -- ⊢ ‖f n x‖ ≤ rexp (-x) * x ^ (s.re - 1)
    dsimp only
    -- ⊢ ‖indicator (Ioc 0 ↑n) (fun x => ↑((1 - x / ↑n) ^ n) * ↑x ^ (s - 1)) x‖ ≤ rex …
    rcases lt_or_le (n : ℝ) x with (hxn | hxn)
    -- ⊢ ‖indicator (Ioc 0 ↑n) (fun x => ↑((1 - x / ↑n) ^ n) * ↑x ^ (s - 1)) x‖ ≤ rex …
    · rw [indicator_of_not_mem (not_mem_Ioc_of_gt hxn), norm_zero,
        mul_nonneg_iff_right_nonneg_of_pos (exp_pos _)]
      exact rpow_nonneg_of_nonneg (le_of_lt hx) _
      -- 🎉 no goals
    · rw [indicator_of_mem (mem_Ioc.mpr ⟨mem_Ioi.mp hx, hxn⟩), norm_mul, Complex.norm_eq_abs,
        Complex.abs_of_nonneg
          (pow_nonneg (sub_nonneg.mpr <| div_le_one_of_le hxn <| by positivity) _),
        Complex.norm_eq_abs, abs_cpow_eq_rpow_re_of_pos hx, sub_re, one_re,
        mul_le_mul_right (rpow_pos_of_pos hx _)]
      exact one_sub_div_pow_le_exp_neg hxn
      -- 🎉 no goals
#align complex.approx_Gamma_integral_tendsto_Gamma_integral Complex.approx_Gamma_integral_tendsto_Gamma_integral

/-- Euler's limit formula for the complex Gamma function. -/
theorem GammaSeq_tendsto_Gamma (s : ℂ) : Tendsto (GammaSeq s) atTop (𝓝 <| Gamma s) := by
  suffices ∀ m : ℕ, -↑m < re s → Tendsto (GammaSeq s) atTop (𝓝 <| GammaAux m s) by
    rw [Gamma]
    apply this
    rw [neg_lt]
    rcases lt_or_le 0 (re s) with (hs | hs)
    · exact (neg_neg_of_pos hs).trans_le (Nat.cast_nonneg _)
    · refine' (Nat.lt_floor_add_one _).trans_le _
      rw [sub_eq_neg_add, Nat.floor_add_one (neg_nonneg.mpr hs), Nat.cast_add_one]
  intro m
  -- ⊢ -↑m < s.re → Tendsto (GammaSeq s) atTop (𝓝 (GammaAux m s))
  induction' m with m IH generalizing s
  -- ⊢ -↑Nat.zero < s.re → Tendsto (GammaSeq s) atTop (𝓝 (GammaAux Nat.zero s))
  · -- Base case: `0 < re s`, so Gamma is given by the integral formula
    intro hs
    -- ⊢ Tendsto (GammaSeq s) atTop (𝓝 (GammaAux Nat.zero s))
    rw [Nat.cast_zero, neg_zero] at hs
    -- ⊢ Tendsto (GammaSeq s) atTop (𝓝 (GammaAux Nat.zero s))
    rw [← Gamma_eq_GammaAux]
    -- ⊢ Tendsto (GammaSeq s) atTop (𝓝 (Gamma s))
    · refine' Tendsto.congr' _ (approx_Gamma_integral_tendsto_Gamma_integral hs)
      -- ⊢ (fun n => ∫ (x : ℝ) in 0 ..↑n, ↑((1 - x / ↑n) ^ n) * ↑x ^ (s - 1)) =ᶠ[atTop] …
      refine' (eventually_ne_atTop 0).mp (eventually_of_forall fun n hn => _)
      -- ⊢ (fun n => ∫ (x : ℝ) in 0 ..↑n, ↑((1 - x / ↑n) ^ n) * ↑x ^ (s - 1)) n = Gamma …
      exact (GammaSeq_eq_approx_Gamma_integral hs hn).symm
      -- 🎉 no goals
    · rwa [Nat.cast_zero, neg_lt_zero]
      -- 🎉 no goals
  · -- Induction step: use recurrence formulae in `s` for Gamma and GammaSeq
    intro hs
    -- ⊢ Tendsto (GammaSeq s) atTop (𝓝 (GammaAux (Nat.succ m) s))
    rw [Nat.cast_succ, neg_add, ← sub_eq_add_neg, sub_lt_iff_lt_add, ← one_re, ← add_re] at hs
    -- ⊢ Tendsto (GammaSeq s) atTop (𝓝 (GammaAux (Nat.succ m) s))
    rw [GammaAux]
    -- ⊢ Tendsto (GammaSeq s) atTop (𝓝 ((fun s => GammaAux m (s + 1) / s) s))
    have := @Tendsto.congr' _ _ _ ?_ _ _
      ((eventually_ne_atTop 0).mp (eventually_of_forall fun n hn => ?_)) ((IH _ hs).div_const s)
    pick_goal 3; · exact GammaSeq_add_one_left s hn -- doesn't work if inlined?
                   -- 🎉 no goals
    conv at this => arg 1; intro n; rw [mul_comm]
    -- ⊢ Tendsto (GammaSeq s) atTop (𝓝 ((fun s => GammaAux m (s + 1) / s) s))
    rwa [← mul_one (GammaAux m (s + 1) / s), tendsto_mul_iff_of_ne_zero _ (one_ne_zero' ℂ)] at this
    -- ⊢ Tendsto (fun n => ↑n / (↑n + 1 + s)) atTop (𝓝 1)
    simp_rw [add_assoc]
    -- ⊢ Tendsto (fun n => ↑n / (↑n + (1 + s))) atTop (𝓝 1)
    exact tendsto_coe_nat_div_add_atTop (1 + s)
    -- 🎉 no goals
#align complex.Gamma_seq_tendsto_Gamma Complex.GammaSeq_tendsto_Gamma

end Complex

end LimitFormula

section GammaReflection

/-! ## The reflection formula -/


namespace Complex

theorem GammaSeq_mul (z : ℂ) {n : ℕ} (hn : n ≠ 0) :
    GammaSeq z n * GammaSeq (1 - z) n =
      n / (n + ↑1 - z) * (↑1 / (z * ∏ j in Finset.range n, (↑1 - z ^ 2 / ((j : ℂ) + 1) ^ 2))) := by
  -- also true for n = 0 but we don't need it
  have aux : ∀ a b c d : ℂ, a * b * (c * d) = a * c * (b * d) := by intros; ring
  -- ⊢ GammaSeq z n * GammaSeq (1 - z) n = ↑n / (↑n + 1 - z) * (1 / (z * ∏ j in Fin …
  rw [GammaSeq, GammaSeq, div_mul_div_comm, aux, ← pow_two]
  -- ⊢ ↑n ^ z * ↑n ^ (1 - z) * ↑n ! ^ 2 / ((∏ j in Finset.range (n + 1), (z + ↑j))  …
  have : (n : ℂ) ^ z * (n : ℂ) ^ (1 - z) = n := by
    rw [← cpow_add _ _ (Nat.cast_ne_zero.mpr hn), add_sub_cancel'_right, cpow_one]
  rw [this, Finset.prod_range_succ', Finset.prod_range_succ, aux, ← Finset.prod_mul_distrib,
    Nat.cast_zero, add_zero, add_comm (1 - z) n, ← add_sub_assoc]
  have : ∀ j : ℕ, (z + ↑(j + 1)) * (↑1 - z + ↑j) =
      ↑((j + 1) ^ 2) * (↑1 - z ^ 2 / ((j : ℂ) + 1) ^ 2) := by
    intro j
    push_cast
    have : (j : ℂ) + 1 ≠ 0 := by rw [← Nat.cast_succ, Nat.cast_ne_zero]; exact Nat.succ_ne_zero j
    field_simp; ring
  simp_rw [this]
  -- ⊢ ↑n * ↑n ! ^ 2 / ((∏ x in Finset.range n, ↑((x + 1) ^ 2) * (1 - z ^ 2 / (↑x + …
  rw [Finset.prod_mul_distrib, ← Nat.cast_prod, Finset.prod_pow,
    Finset.prod_range_add_one_eq_factorial, Nat.cast_pow,
    (by intros; ring : ∀ a b c d : ℂ, a * b * (c * d) = a * (d * (b * c))), ← div_div,
    mul_div_cancel, ← div_div, mul_comm z _, mul_one_div]
  exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr <| Nat.factorial_ne_zero n)
  -- 🎉 no goals
#align complex.Gamma_seq_mul Complex.GammaSeq_mul

/-- Euler's reflection formula for the complex Gamma function. -/
theorem Gamma_mul_Gamma_one_sub (z : ℂ) : Gamma z * Gamma (1 - z) = π / sin (π * z) := by
  have pi_ne : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
  -- ⊢ Gamma z * Gamma (1 - z) = ↑π / sin (↑π * z)
  by_cases hs : sin (↑π * z) = 0
  -- ⊢ Gamma z * Gamma (1 - z) = ↑π / sin (↑π * z)
  · -- first deal with silly case z = integer
    rw [hs, div_zero]
    -- ⊢ Gamma z * Gamma (1 - z) = 0
    rw [← neg_eq_zero, ← Complex.sin_neg, ← mul_neg, Complex.sin_eq_zero_iff, mul_comm] at hs
    -- ⊢ Gamma z * Gamma (1 - z) = 0
    obtain ⟨k, hk⟩ := hs
    -- ⊢ Gamma z * Gamma (1 - z) = 0
    rw [mul_eq_mul_right_iff, eq_false (ofReal_ne_zero.mpr pi_pos.ne'), or_false_iff,
      neg_eq_iff_eq_neg] at hk
    rw [hk]
    -- ⊢ Gamma (-↑k) * Gamma (1 - -↑k) = 0
    cases k
    -- ⊢ Gamma (-↑(Int.ofNat a✝)) * Gamma (1 - -↑(Int.ofNat a✝)) = 0
    · rw [Int.ofNat_eq_coe, Int.cast_ofNat, Complex.Gamma_neg_nat_eq_zero, zero_mul]
      -- 🎉 no goals
    · rw [Int.cast_negSucc, neg_neg, Nat.cast_add, Nat.cast_one, add_comm, sub_add_cancel',
        Complex.Gamma_neg_nat_eq_zero, mul_zero]
  refine' tendsto_nhds_unique ((GammaSeq_tendsto_Gamma z).mul (GammaSeq_tendsto_Gamma <| 1 - z)) _
  -- ⊢ Tendsto (fun x => GammaSeq z x * GammaSeq (1 - z) x) atTop (𝓝 (↑π / sin (↑π  …
  have : ↑π / sin (↑π * z) = 1 * (π / sin (π * z)) := by rw [one_mul]
  -- ⊢ Tendsto (fun x => GammaSeq z x * GammaSeq (1 - z) x) atTop (𝓝 (↑π / sin (↑π  …
  convert Tendsto.congr' ((eventually_ne_atTop 0).mp (eventually_of_forall fun n hn =>
    (GammaSeq_mul z hn).symm)) (Tendsto.mul _ _)
  · convert tendsto_coe_nat_div_add_atTop (1 - z) using 1; ext1 n; rw [add_sub_assoc]
    -- ⊢ (fun n => ↑n / (↑n + 1 - z)) = fun n => ↑n / (↑n + (1 - z))
                                                           -- ⊢ ↑n / (↑n + 1 - z) = ↑n / (↑n + (1 - z))
                                                                   -- 🎉 no goals
  · have : ↑π / sin (↑π * z) = 1 / (sin (π * z) / π) := by field_simp
    -- ⊢ Tendsto (fun n => 1 / (z * ∏ j in Finset.range n, (1 - z ^ 2 / (↑j + 1) ^ 2) …
    convert tendsto_const_nhds.div _ (div_ne_zero hs pi_ne)
    -- ⊢ Tendsto (fun x => z * ∏ j in Finset.range x, (1 - z ^ 2 / (↑j + 1) ^ 2)) atT …
    rw [← tendsto_mul_iff_of_ne_zero tendsto_const_nhds pi_ne, div_mul_cancel _ pi_ne]
    -- ⊢ Tendsto (fun n => (z * ∏ j in Finset.range n, (1 - z ^ 2 / (↑j + 1) ^ 2)) *  …
    convert tendsto_euler_sin_prod z using 1
    -- ⊢ (fun n => (z * ∏ j in Finset.range n, (1 - z ^ 2 / (↑j + 1) ^ 2)) * ↑π) = fu …
    ext1 n; rw [mul_comm, ← mul_assoc]
    -- ⊢ (z * ∏ j in Finset.range n, (1 - z ^ 2 / (↑j + 1) ^ 2)) * ↑π = ↑π * z * ∏ j  …
            -- 🎉 no goals
#align complex.Gamma_mul_Gamma_one_sub Complex.Gamma_mul_Gamma_one_sub

/-- The Gamma function does not vanish on `ℂ` (except at non-positive integers, where the function
is mathematically undefined and we set it to `0` by convention). -/
theorem Gamma_ne_zero {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) : Gamma s ≠ 0 := by
  by_cases h_im : s.im = 0
  -- ⊢ Gamma s ≠ 0
  · have : s = ↑s.re := by
      conv_lhs => rw [← Complex.re_add_im s]
      rw [h_im, ofReal_zero, zero_mul, add_zero]
    rw [this, Gamma_ofReal, ofReal_ne_zero]
    -- ⊢ Real.Gamma s.re ≠ 0
    refine' Real.Gamma_ne_zero fun n => _
    -- ⊢ s.re ≠ -↑n
    specialize hs n
    -- ⊢ s.re ≠ -↑n
    contrapose! hs
    -- ⊢ s = -↑n
    rwa [this, ← ofReal_nat_cast, ← ofReal_neg, ofReal_inj]
    -- 🎉 no goals
  · have : sin (↑π * s) ≠ 0 := by
      rw [Complex.sin_ne_zero_iff]
      intro k
      apply_fun im
      rw [ofReal_mul_im, ← ofReal_int_cast, ← ofReal_mul, ofReal_im]
      exact mul_ne_zero Real.pi_pos.ne' h_im
    have A := div_ne_zero (ofReal_ne_zero.mpr Real.pi_pos.ne') this
    -- ⊢ Gamma s ≠ 0
    rw [← Complex.Gamma_mul_Gamma_one_sub s, mul_ne_zero_iff] at A
    -- ⊢ Gamma s ≠ 0
    exact A.1
    -- 🎉 no goals
#align complex.Gamma_ne_zero Complex.Gamma_ne_zero

theorem Gamma_eq_zero_iff (s : ℂ) : Gamma s = 0 ↔ ∃ m : ℕ, s = -m := by
  constructor
  -- ⊢ Gamma s = 0 → ∃ m, s = -↑m
  · contrapose!; exact Gamma_ne_zero
    -- ⊢ (∀ (m : ℕ), s ≠ -↑m) → Gamma s ≠ 0
                 -- 🎉 no goals
  · rintro ⟨m, rfl⟩; exact Gamma_neg_nat_eq_zero m
    -- ⊢ Gamma (-↑m) = 0
                     -- 🎉 no goals
#align complex.Gamma_eq_zero_iff Complex.Gamma_eq_zero_iff

/-- A weaker, but easier-to-apply, version of `Complex.Gamma_ne_zero`. -/
theorem Gamma_ne_zero_of_re_pos {s : ℂ} (hs : 0 < re s) : Gamma s ≠ 0 := by
  refine' Gamma_ne_zero fun m => _
  -- ⊢ s ≠ -↑m
  contrapose! hs
  -- ⊢ s.re ≤ 0
  simpa only [hs, neg_re, ← ofReal_nat_cast, ofReal_re, neg_nonpos] using Nat.cast_nonneg _
  -- 🎉 no goals
#align complex.Gamma_ne_zero_of_re_pos Complex.Gamma_ne_zero_of_re_pos

end Complex

namespace Real

/-- The sequence with `n`-th term `n ^ s * n! / (s * (s + 1) * ... * (s + n))`, for real `s`. We
will show that this tends to `Γ(s)` as `n → ∞`. -/
noncomputable def GammaSeq (s : ℝ) (n : ℕ) :=
  (n : ℝ) ^ s * n ! / ∏ j : ℕ in Finset.range (n + 1), (s + j)
#align real.Gamma_seq Real.GammaSeq

/-- Euler's limit formula for the real Gamma function. -/
theorem GammaSeq_tendsto_Gamma (s : ℝ) : Tendsto (GammaSeq s) atTop (𝓝 <| Gamma s) := by
  suffices : Tendsto ((↑) ∘ GammaSeq s : ℕ → ℂ) atTop (𝓝 <| Complex.Gamma s)
  -- ⊢ Tendsto (GammaSeq s) atTop (𝓝 (Gamma s))
  exact (Complex.continuous_re.tendsto (Complex.Gamma ↑s)).comp this
  -- ⊢ Tendsto (Complex.ofReal' ∘ GammaSeq s) atTop (𝓝 (Complex.Gamma ↑s))
  convert Complex.GammaSeq_tendsto_Gamma s
  -- ⊢ Complex.ofReal' ∘ GammaSeq s = Complex.GammaSeq ↑s
  ext1 n
  -- ⊢ (Complex.ofReal' ∘ GammaSeq s) n = Complex.GammaSeq (↑s) n
  dsimp only [GammaSeq, Function.comp_apply, Complex.GammaSeq]
  -- ⊢ ↑(↑n ^ s * ↑n ! / ∏ j in Finset.range (n + 1), (s + ↑j)) = ↑n ^ ↑s * ↑n ! /  …
  push_cast
  -- ⊢ ↑(↑n ^ s) * ↑n ! / ∏ x in Finset.range (n + 1), (↑s + ↑x) = ↑n ^ ↑s * ↑n ! / …
  rw [Complex.ofReal_cpow n.cast_nonneg, Complex.ofReal_nat_cast]
  -- 🎉 no goals
#align real.Gamma_seq_tendsto_Gamma Real.GammaSeq_tendsto_Gamma

/-- Euler's reflection formula for the real Gamma function. -/
theorem Gamma_mul_Gamma_one_sub (s : ℝ) : Gamma s * Gamma (1 - s) = π / sin (π * s) := by
  simp_rw [← Complex.ofReal_inj, Complex.ofReal_div, Complex.ofReal_sin, Complex.ofReal_mul, ←
    Complex.Gamma_ofReal, Complex.ofReal_sub, Complex.ofReal_one]
  exact Complex.Gamma_mul_Gamma_one_sub s
  -- 🎉 no goals
#align real.Gamma_mul_Gamma_one_sub Real.Gamma_mul_Gamma_one_sub

end Real

end GammaReflection

section InvGamma

open scoped Real

namespace Complex

/-! ## The reciprocal Gamma function

We show that the reciprocal Gamma function `1 / Γ(s)` is entire. These lemmas show that (in this
case at least) mathlib's conventions for division by zero do actually give a mathematically useful
answer! (These results are useful in the theory of zeta and L-functions.) -/


/-- A reformulation of the Gamma recurrence relation which is true for `s = 0` as well. -/
theorem one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (s : ℂ) :
    (Gamma s)⁻¹ = s * (Gamma (s + 1))⁻¹ := by
  rcases ne_or_eq s 0 with (h | rfl)
  -- ⊢ (Gamma s)⁻¹ = s * (Gamma (s + 1))⁻¹
  · rw [Gamma_add_one s h, mul_inv, mul_inv_cancel_left₀ h]
    -- 🎉 no goals
  · rw [zero_add, Gamma_zero, inv_zero, zero_mul]
    -- 🎉 no goals
#align complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one

/-- The reciprocal of the Gamma function is differentiable everywhere (including the points where
Gamma itself is not). -/
theorem differentiable_one_div_Gamma : Differentiable ℂ fun s : ℂ => (Gamma s)⁻¹ := by
  suffices : ∀ n : ℕ, ∀ (s : ℂ) (_ : -s.re < n), DifferentiableAt ℂ (fun u : ℂ => (Gamma u)⁻¹) s
  -- ⊢ Differentiable ℂ fun s => (Gamma s)⁻¹
  exact fun s =>
    let ⟨n, h⟩ := exists_nat_gt (-s.re)
    this n s h
  intro n
  -- ⊢ ∀ (s : ℂ), -s.re < ↑n → DifferentiableAt ℂ (fun u => (Gamma u)⁻¹) s
  induction' n with m hm
  -- ⊢ ∀ (s : ℂ), -s.re < ↑Nat.zero → DifferentiableAt ℂ (fun u => (Gamma u)⁻¹) s
  · intro s hs
    -- ⊢ DifferentiableAt ℂ (fun u => (Gamma u)⁻¹) s
    rw [Nat.cast_zero, neg_lt_zero] at hs
    -- ⊢ DifferentiableAt ℂ (fun u => (Gamma u)⁻¹) s
    suffices : ∀ m : ℕ, s ≠ -↑m; exact (differentiableAt_Gamma _ this).inv (Gamma_ne_zero this)
    -- ⊢ DifferentiableAt ℂ (fun u => (Gamma u)⁻¹) s
                                 -- ⊢ ∀ (m : ℕ), s ≠ -↑m
    contrapose! hs
    -- ⊢ s.re ≤ 0
    rcases hs with ⟨m, rfl⟩
    -- ⊢ (-↑m).re ≤ 0
    simpa only [neg_re, ← ofReal_nat_cast, ofReal_re, neg_nonpos] using Nat.cast_nonneg m
    -- 🎉 no goals
  · intro s hs
    -- ⊢ DifferentiableAt ℂ (fun u => (Gamma u)⁻¹) s
    rw [funext one_div_Gamma_eq_self_mul_one_div_Gamma_add_one]
    -- ⊢ DifferentiableAt ℂ (fun x => x * (Gamma (x + 1))⁻¹) s
    specialize hm (s + 1) (by rwa [add_re, one_re, neg_add', sub_lt_iff_lt_add, ← Nat.cast_succ])
    -- ⊢ DifferentiableAt ℂ (fun x => x * (Gamma (x + 1))⁻¹) s
    refine' differentiableAt_id.mul (hm.comp s _)
    -- ⊢ DifferentiableAt ℂ (fun x => x + 1) s
    exact differentiableAt_id.add (differentiableAt_const _)
    -- 🎉 no goals
#align complex.differentiable_one_div_Gamma Complex.differentiable_one_div_Gamma

end Complex

end InvGamma

section Doubling

/-!
## The doubling formula for Gamma

We prove the doubling formula for arbitrary real or complex arguments, by analytic continuation from
the positive real case. (Knowing that `Γ⁻¹` is analytic everywhere makes this much simpler, since we
do not have to do any special-case handling for the poles of `Γ`.)
-/


namespace Complex

theorem Gamma_mul_Gamma_add_half (s : ℂ) :
    Gamma s * Gamma (s + 1 / 2) = Gamma (2 * s) * (2 : ℂ) ^ (1 - 2 * s) * ↑(Real.sqrt π) := by
  suffices (fun z => (Gamma z)⁻¹ * (Gamma (z + 1 / 2))⁻¹) = fun z =>
      (Gamma (2 * z))⁻¹ * (2 : ℂ) ^ (2 * z - 1) / ↑(Real.sqrt π) by
    convert congr_arg Inv.inv (congr_fun this s) using 1
    · rw [mul_inv, inv_inv, inv_inv]
    · rw [div_eq_mul_inv, mul_inv, mul_inv, inv_inv, inv_inv, ← cpow_neg, neg_sub]
  have h1 : AnalyticOn ℂ (fun z : ℂ => (Gamma z)⁻¹ * (Gamma (z + 1 / 2))⁻¹) univ := by
    refine' DifferentiableOn.analyticOn _ isOpen_univ
    refine' (differentiable_one_div_Gamma.mul _).differentiableOn
    exact differentiable_one_div_Gamma.comp (differentiable_id.add (differentiable_const _))
  have h2 : AnalyticOn ℂ
      (fun z => (Gamma (2 * z))⁻¹ * (2 : ℂ) ^ (2 * z - 1) / ↑(Real.sqrt π)) univ := by
    refine' DifferentiableOn.analyticOn _ isOpen_univ
    refine' (Differentiable.mul _ (differentiable_const _)).differentiableOn
    apply Differentiable.mul
    · exact differentiable_one_div_Gamma.comp (differentiable_id'.const_mul _)
    · refine' fun t => DifferentiableAt.const_cpow _ (Or.inl two_ne_zero)
      refine' DifferentiableAt.sub_const (differentiableAt_id.const_mul _) _
  have h3 : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] 1) (𝓝[≠] 1) := by
    rw [tendsto_nhdsWithin_iff]; constructor
    · exact tendsto_nhdsWithin_of_tendsto_nhds continuous_ofReal.continuousAt
    · exact eventually_nhdsWithin_iff.mpr (eventually_of_forall fun t ht => ofReal_ne_one.mpr ht)
  refine' AnalyticOn.eq_of_frequently_eq h1 h2 (h3.frequently _)
  -- ⊢ ∃ᶠ (x : ℝ) in 𝓝[{1}ᶜ] 1, (Gamma ↑x)⁻¹ * (Gamma (↑x + 1 / 2))⁻¹ = (Gamma (2 * …
  refine' ((Eventually.filter_mono nhdsWithin_le_nhds) _).frequently
  -- ⊢ ∀ᶠ (x : ℝ) in 𝓝 1, (Gamma ↑x)⁻¹ * (Gamma (↑x + 1 / 2))⁻¹ = (Gamma (2 * ↑x))⁻ …
  refine' (eventually_gt_nhds zero_lt_one).mp (eventually_of_forall fun t ht => _)
  -- ⊢ (Gamma ↑t)⁻¹ * (Gamma (↑t + 1 / 2))⁻¹ = (Gamma (2 * ↑t))⁻¹ * 2 ^ (2 * ↑t - 1 …
  rw [← mul_inv, Gamma_ofReal, (by norm_num : (t : ℂ) + 1 / 2 = ↑(t + 1 / 2)), Gamma_ofReal, ←
    ofReal_mul, Gamma_mul_Gamma_add_half_of_pos ht, ofReal_mul, ofReal_mul, ← Gamma_ofReal,
    mul_inv, mul_inv, (by norm_num : 2 * (t : ℂ) = ↑(2 * t)), Gamma_ofReal,
    ofReal_cpow zero_le_two, show (2 : ℝ) = (2 : ℂ) by norm_cast, ← cpow_neg, ofReal_sub,
    ofReal_one, neg_sub, ← div_eq_mul_inv]
#align complex.Gamma_mul_Gamma_add_half Complex.Gamma_mul_Gamma_add_half

end Complex

namespace Real

open Complex

theorem Gamma_mul_Gamma_add_half (s : ℝ) :
    Gamma s * Gamma (s + 1 / 2) = Gamma (2 * s) * (2 : ℝ) ^ (1 - 2 * s) * sqrt π := by
  rw [← ofReal_inj]
  -- ⊢ ↑(Gamma s * Gamma (s + 1 / 2)) = ↑(Gamma (2 * s) * 2 ^ (1 - 2 * s) * sqrt π)
  simpa only [← Gamma_ofReal, ofReal_cpow zero_le_two, ofReal_mul, ofReal_add, ofReal_div,
    ofReal_sub] using Complex.Gamma_mul_Gamma_add_half ↑s
#align real.Gamma_mul_Gamma_add_half Real.Gamma_mul_Gamma_add_half

end Real

end Doubling
