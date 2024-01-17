/-
Copyright (c) 2020 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

#align_import data.real.pi.leibniz from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-! ### Leibniz's Series for Pi -/


namespace Real

open Filter Set

open scoped Classical BigOperators Topology Real

/-- This theorem establishes **Leibniz's series for `π`**: The alternating sum of the reciprocals
  of the odd numbers is `π/4`. Note that this is a conditionally rather than absolutely convergent
  series. The main tool that this proof uses is the Mean Value Theorem (specifically avoiding the
  Fundamental Theorem of Calculus).

  Intuitively, the theorem holds because Leibniz's series is the Taylor series of `arctan x`
  centered about `0` and evaluated at the value `x = 1`. Therefore, much of this proof consists of
  reasoning about a function
    `f := arctan x - ∑ i in Finset.range k, (-(1:ℝ))^i * x^(2*i+1) / (2*i+1)`,
  the difference between `arctan` and the `k`-th partial sum of its Taylor series. Some ingenuity is
  required due to the fact that the Taylor series is not absolutely convergent at `x = 1`.

  This proof requires a bound on `f 1`, the key idea being that `f 1` can be split as the sum of
  `f 1 - f u` and `f u`, where `u` is a sequence of values in [0,1], carefully chosen such that
  each of these two terms can be controlled (in different ways).

  We begin the proof by (1) introducing that sequence `u` and then proving that another sequence
  constructed from `u` tends to `0` at `+∞`. After (2) converting the limit in our goal to an
  inequality, we (3) introduce the auxiliary function `f` defined above. Next, we (4) compute the
  derivative of `f`, denoted by `f'`, first generally and then on each of two subintervals of [0,1].
  We then (5) prove a bound for `f'`, again both generally as well as on each of the two
  subintervals. Finally, we (6) apply the Mean Value Theorem twice, obtaining bounds on `f 1 - f u`
  and `f u - f 0` from the bounds on `f'` (note that `f 0 = 0`). -/
theorem tendsto_sum_pi_div_four :
    Tendsto (fun k => ∑ i in Finset.range k, (-(1 : ℝ)) ^ i / (2 * i + 1)) atTop (𝓝 (π / 4)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero, ← tendsto_zero_iff_norm_tendsto_zero]
  -- (1) We introduce a useful sequence `u` of values in [0,1], then prove that another sequence
  --     constructed from `u` tends to `0` at `+∞`
  let u := fun k : ℕ => (k : NNReal) ^ (-1 / (2 * (k : ℝ) + 1))
  have H : Tendsto (fun k : ℕ => (1 : ℝ) - u k + u k ^ (2 * (k : ℝ) + 1)) atTop (𝓝 0) := by
    convert (((tendsto_rpow_div_mul_add (-1) 2 1 two_ne_zero.symm).neg.const_add 1).add
        tendsto_inv_atTop_zero).comp tendsto_nat_cast_atTop_atTop using 1
    · ext k
      simp only [NNReal.coe_nat_cast, Function.comp_apply, NNReal.coe_rpow]
      rw [← rpow_mul (Nat.cast_nonneg k) (-1 / (2 * (k : ℝ) + 1)) (2 * (k : ℝ) + 1),
        @div_mul_cancel _ _ (2 * (k : ℝ) + 1) _
          (by norm_cast; simp only [Nat.succ_ne_zero, not_false_iff]),
        rpow_neg_one k, sub_eq_add_neg]
    · simp only [add_zero, add_right_neg]
  -- (2) We convert the limit in our goal to an inequality
  refine' squeeze_zero_norm _ H
  intro k
  -- Since `k` is now fixed, we henceforth denote `u k` as `U`
  let U := u k
  -- (3) We introduce an auxiliary function `f`
  let b (i : ℕ) x := (-(1 : ℝ)) ^ i * x ^ (2 * i + 1) / (2 * i + 1)
  let f x := arctan x - ∑ i in Finset.range k, b i x
  suffices f_bound : |f 1 - f 0| ≤ (1 : ℝ) - U + U ^ (2 * (k : ℝ) + 1)
  · rw [← norm_neg]
    convert f_bound using 1
    simp
  -- We show that `U` is indeed in [0,1]
  have hU1 : (U : ℝ) ≤ 1 := by
    by_cases hk : k = 0
    · simp [hk]
    · exact rpow_le_one_of_one_le_of_nonpos
        (by norm_cast; exact Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hk)) (le_of_lt
          (@div_neg_of_neg_of_pos _ _ (-(1 : ℝ)) (2 * k + 1) (neg_neg_iff_pos.mpr zero_lt_one)
            (by norm_cast; exact Nat.succ_pos')))
  have hU2 := NNReal.coe_nonneg U
  -- (4) We compute the derivative of `f`, denoted by `f'`
  let f' := fun x : ℝ => (-x ^ 2) ^ k / (1 + x ^ 2)
  have has_deriv_at_f : ∀ x, HasDerivAt f (f' x) x := by
    intro x
    have has_deriv_at_b : ∀ i ∈ Finset.range k, HasDerivAt (b i) ((-x ^ 2) ^ i) x := by
      intro i _
      convert HasDerivAt.const_mul ((-1 : ℝ) ^ i / (2 * i + 1))
          (HasDerivAt.pow (2 * i + 1) (hasDerivAt_id x)) using 1
      · ext y
        simp only [id.def]
        ring
      · simp
        rw [← mul_assoc, @div_mul_cancel _ _ (2 * (i : ℝ) + 1) _ (by norm_cast; linarith),
          pow_mul x 2 i, ← mul_pow (-1 : ℝ) (x ^ 2) i]
        ring_nf
    convert (hasDerivAt_arctan x).sub (HasDerivAt.sum has_deriv_at_b) using 1
    have g_sum :=
      @geom_sum_eq _ _ (-x ^ 2) ((neg_nonpos.mpr (sq_nonneg x)).trans_lt zero_lt_one).ne k
    simp only at g_sum ⊢
    rw [g_sum, ← neg_add' (x ^ 2) 1, add_comm (x ^ 2) 1, sub_eq_add_neg, neg_div', neg_div_neg_eq]
    ring
  have hderiv1 : ∀ x ∈ Icc (U : ℝ) 1, HasDerivWithinAt f (f' x) (Icc (U : ℝ) 1) x := fun x _ =>
    (has_deriv_at_f x).hasDerivWithinAt
  have hderiv2 : ∀ x ∈ Icc 0 (U : ℝ), HasDerivWithinAt f (f' x) (Icc 0 (U : ℝ)) x := fun x _ =>
    (has_deriv_at_f x).hasDerivWithinAt
  -- (5) We prove a general bound for `f'` and then more precise bounds on each of two subintervals
  have f'_bound : ∀ x ∈ Icc (-1 : ℝ) 1, |f' x| ≤ |x| ^ (2 * k) := by
    intro x _
    rw [abs_div, IsAbsoluteValue.abv_pow abs (-x ^ 2) k, abs_neg, IsAbsoluteValue.abv_pow abs x 2,
      ← pow_mul]
    refine' div_le_of_nonneg_of_le_mul (abs_nonneg _) (pow_nonneg (abs_nonneg _) _) _
    refine' le_mul_of_one_le_right (pow_nonneg (abs_nonneg _) _) _
    rw_mod_cast [abs_of_nonneg (add_nonneg zero_le_one (sq_nonneg x) : (0 : ℝ) ≤ _)]
    exact (le_add_of_nonneg_right (sq_nonneg x) : (1 : ℝ) ≤ _)
  have hbound1 : ∀ x ∈ Ico (U : ℝ) 1, |f' x| ≤ 1 := by
    rintro x ⟨hx_left, hx_right⟩
    have hincr := pow_le_pow_left (le_trans hU2 hx_left) (le_of_lt hx_right) (2 * k)
    rw [one_pow (2 * k), ← abs_of_nonneg (le_trans hU2 hx_left)] at hincr
    rw [← abs_of_nonneg (le_trans hU2 hx_left)] at hx_right
    linarith [f'_bound x (mem_Icc.mpr (abs_le.mp (le_of_lt hx_right)))]
  have hbound2 : ∀ x ∈ Ico 0 (U : ℝ), |f' x| ≤ U ^ (2 * k) := by
    rintro x ⟨hx_left, hx_right⟩
    have hincr := pow_le_pow_left hx_left (le_of_lt hx_right) (2 * k)
    rw [← abs_of_nonneg hx_left] at hincr hx_right
    rw [← abs_of_nonneg hU2] at hU1 hx_right
    exact (f'_bound x (mem_Icc.mpr (abs_le.mp (le_trans (le_of_lt hx_right) hU1)))).trans hincr
  -- (6) We twice apply the Mean Value Theorem to obtain bounds on `f` from the bounds on `f'`
  have mvt1 := norm_image_sub_le_of_norm_deriv_le_segment' hderiv1 hbound1 _ (right_mem_Icc.mpr hU1)
  have mvt2 := norm_image_sub_le_of_norm_deriv_le_segment' hderiv2 hbound2 _ (right_mem_Icc.mpr hU2)
  -- The following algebra is enough to complete the proof
  calc
    |f 1 - f 0| = |f 1 - f U + (f U - f 0)| := by simp
    _ ≤ 1 * (1 - U) + U ^ (2 * k) * (U - 0) :=
      (le_trans (abs_add (f 1 - f U) (f U - f 0)) (add_le_add mvt1 mvt2))
    _ = 1 - U + (U : ℝ) ^ (2 * k) * U := by simp
    _ = 1 - u k + u k ^ (2 * (k : ℝ) + 1) := by rw [← pow_succ' (U : ℝ) (2 * k)]; norm_cast
#align real.tendsto_sum_pi_div_four Real.tendsto_sum_pi_div_four

end Real
