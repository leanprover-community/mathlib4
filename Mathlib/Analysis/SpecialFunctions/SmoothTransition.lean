/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.PolynomialExp

#align_import analysis.calculus.bump_function_inner from "leanprover-community/mathlib"@"3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe"

/-!
# Infinitely smooth transition function

In this file we construct two infinitely smooth functions with properties that an analytic function
cannot have:

* `expNegInvGlue` is equal to zero for `x ≤ 0` and is strictly positive otherwise; it is given by
  `x ↦ exp (-1/x)` for `x > 0`;

* `Real.smoothTransition` is equal to zero for `x ≤ 0` and is equal to one for `x ≥ 1`; it is given
  by `expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1 - x))`;
-/

noncomputable section

open scoped Classical Topology

open Polynomial Real Filter Set Function

open scoped Polynomial

/-- `expNegInvGlue` is the real function given by `x ↦ exp (-1/x)` for `x > 0` and `0`
for `x ≤ 0`. It is a basic building block to construct smooth partitions of unity. Its main property
is that it vanishes for `x ≤ 0`, it is positive for `x > 0`, and the junction between the two
behaviors is flat enough to retain smoothness. The fact that this function is `C^∞` is proved in
`expNegInvGlue.contDiff`. -/
def expNegInvGlue (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else exp (-x⁻¹)
#align exp_neg_inv_glue expNegInvGlue

namespace expNegInvGlue

/-- The function `expNegInvGlue` vanishes on `(-∞, 0]`. -/
theorem zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : expNegInvGlue x = 0 := by simp [expNegInvGlue, hx]
#align exp_neg_inv_glue.zero_of_nonpos expNegInvGlue.zero_of_nonpos

@[simp] -- Porting note (#10756): new lemma
protected theorem zero : expNegInvGlue 0 = 0 := zero_of_nonpos le_rfl

/-- The function `expNegInvGlue` is positive on `(0, +∞)`. -/
theorem pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < expNegInvGlue x := by
  simp [expNegInvGlue, not_le.2 hx, exp_pos]
#align exp_neg_inv_glue.pos_of_pos expNegInvGlue.pos_of_pos

/-- The function `expNegInvGlue` is nonnegative. -/
theorem nonneg (x : ℝ) : 0 ≤ expNegInvGlue x := by
  cases le_or_gt x 0 with
  | inl h => exact ge_of_eq (zero_of_nonpos h)
  | inr h => exact le_of_lt (pos_of_pos h)
#align exp_neg_inv_glue.nonneg expNegInvGlue.nonneg

-- Porting note (#10756): new lemma
@[simp] theorem zero_iff_nonpos {x : ℝ} : expNegInvGlue x = 0 ↔ x ≤ 0 :=
  ⟨fun h ↦ not_lt.mp fun h' ↦ (pos_of_pos h').ne' h, zero_of_nonpos⟩

/-!
### Smoothness of `expNegInvGlue`

Porting note: Yury Kudryashov rewrote the proof while porting, generalizing auxiliary lemmas and
removing some auxiliary definitions.

In this section we prove that the function `f = expNegInvGlue` is infinitely smooth. To do
this, we show that $g_p(x)=p(x^{-1})f(x)$ is infinitely smooth for any polynomial `p` with real
coefficients. First we show that $g_p(x)$ tends to zero at zero, then we show that it is
differentiable with derivative $g_p'=g_{x^2(p-p')}$. Finally, we prove smoothness of $g_p$ by
induction, then deduce smoothness of $f$ by setting $p=1$.
-/

#noalign exp_neg_inv_glue.P_aux
#noalign exp_neg_inv_glue.f_aux
#noalign exp_neg_inv_glue.f_aux_zero_eq
#noalign exp_neg_inv_glue.f_aux_deriv
#noalign exp_neg_inv_glue.f_aux_deriv_pos
#noalign exp_neg_inv_glue.f_aux_limit
#noalign exp_neg_inv_glue.f_aux_deriv_zero
#noalign exp_neg_inv_glue.f_aux_has_deriv_at

/-- Our function tends to zero at zero faster than any $P(x^{-1})$, $P∈ℝ[X]$, tends to infinity. -/
theorem tendsto_polynomial_inv_mul_zero (p : ℝ[X]) :
    Tendsto (fun x ↦ p.eval x⁻¹ * expNegInvGlue x) (𝓝 0) (𝓝 0) := by
  simp only [expNegInvGlue, mul_ite, mul_zero]
  refine tendsto_const_nhds.if ?_
  simp only [not_le]
  have : Tendsto (fun x ↦ p.eval x⁻¹ / exp x⁻¹) (𝓝[>] 0) (𝓝 0) :=
    p.tendsto_div_exp_atTop.comp tendsto_inv_zero_atTop
  refine this.congr' <| mem_of_superset self_mem_nhdsWithin fun x hx ↦ ?_
  simp [expNegInvGlue, hx.out.not_le, exp_neg, div_eq_mul_inv]

theorem hasDerivAt_polynomial_eval_inv_mul (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun x ↦ p.eval x⁻¹ * expNegInvGlue x)
      ((X ^ 2 * (p - derivative (R := ℝ) p)).eval x⁻¹ * expNegInvGlue x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [zero_of_nonpos hx.le, mul_zero]
    refine (hasDerivAt_const _ 0).congr_of_eventuallyEq ?_
    filter_upwards [gt_mem_nhds hx] with y hy
    rw [zero_of_nonpos hy.le, mul_zero]
  · rw [expNegInvGlue.zero, mul_zero, hasDerivAt_iff_tendsto_slope]
    refine ((tendsto_polynomial_inv_mul_zero (p * X)).mono_left inf_le_left).congr fun x ↦ ?_
    simp [slope_def_field, div_eq_mul_inv, mul_right_comm]
  · have := ((p.hasDerivAt x⁻¹).mul (hasDerivAt_neg _).exp).comp x (hasDerivAt_inv hx.ne')
    convert this.congr_of_eventuallyEq _ using 1
    · simp [expNegInvGlue, hx.not_le]
      ring
    · filter_upwards [lt_mem_nhds hx] with y hy
      simp [expNegInvGlue, hy.not_le]

theorem differentiable_polynomial_eval_inv_mul (p : ℝ[X]) :
    Differentiable ℝ (fun x ↦ p.eval x⁻¹ * expNegInvGlue x) := fun x ↦
  (hasDerivAt_polynomial_eval_inv_mul p x).differentiableAt

theorem continuous_polynomial_eval_inv_mul (p : ℝ[X]) :
    Continuous (fun x ↦ p.eval x⁻¹ * expNegInvGlue x) :=
  (differentiable_polynomial_eval_inv_mul p).continuous

theorem contDiff_polynomial_eval_inv_mul {n : ℕ∞} (p : ℝ[X]) :
    ContDiff ℝ n (fun x ↦ p.eval x⁻¹ * expNegInvGlue x) := by
  apply contDiff_all_iff_nat.2 (fun m => ?_) n
  induction m generalizing p with
  | zero => exact contDiff_zero.2 <| continuous_polynomial_eval_inv_mul _
  | succ m ihm =>
    refine contDiff_succ_iff_deriv.2 ⟨differentiable_polynomial_eval_inv_mul _, ?_⟩
    convert ihm (X ^ 2 * (p - derivative (R := ℝ) p)) using 2
    exact (hasDerivAt_polynomial_eval_inv_mul p _).deriv

/-- The function `expNegInvGlue` is smooth. -/
protected theorem contDiff {n} : ContDiff ℝ n expNegInvGlue := by
  simpa using contDiff_polynomial_eval_inv_mul 1
#align exp_neg_inv_glue.cont_diff expNegInvGlue.contDiff

end expNegInvGlue

/-- An infinitely smooth function `f : ℝ → ℝ` such that `f x = 0` for `x ≤ 0`,
`f x = 1` for `1 ≤ x`, and `0 < f x < 1` for `0 < x < 1`. -/
def Real.smoothTransition (x : ℝ) : ℝ :=
  expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1 - x))
#align real.smooth_transition Real.smoothTransition

namespace Real

namespace smoothTransition

variable {x : ℝ}

open expNegInvGlue

theorem pos_denom (x) : 0 < expNegInvGlue x + expNegInvGlue (1 - x) :=
  (zero_lt_one.lt_or_lt x).elim (fun hx => add_pos_of_pos_of_nonneg (pos_of_pos hx) (nonneg _))
    fun hx => add_pos_of_nonneg_of_pos (nonneg _) (pos_of_pos <| sub_pos.2 hx)
#align real.smooth_transition.pos_denom Real.smoothTransition.pos_denom

theorem one_of_one_le (h : 1 ≤ x) : smoothTransition x = 1 :=
  (div_eq_one_iff_eq <| (pos_denom x).ne').2 <| by rw [zero_of_nonpos (sub_nonpos.2 h), add_zero]
#align real.smooth_transition.one_of_one_le Real.smoothTransition.one_of_one_le

@[simp] -- Porting note (#10756): new theorem
nonrec theorem zero_iff_nonpos : smoothTransition x = 0 ↔ x ≤ 0 := by
  simp only [smoothTransition, _root_.div_eq_zero_iff, (pos_denom x).ne', zero_iff_nonpos, or_false]

theorem zero_of_nonpos (h : x ≤ 0) : smoothTransition x = 0 := zero_iff_nonpos.2 h
#align real.smooth_transition.zero_of_nonpos Real.smoothTransition.zero_of_nonpos

@[simp]
protected theorem zero : smoothTransition 0 = 0 :=
  zero_of_nonpos le_rfl
#align real.smooth_transition.zero Real.smoothTransition.zero

@[simp]
protected theorem one : smoothTransition 1 = 1 :=
  one_of_one_le le_rfl
#align real.smooth_transition.one Real.smoothTransition.one

/-- Since `Real.smoothTransition` is constant on $(-∞, 0]$ and $[1, ∞)$, applying it to the
projection of `x : ℝ` to $[0, 1]$ gives the same result as applying it to `x`. -/
@[simp]
protected theorem projIcc :
    smoothTransition (projIcc (0 : ℝ) 1 zero_le_one x) = smoothTransition x := by
  refine congr_fun
    (IccExtend_eq_self zero_le_one smoothTransition (fun x hx => ?_) fun x hx => ?_) x
  · rw [smoothTransition.zero, zero_of_nonpos hx.le]
  · rw [smoothTransition.one, one_of_one_le hx.le]
#align real.smooth_transition.proj_Icc Real.smoothTransition.projIcc

theorem le_one (x : ℝ) : smoothTransition x ≤ 1 :=
  (div_le_one (pos_denom x)).2 <| le_add_of_nonneg_right (nonneg _)
#align real.smooth_transition.le_one Real.smoothTransition.le_one

theorem nonneg (x : ℝ) : 0 ≤ smoothTransition x :=
  div_nonneg (expNegInvGlue.nonneg _) (pos_denom x).le
#align real.smooth_transition.nonneg Real.smoothTransition.nonneg

theorem lt_one_of_lt_one (h : x < 1) : smoothTransition x < 1 :=
  (div_lt_one <| pos_denom x).2 <| lt_add_of_pos_right _ <| pos_of_pos <| sub_pos.2 h
#align real.smooth_transition.lt_one_of_lt_one Real.smoothTransition.lt_one_of_lt_one

theorem pos_of_pos (h : 0 < x) : 0 < smoothTransition x :=
  div_pos (expNegInvGlue.pos_of_pos h) (pos_denom x)
#align real.smooth_transition.pos_of_pos Real.smoothTransition.pos_of_pos

protected theorem contDiff {n} : ContDiff ℝ n smoothTransition :=
  expNegInvGlue.contDiff.div
    (expNegInvGlue.contDiff.add <| expNegInvGlue.contDiff.comp <| contDiff_const.sub contDiff_id)
    fun x => (pos_denom x).ne'
#align real.smooth_transition.cont_diff Real.smoothTransition.contDiff

protected theorem contDiffAt {x n} : ContDiffAt ℝ n smoothTransition x :=
  smoothTransition.contDiff.contDiffAt
#align real.smooth_transition.cont_diff_at Real.smoothTransition.contDiffAt

protected theorem continuous : Continuous smoothTransition :=
  (@smoothTransition.contDiff 0).continuous
#align real.smooth_transition.continuous Real.smoothTransition.continuous

protected theorem continuousAt : ContinuousAt smoothTransition x :=
  smoothTransition.continuous.continuousAt
#align real.smooth_transition.continuous_at Real.smoothTransition.continuousAt

end smoothTransition

end Real
