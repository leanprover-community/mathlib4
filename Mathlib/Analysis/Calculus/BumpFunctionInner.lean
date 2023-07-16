/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn

! This file was ported from Lean 3 source module analysis.calculus.bump_function_inner
! leanprover-community/mathlib commit 3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.ExtendDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.PolynomialExp
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Topology.Algebra.Polynomial

/-!
# Infinitely smooth bump function

In this file we construct several infinitely smooth functions with properties that an analytic
function cannot have:

* `expNegInvGlue` is equal to zero for `x ≤ 0` and is strictly positive otherwise; it is given by
  `x ↦ exp (-1/x)` for `x > 0`;

* `Real.smoothTransition` is equal to zero for `x ≤ 0` and is equal to one for `x ≥ 1`; it is given
  by `expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1 - x))`;

* `f : ContDiffBump c`, where `c` is a point in a real vector space, is
  a bundled smooth function such that

  - `f` is equal to `1` in `Metric.closedBall c f.rIn`;
  - `support f = Metric.ball c f.rOut`;
  - `0 ≤ f x ≤ 1` for all `x`.

  The structure `ContDiffBump` contains the data required to construct the
  function: real numbers `rIn`, `rOut`, and proofs of `0 < rIn < rOut`. The function itself is
  available through `CoeFun`.

* If `f : ContDiffBump c` and `μ` is a measure on the domain of `f`, then `f.normed μ`
  is a smooth bump function with integral `1` w.r.t. `μ`.
-/

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y) -- Porting note: See issue #2220
noncomputable section

open scoped Classical Topology

open Polynomial Real Filter Set Function

open scoped Polynomial

/-- `expNegInvGlue` is the real function given by `x ↦ exp (-1/x)` for `x > 0` and `0`
for `x ≤ 0`. It is a basic building block to construct smooth partitions of unity. Its main property
is that it vanishes for `x ≤ 0`, it is positive for `x > 0`, and the junction between the two
behaviors is flat enough to retain smoothness. The fact that this function is `C^∞` is proved in
`expNegInvGlue.contDiff `. -/
def expNegInvGlue (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else exp (-x⁻¹)
#align exp_neg_inv_glue expNegInvGlue

namespace expNegInvGlue

/-- The function `expNegInvGlue` vanishes on `(-∞, 0]`. -/
theorem zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : expNegInvGlue x = 0 := by simp [expNegInvGlue, hx]
#align exp_neg_inv_glue.zero_of_nonpos expNegInvGlue.zero_of_nonpos

@[simp] -- porting note: new lemma
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

-- porting note: new lemma
@[simp] theorem zero_iff_nonpos : expNegInvGlue x = 0 ↔ x ≤ 0 :=
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

@[simp] -- porting note: new theorem
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
  refine' congr_fun (IccExtend_eq_self zero_le_one smoothTransition (fun x hx => _) fun x hx => _) x
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

variable {E X : Type _}

/-- `f : ContDiffBump c`, where `c` is a point in a normed vector space, is a
bundled smooth function such that

- `f` is equal to `1` in `Metric.closedBall c f.rIn`;
- `support f = Metric.ball c f.rOut`;
- `0 ≤ f x ≤ 1` for all `x`.

The structure `ContDiffBump` contains the data required to construct the function:
real numbers `rIn`, `rOut`, and proofs of `0 < rIn < rOut`. The function itself is available through
`CoeFun` when the space is nice enough, i.e., satisfies the `HasContDiffBump` typeclass. -/
structure ContDiffBump (c : E) where
  (rIn rOut : ℝ)
  rIn_pos : 0 < rIn
  rIn_lt_rOut : rIn < rOut
#align cont_diff_bump ContDiffBump
#align cont_diff_bump.r ContDiffBump.rIn
set_option linter.uppercaseLean3 false in
#align cont_diff_bump.R ContDiffBump.rOut
#align cont_diff_bump.r_pos ContDiffBump.rIn_pos
set_option linter.uppercaseLean3 false in
#align cont_diff_bump.r_lt_R ContDiffBump.rIn_lt_rOut

/-- The base function from which one will construct a family of bump functions. One could
add more properties if they are useful and satisfied in the examples of inner product spaces
and finite dimensional vector spaces, notably derivative norm control in terms of `R - 1`.

TODO: do we ever need `f x = 1 ↔ ‖x‖ ≤ 1`? -/
-- porting note: was @[nolint has_nonempty_instance]
structure ContDiffBumpBase (E : Type _) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E → ℝ
  mem_Icc : ∀ (R : ℝ) (x : E), toFun R x ∈ Icc (0 : ℝ) 1
  symmetric : ∀ (R : ℝ) (x : E), toFun R (-x) = toFun R x
  smooth : ContDiffOn ℝ ⊤ (uncurry toFun) (Ioi (1 : ℝ) ×ˢ (univ : Set E))
  eq_one : ∀ R : ℝ, 1 < R → ∀ x : E, ‖x‖ ≤ 1 → toFun R x = 1
  support : ∀ R : ℝ, 1 < R → Function.support (toFun R) = Metric.ball (0 : E) R
#align cont_diff_bump_base ContDiffBumpBase

/-- A class registering that a real vector space admits bump functions. This will be instantiated
first for inner product spaces, and then for finite-dimensional normed spaces.
We use a specific class instead of `Nonempty (ContDiffBumpBase E)` for performance reasons. -/
class HasContDiffBump (E : Type _) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop where
  out : Nonempty (ContDiffBumpBase E)
#align has_cont_diff_bump HasContDiffBump

/-- In a space with `C^∞` bump functions, register some function that will be used as a basis
to construct bump functions of arbitrary size around any point. -/
def someContDiffBumpBase (E : Type _) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [hb : HasContDiffBump E] : ContDiffBumpBase E :=
  Nonempty.some hb.out
#align some_cont_diff_bump_base someContDiffBumpBase

-- porting note: this definition was hidden inside the next instance.
/-- A base bump function in an inner product space. This construction works in any space with a
norm smooth away from zero but we do not have a typeclass for this. -/
def ContDiffBumpBase.ofInnerProductSpace (E : Type _) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [InnerProductSpace ℝ E] : ContDiffBumpBase E where
  toFun R x := smoothTransition ((R - ‖x‖) / (R - 1))
  mem_Icc _ _ := ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩
  symmetric _ _ := by simp only [norm_neg]
  smooth := by
    rintro ⟨R, x⟩ ⟨hR : 1 < R, -⟩
    apply ContDiffAt.contDiffWithinAt
    rw [← sub_pos] at hR
    rcases eq_or_ne x 0 with rfl | hx
    · have A : ContinuousAt (fun p : ℝ × E ↦ (p.1 - ‖p.2‖) / (p.1 - 1)) (R, 0) :=
        (continuousAt_fst.sub continuousAt_snd.norm).div
          (continuousAt_fst.sub continuousAt_const) hR.ne'
      have B : ∀ᶠ p in 𝓝 (R, (0 : E)), 1 ≤ (p.1 - ‖p.2‖) / (p.1 - 1) :=
        A.eventually <| le_mem_nhds <| (one_lt_div hR).2 <| sub_lt_sub_left (by simp) _
      refine (contDiffAt_const (c := 1)).congr_of_eventuallyEq <| B.mono fun _ ↦
        smoothTransition.one_of_one_le
    · refine smoothTransition.contDiffAt.comp _ (ContDiffAt.div ?_ ?_ hR.ne')
      · exact contDiffAt_fst.sub (contDiffAt_snd.norm ℝ hx)
      · exact contDiffAt_fst.sub contDiffAt_const
  eq_one R hR x hx := smoothTransition.one_of_one_le <| (one_le_div <| sub_pos.2 hR).2 <|
    sub_le_sub_left hx _
  support R hR := by
    ext x
    rw [mem_support, Ne.def, smoothTransition.zero_iff_nonpos, not_le, mem_ball_zero_iff]
    simp [div_pos_iff, sq_lt_sq, abs_of_pos (one_pos.trans hR), hR, hR.not_lt]

/-- Any inner product space has smooth bump functions. -/
instance (priority := 100) hasContDiffBump_of_innerProductSpace (E : Type _) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] : HasContDiffBump E :=
  ⟨⟨.ofInnerProductSpace E⟩⟩
#align has_cont_diff_bump_of_inner_product_space hasContDiffBump_of_innerProductSpace

namespace ContDiffBump

theorem rOut_pos {c : E} (f : ContDiffBump c) : 0 < f.rOut :=
  f.rIn_pos.trans f.rIn_lt_rOut
set_option linter.uppercaseLean3 false in
#align cont_diff_bump.R_pos ContDiffBump.rOut_pos

theorem one_lt_rOut_div_rIn {c : E} (f : ContDiffBump c) : 1 < f.rOut / f.rIn := by
  rw [one_lt_div f.rIn_pos]
  exact f.rIn_lt_rOut
set_option linter.uppercaseLean3 false in
#align cont_diff_bump.one_lt_R_div_r ContDiffBump.one_lt_rOut_div_rIn

instance (c : E) : Inhabited (ContDiffBump c) :=
  ⟨⟨1, 2, zero_lt_one, one_lt_two⟩⟩

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [HasContDiffBump E] {c : E} (f : ContDiffBump c) {x : E} {n : ℕ∞}

/-- The function defined by `f : ContDiffBump c`. Use automatic coercion to
function instead. -/
@[coe] def toFun {c : E} (f : ContDiffBump c) : E → ℝ :=
  (someContDiffBumpBase E).toFun (f.rOut / f.rIn) ∘ fun x ↦ (f.rIn⁻¹ • (x - c))
#align cont_diff_bump.to_fun ContDiffBump.toFun

instance : CoeFun (ContDiffBump c) fun _ => E → ℝ :=
  ⟨toFun⟩

protected theorem apply (x : E) :
    f x = (someContDiffBumpBase E).toFun (f.rOut / f.rIn) (f.rIn⁻¹ • (x - c)) :=
  rfl
#align cont_diff_bump.def ContDiffBump.apply

protected theorem sub (x : E) : f (c - x) = f (c + x) := by
  simp [f.apply, ContDiffBumpBase.symmetric]
#align cont_diff_bump.sub ContDiffBump.sub

protected theorem neg (f : ContDiffBump (0 : E)) (x : E) : f (-x) = f x := by
  simp_rw [← zero_sub, f.sub, zero_add]
#align cont_diff_bump.neg ContDiffBump.neg

open Metric

theorem one_of_mem_closedBall (hx : x ∈ closedBall c f.rIn) : f x = 1 := by
  apply ContDiffBumpBase.eq_one _ _ f.one_lt_rOut_div_rIn
  simpa only [norm_smul, norm_eq_abs, abs_inv, abs_of_nonneg f.rIn_pos.le, ← div_eq_inv_mul,
    div_le_one f.rIn_pos] using mem_closedBall_iff_norm.1 hx
#align cont_diff_bump.one_of_mem_closed_ball ContDiffBump.one_of_mem_closedBall

theorem nonneg : 0 ≤ f x :=
  (ContDiffBumpBase.mem_Icc (someContDiffBumpBase E) _ _).1
#align cont_diff_bump.nonneg ContDiffBump.nonneg

/-- A version of `ContDiffBump.nonneg` with `x` explicit -/
theorem nonneg' (x : E) : 0 ≤ f x := f.nonneg
#align cont_diff_bump.nonneg' ContDiffBump.nonneg'

theorem le_one : f x ≤ 1 :=
  (ContDiffBumpBase.mem_Icc (someContDiffBumpBase E) _ _).2
#align cont_diff_bump.le_one ContDiffBump.le_one

theorem support_eq : Function.support (f : E → ℝ) = Metric.ball c f.rOut := by
  simp only [toFun, support_comp_eq_preimage, ContDiffBumpBase.support _ _ f.one_lt_rOut_div_rIn]
  ext x
  simp only [mem_ball_iff_norm, sub_zero, norm_smul, mem_preimage, norm_eq_abs, abs_inv,
    abs_of_pos f.rIn_pos, ← div_eq_inv_mul, div_lt_div_right f.rIn_pos]
#align cont_diff_bump.support_eq ContDiffBump.support_eq

theorem tsupport_eq : tsupport f = closedBall c f.rOut := by
  simp_rw [tsupport, f.support_eq, closure_ball _ f.rOut_pos.ne']
#align cont_diff_bump.tsupport_eq ContDiffBump.tsupport_eq

theorem pos_of_mem_ball (hx : x ∈ ball c f.rOut) : 0 < f x :=
  f.nonneg.lt_of_ne' <| by rwa [← support_eq, mem_support] at hx
#align cont_diff_bump.pos_of_mem_ball ContDiffBump.pos_of_mem_ball

theorem zero_of_le_dist (hx : f.rOut ≤ dist x c) : f x = 0 := by
  rwa [← nmem_support, support_eq, mem_ball, not_lt]
#align cont_diff_bump.zero_of_le_dist ContDiffBump.zero_of_le_dist

protected theorem hasCompactSupport [FiniteDimensional ℝ E] : HasCompactSupport f := by
  simp_rw [HasCompactSupport, f.tsupport_eq, isCompact_closedBall]
#align cont_diff_bump.has_compact_support ContDiffBump.hasCompactSupport

theorem eventuallyEq_one_of_mem_ball (h : x ∈ ball c f.rIn) : f =ᶠ[𝓝 x] 1 :=
  mem_of_superset (closedBall_mem_nhds_of_mem h) fun _ ↦ f.one_of_mem_closedBall
#align cont_diff_bump.eventually_eq_one_of_mem_ball ContDiffBump.eventuallyEq_one_of_mem_ball

theorem eventuallyEq_one : f =ᶠ[𝓝 c] 1 :=
  f.eventuallyEq_one_of_mem_ball (mem_ball_self f.rIn_pos)
#align cont_diff_bump.eventually_eq_one ContDiffBump.eventuallyEq_one

-- porting note: new lemma
/-- `ContDiffBump` is `𝒞ⁿ` in all its arguments. -/
protected theorem _root_.ContDiffWithinAt.contDiffBump {c g : X → E} {s : Set X}
    {f : ∀ x, ContDiffBump (c x)} {x : X} (hc : ContDiffWithinAt ℝ n c s x)
    (hr : ContDiffWithinAt ℝ n (fun x => (f x).rIn) s x)
    (hR : ContDiffWithinAt ℝ n (fun x => (f x).rOut) s x)
    (hg : ContDiffWithinAt ℝ n g s x) :
    ContDiffWithinAt ℝ n (fun x => f x (g x)) s x := by
  change ContDiffWithinAt ℝ n (uncurry (someContDiffBumpBase E).toFun ∘ fun x : X =>
    ((f x).rOut / (f x).rIn, (f x).rIn⁻¹ • (g x - c x))) s x
  refine (((someContDiffBumpBase E).smooth.contDiffAt ?_).of_le le_top).comp_contDiffWithinAt x ?_
  · exact prod_mem_nhds (Ioi_mem_nhds (f x).one_lt_rOut_div_rIn) univ_mem
  · exact (hR.div hr (f x).rIn_pos.ne').prod ((hr.inv (f x).rIn_pos.ne').smul (hg.sub hc))

/-- `ContDiffBump` is `𝒞ⁿ` in all its arguments. -/
protected nonrec theorem _root_.ContDiffAt.contDiffBump {c g : X → E} {f : ∀ x, ContDiffBump (c x)}
    {x : X} (hc : ContDiffAt ℝ n c x) (hr : ContDiffAt ℝ n (fun x => (f x).rIn) x)
    (hR : ContDiffAt ℝ n (fun x => (f x).rOut) x) (hg : ContDiffAt ℝ n g x) :
    ContDiffAt ℝ n (fun x => f x (g x)) x :=
  hc.contDiffBump hr hR hg
#align cont_diff_at.cont_diff_bump ContDiffAt.contDiffBump

theorem _root_.ContDiff.contDiffBump {c g : X → E} {f : ∀ x, ContDiffBump (c x)}
    (hc : ContDiff ℝ n c) (hr : ContDiff ℝ n fun x => (f x).rIn)
    (hR : ContDiff ℝ n fun x => (f x).rOut) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n fun x => f x (g x) := by
  rw [contDiff_iff_contDiffAt] at *
  exact fun x => (hc x).contDiffBump (hr x) (hR x) (hg x)
#align cont_diff.cont_diff_bump ContDiff.contDiffBump

protected theorem contDiff : ContDiff ℝ n f :=
  contDiff_const.contDiffBump contDiff_const contDiff_const contDiff_id
#align cont_diff_bump.cont_diff ContDiffBump.contDiff

protected theorem contDiffAt : ContDiffAt ℝ n f x :=
  f.contDiff.contDiffAt
#align cont_diff_bump.cont_diff_at ContDiffBump.contDiffAt

protected theorem contDiffWithinAt {s : Set E} : ContDiffWithinAt ℝ n f s x :=
  f.contDiffAt.contDiffWithinAt
#align cont_diff_bump.cont_diff_within_at ContDiffBump.contDiffWithinAt

protected theorem continuous : Continuous f :=
  contDiff_zero.mp f.contDiff
#align cont_diff_bump.continuous ContDiffBump.continuous

open MeasureTheory

variable [MeasurableSpace E] {μ : Measure E}

/-- A bump function normed so that `∫ x, f.normed μ x ∂μ = 1`. -/
protected def normed (μ : Measure E) : E → ℝ := fun x => f x / ∫ x, f x ∂μ
#align cont_diff_bump.normed ContDiffBump.normed

theorem normed_def {μ : Measure E} (x : E) : f.normed μ x = f x / ∫ x, f x ∂μ :=
  rfl
#align cont_diff_bump.normed_def ContDiffBump.normed_def

theorem nonneg_normed (x : E) : 0 ≤ f.normed μ x :=
  div_nonneg f.nonneg <| integral_nonneg f.nonneg'
#align cont_diff_bump.nonneg_normed ContDiffBump.nonneg_normed

theorem contDiff_normed {n : ℕ∞} : ContDiff ℝ n (f.normed μ) :=
  f.contDiff.div_const _
#align cont_diff_bump.cont_diff_normed ContDiffBump.contDiff_normed

theorem continuous_normed : Continuous (f.normed μ) :=
  f.continuous.div_const _
#align cont_diff_bump.continuous_normed ContDiffBump.continuous_normed

theorem normed_sub (x : E) : f.normed μ (c - x) = f.normed μ (c + x) := by
  simp_rw [f.normed_def, f.sub]
#align cont_diff_bump.normed_sub ContDiffBump.normed_sub

theorem normed_neg (f : ContDiffBump (0 : E)) (x : E) : f.normed μ (-x) = f.normed μ x := by
  simp_rw [f.normed_def, f.neg]
#align cont_diff_bump.normed_neg ContDiffBump.normed_neg

variable [BorelSpace E] [FiniteDimensional ℝ E] [IsLocallyFiniteMeasure μ]

protected theorem integrable : Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
#align cont_diff_bump.integrable ContDiffBump.integrable

protected theorem integrable_normed : Integrable (f.normed μ) μ :=
  f.integrable.div_const _
#align cont_diff_bump.integrable_normed ContDiffBump.integrable_normed

variable [μ.IsOpenPosMeasure]

theorem integral_pos : 0 < ∫ x, f x ∂μ := by
  refine' (integral_pos_iff_support_of_nonneg f.nonneg' f.integrable).mpr _
  rw [f.support_eq]
  exact measure_ball_pos μ c f.rOut_pos
#align cont_diff_bump.integral_pos ContDiffBump.integral_pos

theorem integral_normed : ∫ x, f.normed μ x ∂μ = 1 := by
  simp_rw [ContDiffBump.normed, div_eq_mul_inv, mul_comm (f _), ← smul_eq_mul, integral_smul]
  exact inv_mul_cancel f.integral_pos.ne'
#align cont_diff_bump.integral_normed ContDiffBump.integral_normed

theorem support_normed_eq : Function.support (f.normed μ) = Metric.ball c f.rOut := by
  unfold ContDiffBump.normed
  rw [support_div, f.support_eq, support_const f.integral_pos.ne', inter_univ]
#align cont_diff_bump.support_normed_eq ContDiffBump.support_normed_eq

theorem tsupport_normed_eq : tsupport (f.normed μ) = Metric.closedBall c f.rOut := by
  rw [tsupport, f.support_normed_eq, closure_ball _ f.rOut_pos.ne']
#align cont_diff_bump.tsupport_normed_eq ContDiffBump.tsupport_normed_eq

theorem hasCompactSupport_normed : HasCompactSupport (f.normed μ) := by
  simp only [HasCompactSupport, f.tsupport_normed_eq (μ := μ), isCompact_closedBall]
#align cont_diff_bump.has_compact_support_normed ContDiffBump.hasCompactSupport_normed

theorem tendsto_support_normed_smallSets {ι} {φ : ι → ContDiffBump c} {l : Filter ι}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) :
    Tendsto (fun i => Function.support fun x => (φ i).normed μ x) l (𝓝 c).smallSets := by
  simp_rw [NormedAddCommGroup.tendsto_nhds_zero, Real.norm_eq_abs,
    abs_eq_self.mpr (φ _).rOut_pos.le] at hφ
  rw [nhds_basis_ball.smallSets.tendsto_right_iff]
  refine fun ε hε ↦ (hφ ε hε).mono fun i hi ↦ ?_
  rw [(φ i).support_normed_eq]
  exact ball_subset_ball hi.le
#align cont_diff_bump.tendsto_support_normed_small_sets ContDiffBump.tendsto_support_normed_smallSets

variable (μ)

theorem integral_normed_smul [CompleteSpace X] (z : X) : ∫ x, f.normed μ x • z ∂μ = z := by
  simp_rw [integral_smul_const, f.integral_normed (μ := μ), one_smul]
#align cont_diff_bump.integral_normed_smul ContDiffBump.integral_normed_smul

end ContDiffBump
