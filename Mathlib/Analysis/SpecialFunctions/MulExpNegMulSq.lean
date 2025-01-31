/-
Copyright (c) 2024 Jakob Stiefel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Stiefel
-/
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Definition of `mulExpNegMulSq` and properties

`mulExpNegMulSq` is the mapping `fun (ε : ℝ) (x : ℝ) => x * Real.exp (- (ε * x * x))`. By
composition, It can be used to transform a function `g : E → ℝ` into a bounded function
`(mulExpNegMulSq ε).comp g : E → ℝ = fun x => g x * Real.exp (-ε * g x * g x)`.

## Main Properties

- `abs_mulExpNegMulSq_comp_le`: For fixed `ε > 0`, the mapping `(mulExpNegMulSq ε).comp g` is
  bounded by `Real.sqrt ε⁻¹` uniformly in `g`;
- `tendsto_mulExpNegMulSq_comp`: For fixed function `g`, the mapping `(mulExpNegMulSq ε).comp g`
  converges pointwise to `g` as `ε → 0`;
- `continuous_mulExpNegMulSq_comp`: If the function `g` is continuous, the function
  `(mulExpNegMulSq ε).comp g` is continuous;
- `abs_mulExpNegMulSq_comp_le_norm`: For a fixed bounded continuous function `g`, the mapping
  `(mulExpNegMulSq ε).comp g` is bounded by `norm g`, uniformly in `ε ≥ 0`;
-/

open NNReal ENNReal BoundedContinuousFunction Filter

namespace Real

section mulExpNegMulSq

/-! ### Definition and properties of `fun x => x * Real.exp (- x * x)`-/

/--
Mapping `fun ε x => x * Real.exp (- (ε * x * x))`. It can be used to transform functions into
bounded functions, see `section MulExpNegMulSq_comp`.
-/
noncomputable
def mulExpNegMulSq (ε x : ℝ) := x * exp (- (ε * x * x))

theorem mulExpNegSq_apply (ε x : ℝ) : mulExpNegMulSq ε x = x * exp (- (ε * x * x)) := rfl

theorem mulExpNegSq_one (x : ℝ) : mulExpNegMulSq 1 x = x * exp (-x * x) := by
  simp [mulExpNegMulSq]

theorem neg_mulExpNegMulSq_neg (ε x : ℝ) : - mulExpNegMulSq ε (-x) = mulExpNegMulSq ε x := by
  simp [mulExpNegMulSq]

theorem mulExpNegMulSq_one_le_one (x : ℝ) : mulExpNegMulSq 1 x ≤ 1 := by
  simp [mulExpNegMulSq]
  rw [← le_div_iff₀ (exp_pos (-(x * x))), exp_neg, div_inv_eq_mul, one_mul]
  apply le_trans _ (add_one_le_exp (x * x))
  nlinarith

theorem neg_one_le_mulExpNegMulSq_one (x : ℝ) : -1 ≤ mulExpNegMulSq 1 x := by
  rw [← neg_mulExpNegMulSq_neg, neg_le_neg_iff]
  exact mulExpNegMulSq_one_le_one (-x)

theorem abs_mulExpNegMulSq_one_le_one (x : ℝ) : |mulExpNegMulSq 1 x| ≤ 1 :=
  abs_le.mpr ⟨neg_one_le_mulExpNegMulSq_one x, mulExpNegMulSq_one_le_one x⟩

theorem differentiableAt_expNegSq (y : ℝ) :
    DifferentiableAt ℝ (fun (x : ℝ) => exp (-x * x)) y := by
  simp only [neg_mul, differentiableAt_neg_iff, differentiableAt_id', DifferentiableAt.mul,
    DifferentiableAt.exp, implies_true]

theorem differentiable_expNegSq : Differentiable ℝ (fun (x : ℝ) => exp (-x * x)) :=
  fun _ => differentiableAt_expNegSq _

theorem hasDerivAt_expNegSq (y : ℝ) :
    HasDerivAt (fun (x : ℝ) => exp (-x * x)) (exp (-y * y) * (-2 * y)) y :=
  HasDerivAt.exp (HasDerivAt.congr_deriv
      (HasDerivAt.mul (hasDerivAt_neg' y) (hasDerivAt_id' y)) (by ring))

theorem deriv_expNegSq (y : ℝ) :
    deriv (fun (x : ℝ) => exp (-x * x)) y = exp (-y * y) * (-2 * y) :=
  HasDerivAt.deriv (hasDerivAt_expNegSq y)

theorem differentiableAt_mulExpNegSq (y : ℝ) :
    DifferentiableAt ℝ (fun x => x * exp (-x * x)) y := by
  simp only [differentiableAt_id', differentiableAt_expNegSq, DifferentiableAt.mul]

theorem differentiable_mulExpNegSq : Differentiable ℝ (fun x => x * exp (-x * x)) :=
  fun _ => differentiableAt_mulExpNegSq _

theorem hasDerivAt_mulExpNegSq (y : ℝ) :
    HasDerivAt (fun x => x * exp (-x * x)) (exp (-y * y) + y * (exp (-y * y) * (-2 * y))) y := by
  nth_rw 1 [← one_mul (exp (-y * y))]
  exact HasDerivAt.mul (hasDerivAt_id' y) (hasDerivAt_expNegSq y)

theorem deriv_mulExpNegSq (y : ℝ) : deriv (fun x => x * exp (- x * x)) y =
    exp (-y * y) + y * (exp (-y * y) * (-2 * y)) :=
  HasDerivAt.deriv (hasDerivAt_mulExpNegSq y)

theorem deriv_mulExpNegMulSq_one (x : ℝ) : deriv (mulExpNegMulSq 1) x =
    exp (-x * x) + x * (exp (-x * x) * (-2 * x)) := by
  rw [← deriv_mulExpNegSq]
  exact EventuallyEq.deriv_eq (Eventually.of_forall (mulExpNegSq_one))

theorem nnnorm_deriv_mulExpNegMulSq_one_le_one (x : ℝ) : ‖deriv (mulExpNegMulSq 1) x‖₊ ≤ 1 := by
  rw [← NNReal.coe_le_coe, coe_nnnorm, norm_eq_abs, deriv_mulExpNegMulSq_one]
  have heq : exp (-x * x) + x * (exp (-x * x) * (-2 * x)) = exp (-x * x) * (1 + 2 * -x * x) := by
    ring
  rw [heq, abs_mul, abs_exp]
  set y := x * x with hy
  rw [neg_mul, mul_assoc, neg_mul, ← hy]
  apply mul_le_of_le_inv_mul₀ (zero_le_one' ℝ) (exp_nonneg _)
  simp [← exp_neg (-y), abs_le]
  constructor
  · have twomul_le_exp : 2 * y ≤ exp y := by
      apply le_trans _ exp_one_mul_le_exp
      have : 2 ≤ exp 1 := by
        apply le_of_lt (lt_trans _ exp_one_gt_d9)
        norm_num
      apply mul_le_mul_of_nonneg_right this (mul_self_nonneg x)
    exact le_trans twomul_le_exp ((le_add_iff_nonneg_right (exp y)).mpr zero_le_one)
  · apply le_trans (one_le_exp (mul_self_nonneg x)) (le_add_of_nonneg_right _)
    simp [hy, (mul_self_nonneg x)]

theorem lipschitzWith_one_mulExpNegMulSq_one : LipschitzWith 1 (mulExpNegMulSq 1) :=
  lipschitzWith_of_nnnorm_deriv_le (Differentiable.mul differentiable_id' (by simp))
    nnnorm_deriv_mulExpNegMulSq_one_le_one

end mulExpNegMulSq

section mulExpNegMulSq_comp

/-! ### Properties of `(mulExpNegMulSq ε).comp g` -/

variable {E : Type*} {g : E → ℝ} {ε : ℝ} {x : E}

/--
`mulExpNegMulSq ε` transforms a function `g` into another function with useful
boundedness and convergence properties.
-/

theorem mulExpNegMulSq_eq_sqrt_mul_mulExpNegMulSq_one (hε : ε > 0) :
    (mulExpNegMulSq ε).comp g x
    = ε.sqrt⁻¹ * mulExpNegMulSq 1 (sqrt ε * g x) := by
  simp [mulExpNegMulSq]
  have h : ε.sqrt * g x * (ε.sqrt * g x) = ε * g x * g x := by
    ring_nf
    rw [sq_sqrt hε.le, mul_comm]
  rw [h, eq_inv_mul_iff_mul_eq₀ _]
  · ring_nf
  · intro h
    rw [← pow_eq_zero_iff (Ne.symm (Nat.zero_ne_add_one 1)), sq_sqrt hε.le] at h
    linarith

/-- if `ε > 0`, then `(mulExpNegMulSq ε).comp g` is bounded by `ε.sqrt⁻¹` -/
theorem abs_mulExpNegMulSq_comp_le (hε : ε > 0) : |(mulExpNegMulSq ε).comp g x| ≤ ε.sqrt⁻¹ := by
  rw [mulExpNegMulSq_eq_sqrt_mul_mulExpNegMulSq_one hε, abs_mul,
    abs_of_pos (inv_pos.mpr (sqrt_pos_of_pos hε))]
  nth_rw 2 [← mul_one ε.sqrt⁻¹]
  rw [mul_le_mul_left (inv_pos.mpr (sqrt_pos_of_pos hε))]
  exact abs_mulExpNegMulSq_one_le_one (ε.sqrt * g x)

theorem dist_mulExpNegMulSq_comp_le_two_mul_sqrt (hε : ε > 0) (x y : E) :
    dist ((mulExpNegMulSq ε).comp g x) ((mulExpNegMulSq ε).comp g y) ≤ 2 * ε.sqrt⁻¹ := by
  apply le_trans (dist_triangle ((mulExpNegMulSq ε).comp g x) 0 ((mulExpNegMulSq ε).comp g y))
  simp only [dist_zero_right, norm_eq_abs, dist_zero_left, two_mul]
  exact add_le_add (abs_mulExpNegMulSq_comp_le hε) (abs_mulExpNegMulSq_comp_le hε)

theorem dist_mulExpNegMulSq_comp_le_dist {f : E → ℝ} (hε : ε > 0) :
    dist ((mulExpNegMulSq ε).comp g x) ((mulExpNegMulSq ε).comp f x) ≤ dist (g x) (f x) := by
  simp only [ge_iff_le,
    mulExpNegMulSq_eq_sqrt_mul_mulExpNegMulSq_one hε, dist_eq]
  rw [← mul_sub_left_distrib ε.sqrt⁻¹ _ _, abs_mul,
    abs_of_pos (inv_pos_of_pos (sqrt_pos_of_pos hε)), ← one_mul (abs (g x - f x))]
  rw [← inv_mul_cancel₀ (ne_of_gt (sqrt_pos_of_pos hε)), mul_assoc]
  rw [mul_le_mul_left (inv_pos_of_pos (sqrt_pos_of_pos hε))]
  rw [inv_mul_cancel₀ (ne_of_gt (sqrt_pos_of_pos hε))]
  have hlip := lipschitzWith_one_mulExpNegMulSq_one (ε.sqrt * g x) (ε.sqrt * f x)
  rw [ENNReal.coe_one, one_mul, ← (toReal_le_toReal (edist_ne_top _ _) (edist_ne_top _ _))] at hlip
  apply le_trans (hlip) (le_of_eq _)
  nth_rewrite 3 [← abs_of_pos (sqrt_pos_of_pos hε)]
  rw [← abs_mul, mul_sub_left_distrib ε.sqrt _ _]
  exact rfl

/--
For fixed function `g`, `(mulExpNegMulSq ε).comp g` converges pointwise to `g`, as `ε → 0`.
-/
theorem tendsto_mulExpNegMulSq_comp :
    Tendsto (fun ε => (mulExpNegMulSq ε).comp g x) (nhds 0) (nhds (g x)) := by
  have : g x = (fun ε : ℝ => (mulExpNegMulSq ε).comp g x) 0 := by
    simp [mulExpNegMulSq]
  rw [this]
  apply Continuous.tendsto (Continuous.mul continuous_const _)
  apply (Continuous.rexp (Continuous.neg _))
  exact Continuous.mul (Continuous.mul continuous_id' (continuous_const)) continuous_const

variable [TopologicalSpace E]

/-- If the function `g` is continuous, `(mulExpNegMulSq ε).comp g` is continuous. -/
@[continuity]
theorem continuous_mulExpNegMulSq_comp (hg: Continuous g) :
    Continuous ((mulExpNegMulSq ε).comp g) :=
  Continuous.mul hg (Continuous.rexp (Continuous.neg (Continuous.mul
      (Continuous.mul continuous_const hg) hg)))

/--
For a fixed bounded function `g`, `(mulExpNegMulSq ε).comp g` is bounded by `norm g`, uniformly in
`ε ≥ 0`.
-/
theorem abs_mulExpNegMulSq_comp_le_norm (g : BoundedContinuousFunction E ℝ) (hε : ε ≥ 0) :
    |(mulExpNegMulSq ε).comp g x| ≤ ‖g‖ := by
  simp only [Function.comp_apply, mulExpNegMulSq, abs_mul, abs_exp]
  apply le_trans (mul_le_of_le_one_right (abs_nonneg (g x)) _) (g.norm_coe_le_norm x)
  rw [exp_le_one_iff, Left.neg_nonpos_iff, mul_assoc]
  exact mul_nonneg hε (mul_self_nonneg (g x))

end mulExpNegMulSq_comp

end Real
