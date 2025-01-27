/-
Copyright (c) 2024 Jakob Stiefel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Stiefel
-/
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Definition of `mulExpNegSq`, `mulExpNegMulSq` and properties

The mapping mulExpNegMulSq transforms a function `g` into another function
`mulExpNegMulSq g ε : fun x => g x * Real.exp (-ε * g x * g x)`.

## Main Properties

- `abs_mulExpNegMulSq_le`: For fixed `ε > 0`, the mapping `mulExpNegMulSq g ε` is bounded by
  `Real.sqrt ε⁻¹` uniformly in `g`;
- `tendsto_mulExpNegMulSq`: For fixed function `g`, the mapping `mulExpNegMulSq g ε`
  converges pointwise to `g` as `ε → 0`;
- `continuous_mulExpNegMulSq`: If the function `g` is continuous, the function `mulExpNegMulSq g ε`
  is continuous;
- `abs_mulExpNegMulSq_le_norm`: For a fixed bounded continuous function `g`, the mapping
  `mulExpNegMulSq g ε` is bounded by `norm g`, uniformly in `ε ≥ 0`;
-/

open NNReal ENNReal BoundedContinuousFunction Filter

namespace Real

section mulExpNegSq

/-! ### Definition and properties of `fun x => x * Real.exp (- x * x)`-/

/--
`mulExpNegSq` is the bounded function `fun x => x * Real.exp (- x * x)`. It can be used to transform
functions into bounded functions, see `MulExpNegMulSq`.
-/
noncomputable
def mulExpNegSq (x : ℝ) := x * exp (- x * x)

theorem mulExpNegSq_apply (x : ℝ) : mulExpNegSq x = x * exp (- x * x) :=  rfl

theorem neg_mulExpNegSq_neg (x : ℝ) : - mulExpNegSq (-x) = mulExpNegSq x  := by
  simp only [mulExpNegSq, neg_mul, neg_neg, mul_neg]

theorem mulExpNegSq_le_one (x : ℝ) : mulExpNegSq x ≤ 1 := by
  rw [mulExpNegSq_apply, neg_mul, ← le_div_iff₀ (exp_pos (-(x * x))), exp_neg,
    div_inv_eq_mul, one_mul]
  apply le_trans _ (add_one_le_exp (x * x))
  nlinarith

theorem abs_mulExpNegSq_le_one (x : ℝ) : |mulExpNegSq x| ≤ 1 := by
  apply abs_le.mpr ⟨_, mulExpNegSq_le_one x⟩
  rw [← neg_mulExpNegSq_neg, neg_le_neg_iff]
  exact mulExpNegSq_le_one (-x)

theorem deriv_expNegSq (y : ℝ) :
    deriv (fun (x : ℝ) => exp (-x * x)) y = -2 * y * exp (-y * y) := by
  simp only [neg_mul, differentiableAt_neg_iff, differentiableAt_id', DifferentiableAt.mul,
    _root_.deriv_exp, deriv.neg', deriv_mul, deriv_id'', one_mul, mul_one, neg_add_rev]
  ring

theorem expNegSq_differentiableAt (y : ℝ) :
    DifferentiableAt ℝ (fun (x : ℝ) => exp (-x * x)) y := by
  simp only [neg_mul, differentiableAt_neg_iff, differentiableAt_id', DifferentiableAt.mul,
    DifferentiableAt.exp, implies_true]

theorem expNegSq_differentiable : Differentiable ℝ (fun (x : ℝ) => exp (-x * x)) :=
  fun _ => expNegSq_differentiableAt _

theorem deriv_mulExpNegSq (x : ℝ) : deriv (fun x => x * exp (- x * x)) x =
    exp (-x * x) + x * (-2 * x * exp (-x * x)) := by
  nth_rw 1 [← one_mul (exp (-x * x)), ← (deriv_id x)]
  rw [← deriv_expNegSq x]
  apply deriv_mul differentiableAt_id' (expNegSq_differentiableAt x)

theorem deriv_mulExpNegSq_le_one (x : ℝ) : ‖deriv (fun y ↦ y * exp (-y * y)) x‖₊ ≤ 1 := by
  rw [← NNReal.coe_le_coe, coe_nnnorm, norm_eq_abs, deriv_mulExpNegSq x]
  have heq : exp (-x * x) + x * (-2 * x * exp (-x * x)) = exp (-x * x) * (1 + 2 * -x * x) := by
    ring
  rw [heq, abs_mul, abs_exp]
  let y := x * x
  have hy : y = x * x := by rfl
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
    apply le_trans twomul_le_exp _
    simp only [le_add_iff_nonneg_right, zero_le_one]
  · apply le_trans (one_le_exp (mul_self_nonneg x)) (le_add_of_nonneg_right _)
    simp [hy, (mul_self_nonneg x)]

theorem mulExpNegSq_lipschitzWith_one : LipschitzWith 1 mulExpNegSq := by
  apply lipschitzWith_of_nnnorm_deriv_le
      (Differentiable.mul differentiable_id' expNegSq_differentiable) deriv_mulExpNegSq_le_one

end mulExpNegSq

section mulExpNegMulSq

/-! ### Definition and properties of `mulExpNegMulSq g ε` -/

variable {E: Type*}

/--
`mulExpNegMulSq` transforms a function `g` into another function with useful
boundedness and convergence properties.
-/
noncomputable
def mulExpNegMulSq (g : E → ℝ) (ε : ℝ) : E → ℝ := (fun x => (g x) * exp (- (ε * (g x) * (g x))))

theorem mulExpNegMulSq_eq_sqrt_mul_mulExpNegSq {g : E → ℝ} {x : E} {ε : ℝ} (hε : ε > 0) :
    (g x) * (exp (- (ε * (g x) * (g x))))
    = ε.sqrt⁻¹ * mulExpNegSq (sqrt ε * (g x)) := by
  simp only [neg_mul, one_div, mulExpNegSq]
  have h : ((ε.sqrt * g x * (ε.sqrt * g x))) = ε * (g x) * (g x) := by
    ring_nf
    rw [sq_sqrt hε.le, mul_comm]
  rw [h, eq_inv_mul_iff_mul_eq₀ _]
  · ring_nf
  · intro h
    rw [← pow_eq_zero_iff (Ne.symm (Nat.zero_ne_add_one 1)), sq_sqrt hε.le] at h
    linarith

/-- if `ε > 0`, then `mulExpNegMulSq g` is bounded by `ε.sqrt⁻¹` -/
theorem abs_mulExpNegMulSq_le {g : E → ℝ} {ε : ℝ} (hε : ε > 0)
    (x : E) : abs (mulExpNegMulSq g ε x) ≤ ε.sqrt⁻¹ := by
  simp [mulExpNegMulSq]
  rw [mulExpNegMulSq_eq_sqrt_mul_mulExpNegSq hε, abs_mul,
    abs_of_pos (inv_pos.mpr (sqrt_pos_of_pos hε))]
  nth_rw 2 [← mul_one ε.sqrt⁻¹]
  rw [mul_le_mul_left (inv_pos.mpr (sqrt_pos_of_pos hε))]
  exact abs_mulExpNegSq_le_one (ε.sqrt * g x)

theorem dist_mulExpNegMulSq_le_two_mul_sqrt {g : E → ℝ} {ε : ℝ} (hε : ε > 0) (x y : E) :
    dist (mulExpNegMulSq g ε x) (mulExpNegMulSq g ε y) ≤ 2 * ε.sqrt⁻¹ := by
  apply le_trans (dist_triangle (mulExpNegMulSq g ε x) 0 (mulExpNegMulSq g ε y))
  simp only [dist_zero_right, norm_eq_abs, dist_zero_left, two_mul]
  exact add_le_add (abs_mulExpNegMulSq_le hε x) (abs_mulExpNegMulSq_le hε y)

theorem dist_mulExpNegMulSq_le_dist {f g : E → ℝ} {ε : ℝ} (hε : ε > 0) (x : E) :
    dist (mulExpNegMulSq g ε x) (mulExpNegMulSq f ε x) ≤ dist (g x) (f x) := by
  simp only [mulExpNegMulSq, ge_iff_le,
    mulExpNegMulSq_eq_sqrt_mul_mulExpNegSq hε, dist_eq]
  rw [← mul_sub_left_distrib ε.sqrt⁻¹ _ _, abs_mul,
    abs_of_pos (inv_pos_of_pos (sqrt_pos_of_pos hε)), ← one_mul (abs ((g x) - (f x)))]
  rw [← inv_mul_cancel₀ (ne_of_gt (sqrt_pos_of_pos hε)), mul_assoc]
  rw [mul_le_mul_left (inv_pos_of_pos (sqrt_pos_of_pos hε))]
  have hlip := mulExpNegSq_lipschitzWith_one (ε.sqrt * g x) (ε.sqrt * f x)
  rw [ENNReal.coe_one, one_mul, ← (toReal_le_toReal (edist_ne_top _ _) (edist_ne_top _ _))] at hlip
  apply le_trans (hlip) _
  have h : (edist (ε.sqrt * g x) (ε.sqrt * f x)).toReal
      = abs ((ε.sqrt * g x) - (ε.sqrt * f x)) := rfl
  rw [h, ← mul_sub_left_distrib ε.sqrt _ _, abs_mul, abs_of_pos (sqrt_pos_of_pos hε)]

/--
For fixed function `g`, the mapping `mulExpNegMulSq g ε` converges pointwise to `g`, as `ε → 0`.
-/
theorem tendsto_mulExpNegMulSq {g : E → ℝ} (x : E) :
    Tendsto (fun ε => mulExpNegMulSq g ε x) (nhds 0) (nhds (g x)) := by
  have : g x = (fun ε : ℝ => mulExpNegMulSq g ε x) 0 := by
    simp only [mulExpNegMulSq, zero_mul, neg_zero, exp_zero, mul_one]
  rw [this]
  apply Continuous.tendsto
  continuity

variable [TopologicalSpace E]

/-- If the function `g` is continuous, the function `mulExpNegMulSq g ε` is continuous. -/
@[continuity]
theorem continuous_mulExpNegMulSq {g : E → ℝ} {ε : ℝ} (hg: Continuous g) :
    Continuous (mulExpNegMulSq g ε) :=
  Continuous.mul hg (Continuous.rexp (Continuous.neg (Continuous.mul
      (Continuous.mul continuous_const hg) hg)))

/--
For a fixed bounded function `g`, the mapping `mulExpNegMulSq g ε` is bounded by `norm g`,
uniformly in `ε ≥ 0`.
-/
theorem abs_mulExpNegMulSq_le_norm (g : BoundedContinuousFunction E ℝ) {ε : ℝ} (hε : ε ≥ 0)
    (x : E) : |(mulExpNegMulSq g ε) x| ≤ ‖g‖ := by
  simp only [mulExpNegMulSq, ContinuousMap.coe_mk, abs_mul, abs_exp]
  apply le_trans (mul_le_of_le_one_right (abs_nonneg (g x)) _) (g.norm_coe_le_norm x)
  rw [exp_le_one_iff, Left.neg_nonpos_iff, mul_assoc]
  exact mul_nonneg hε (mul_self_nonneg (g x))

end mulExpNegMulSq

end Real
