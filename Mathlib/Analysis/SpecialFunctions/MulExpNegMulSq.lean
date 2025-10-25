/-
Copyright (c) 2024 Jakob Stiefel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Stiefel
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Definition of `mulExpNegMulSq` and properties

`mulExpNegMulSq` is the mapping `fun (ε : ℝ) (x : ℝ) => x * Real.exp (- (ε * x * x))`. By
composition, it can be used to transform a function `g : E → ℝ` into a bounded function
`mulExpNegMulSq ε ∘ g : E → ℝ = fun x => g x * Real.exp (-ε * g x * g x)` with useful
boundedness and convergence properties.

## Main Properties

- `abs_mulExpNegMulSq_le`: For fixed `ε > 0`, the mapping `x ↦ mulExpNegMulSq ε x` is
  bounded by `Real.sqrt ε⁻¹`;
- `tendsto_mulExpNegMulSq`: For fixed `x : ℝ`, the mapping `mulExpNegMulSq ε x`
  converges pointwise to `x` as `ε → 0`;
- `lipschitzWith_one_mulExpNegMulSq`: For fixed `ε > 0`, the mapping `mulExpNegMulSq ε` is
  Lipschitz with constant `1`;
- `abs_mulExpNegMulSq_comp_le_norm`: For a fixed bounded continuous function `g`, the mapping
  `mulExpNegMulSq ε ∘ g` is bounded by `norm g`, uniformly in `ε ≥ 0`;
-/

open NNReal ENNReal BoundedContinuousFunction Filter

open scoped Topology

namespace Real

/-! ### Definition and properties of `fun x => x * Real.exp (- (ε * x * x))` -/

/--
Mapping `fun ε x => x * Real.exp (- (ε * x * x))`. By composition, it can be used to transform
functions into bounded functions.
-/
noncomputable
def mulExpNegMulSq (ε x : ℝ) := x * exp (- (ε * x * x))

theorem mulExpNegSq_apply (ε x : ℝ) : mulExpNegMulSq ε x = x * exp (- (ε * x * x)) := rfl

theorem neg_mulExpNegMulSq_neg (ε x : ℝ) : - mulExpNegMulSq ε (-x) = mulExpNegMulSq ε x := by
  simp [mulExpNegMulSq]

theorem mulExpNegMulSq_one_le_one (x : ℝ) : mulExpNegMulSq 1 x ≤ 1 := by
  simp only [mulExpNegMulSq, one_mul]
  rw [← le_div_iff₀ (exp_pos (-(x * x))), exp_neg, div_inv_eq_mul, one_mul]
  apply le_trans _ (add_one_le_exp (x * x))
  nlinarith

theorem neg_one_le_mulExpNegMulSq_one (x : ℝ) : -1 ≤ mulExpNegMulSq 1 x := by
  rw [← neg_mulExpNegMulSq_neg, neg_le_neg_iff]
  exact mulExpNegMulSq_one_le_one (-x)

theorem abs_mulExpNegMulSq_one_le_one (x : ℝ) : |mulExpNegMulSq 1 x| ≤ 1 :=
  abs_le.mpr ⟨neg_one_le_mulExpNegMulSq_one x, mulExpNegMulSq_one_le_one x⟩

variable {ε : ℝ}

@[continuity, fun_prop]
theorem continuous_mulExpNegMulSq : Continuous (fun x => mulExpNegMulSq ε x) :=
  Continuous.mul continuous_id (by fun_prop)

@[continuity, fun_prop]
theorem _root_.Continuous.mulExpNegMulSq {α : Type*} [TopologicalSpace α] {f : α → ℝ}
    (hf : Continuous f) : Continuous (fun x => mulExpNegMulSq ε (f x)) :=
  continuous_mulExpNegMulSq.comp hf

theorem differentiableAt_mulExpNegMulSq (y : ℝ) :
    DifferentiableAt ℝ (mulExpNegMulSq ε) y :=
  DifferentiableAt.mul differentiableAt_fun_id (by fun_prop)

@[fun_prop] theorem differentiable_mulExpNegMulSq : Differentiable ℝ (mulExpNegMulSq ε) :=
  fun _ => differentiableAt_mulExpNegMulSq _

theorem hasDerivAt_mulExpNegMulSq (y : ℝ) :
    HasDerivAt (mulExpNegMulSq ε)
    (exp (- (ε * y * y)) + y * (exp (- (ε * y * y)) * (-2 * ε * y))) y := by
  nth_rw 1 [← one_mul (exp (- (ε * y * y)))]
  apply HasDerivAt.mul (hasDerivAt_id' y)
  apply HasDerivAt.exp (HasDerivAt.congr_deriv (HasDerivAt.neg
    (HasDerivAt.mul (HasDerivAt.const_mul ε (hasDerivAt_id' y)) (hasDerivAt_id' y))) (by ring))

theorem deriv_mulExpNegMulSq (y : ℝ) : deriv (mulExpNegMulSq ε) y =
    exp (- (ε * y * y)) + y * (exp (- (ε * y * y)) * (-2 * ε * y)) :=
  HasDerivAt.deriv (hasDerivAt_mulExpNegMulSq y)

theorem norm_deriv_mulExpNegMulSq_le_one (hε : 0 < ε) (x : ℝ) :
    ‖deriv (mulExpNegMulSq ε) x‖ ≤ 1 := by
  rw [norm_eq_abs, deriv_mulExpNegMulSq]
  have heq : exp (- (ε * x * x)) + x * (exp (- (ε * x * x)) * (-2 * ε * x))
      = exp (- (ε * x * x)) * (1 -2 * (ε * x * x)) := by ring
  rw [heq, abs_mul, abs_exp]
  set y := ε * x * x with hy
  have hynonneg : 0 ≤ y := by
    rw [hy, mul_assoc]
    exact mul_nonneg hε.le (mul_self_nonneg x)
  apply mul_le_of_le_inv_mul₀ (zero_le_one' ℝ) (exp_nonneg _)
  simp only [← exp_neg (-y), neg_neg, mul_one, abs_le, neg_le_sub_iff_le_add, tsub_le_iff_right]
  refine ⟨le_trans two_mul_le_exp ((le_add_iff_nonneg_left (exp y)).mpr zero_le_one), ?_⟩
  exact le_trans (one_le_exp hynonneg) (le_add_of_nonneg_right (by simp [hynonneg]))

theorem nnnorm_deriv_mulExpNegMulSq_le_one (hε : 0 < ε) (x : ℝ) :
    ‖deriv (mulExpNegMulSq ε) x‖₊ ≤ 1 := by
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  exact norm_deriv_mulExpNegMulSq_le_one hε x

/-- For fixed `ε > 0`, the mapping `mulExpNegMulSq ε` is Lipschitz with constant `1` -/
theorem lipschitzWith_one_mulExpNegMulSq (hε : 0 < ε) :
    LipschitzWith 1 (mulExpNegMulSq ε) := by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_mulExpNegMulSq
  exact nnnorm_deriv_mulExpNegMulSq_le_one hε

theorem mulExpNegMulSq_eq_sqrt_mul_mulExpNegMulSq_one (hε : 0 < ε) (x : ℝ) :
    mulExpNegMulSq ε x = (√ε)⁻¹ * mulExpNegMulSq 1 (sqrt ε * x) := by
  grind [mulExpNegMulSq]

/-- For fixed `ε > 0`, the mapping `x ↦ mulExpNegMulSq ε x` is bounded by `(√ε)⁻¹ -/
theorem abs_mulExpNegMulSq_le (hε : 0 < ε) {x : ℝ} : |mulExpNegMulSq ε x| ≤ (√ε)⁻¹ := by
  rw [mulExpNegMulSq_eq_sqrt_mul_mulExpNegMulSq_one hε x, abs_mul, abs_of_pos (by positivity)]
  apply mul_le_of_le_one_right
  · positivity
  · exact abs_mulExpNegMulSq_one_le_one (√ε * x)

theorem dist_mulExpNegMulSq_le_two_mul_sqrt (hε : 0 < ε) (x y : ℝ) :
    dist (mulExpNegMulSq ε x) (mulExpNegMulSq ε y) ≤ 2 * (√ε)⁻¹ := by
  apply le_trans (dist_triangle (mulExpNegMulSq ε x) 0 (mulExpNegMulSq ε y))
  simp only [dist_zero_right, norm_eq_abs, dist_zero_left, two_mul]
  exact add_le_add (abs_mulExpNegMulSq_le hε) (abs_mulExpNegMulSq_le hε)

theorem dist_mulExpNegMulSq_le_dist (hε : 0 < ε) {x y : ℝ} :
    dist (mulExpNegMulSq ε x) (mulExpNegMulSq ε y) ≤ dist x y := by
  have h := lipschitzWith_one_mulExpNegMulSq hε x y
  rwa [ENNReal.coe_one, one_mul, ← (toReal_le_toReal (edist_ne_top _ _) (edist_ne_top _ _))] at h

/-- For fixed `x : ℝ`, the mapping `mulExpNegMulSq ε x` converges pointwise to `x` as `ε → 0` -/
theorem tendsto_mulExpNegMulSq {x : ℝ} :
    Tendsto (fun ε => mulExpNegMulSq ε x) (𝓝 0) (𝓝 x) := by
  have : x = (fun ε : ℝ => mulExpNegMulSq ε x) 0 := by
    simp only [mulExpNegMulSq, zero_mul, neg_zero, exp_zero, mul_one]
  nth_rw 2 [this]
  apply Continuous.tendsto (Continuous.mul continuous_const (by fun_prop))

/-- For a fixed bounded function `g`, `mulExpNegMulSq ε ∘ g` is bounded by `norm g`,
uniformly in `ε ≥ 0`. -/
theorem abs_mulExpNegMulSq_comp_le_norm {E : Type*} [TopologicalSpace E] {x : E}
    (g : BoundedContinuousFunction E ℝ) (hε : 0 ≤ ε) :
    |(mulExpNegMulSq ε ∘ g) x| ≤ ‖g‖ := by
  simp only [Function.comp_apply, mulExpNegMulSq, abs_mul, abs_exp]
  apply le_trans (mul_le_of_le_one_right (abs_nonneg (g x)) _) (g.norm_coe_le_norm x)
  rw [exp_le_one_iff, Left.neg_nonpos_iff, mul_assoc]
  exact mul_nonneg hε (mul_self_nonneg (g x))

end Real
