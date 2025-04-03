/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Eric Wieser
-/
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.InfiniteSum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Topology.Algebra.Algebra

#align_import analysis.normed_space.exponential from "leanprover-community/mathlib"@"62748956a1ece9b26b33243e2e3a2852176666f5"

/-!
# Exponential in a Banach algebra

In this file, we define `exp : 𝔸 → 𝔸`, the exponential map in a topological algebra `𝔸` over the
field `ℚ`.

While for most interesting results we need `𝔸` to be normed algebra, we do not require this in the
definition in order to make `exp` independent of a particular choice of norm. The definition also
does not require that `𝔸` be complete, but we need to assume it for most results.

We then prove some basic results, but we avoid importing derivatives here to minimize dependencies.
Results involving derivatives and comparisons with `Real.exp` and `Complex.exp` can be found in
`Analysis.SpecialFunctions.Exponential`.

## Main results

We prove most result for an arbitrary field `𝕂`, and then specialize to `𝕂 = ℝ` or `𝕂 = ℂ`.

### General case

- `NormedSpace.exp_add_of_commute_of_mem_ball` : if `𝕂` has characteristic zero,
  then given two commuting elements `x` and `y` in the disk of convergence, we have
  `exp (x+y) = (exp x) * (exp y)`
- `NormedSpace.exp_add_of_mem_ball` : if `𝕂` has characteristic zero and `𝔸` is commutative,
  then given two elements `x` and `y` in the disk of convergence, we have
  `exp (x+y) = (exp x) * (exp y)`
- `NormedSpace.exp_neg_of_mem_ball` : if `𝕂` has characteristic zero and `𝔸` is a division ring,
  then given an element `x` in the disk of convergence, we have `exp (-x) = (exp x)⁻¹`.

### `𝕂 = ℝ` or `𝕂 = ℂ`

- `expSeries_radius_eq_top` : the `FormalMultilinearSeries` defining `exp` has infinite
  radius of convergence
- `NormedSpace.exp_add_of_commute` : given two commuting elements `x` and `y`, we have
  `exp (x+y) = (exp x) * (exp y)`
- `NormedSpace.exp_add` : if `𝔸` is commutative, then we have `exp (x+y) = (exp x) * (exp y)`
  for any `x` and `y`
- `NormedSpace.exp_neg` : if `𝔸` is a division ring, then we have `exp (-x) = (exp x)⁻¹`.
- `exp_sum_of_commute` : the analogous result to `NormedSpace.exp_add_of_commute` for `Finset.sum`.
- `exp_sum` : the analogous result to `NormedSpace.exp_add` for `Finset.sum`.
- `NormedSpace.exp_nsmul` : repeated addition in the domain corresponds to
  repeated multiplication in the codomain.
- `NormedSpace.exp_zsmul` : repeated addition in the domain corresponds to
  repeated multiplication in the codomain.

### Notes

We put nearly all the statements in this file in the `NormedSpace` namespace,
to avoid collisions with the `Real` or `Complex` namespaces.

As of 2023-11-16 due to bad instances in Mathlib
```
import Mathlib

open Real

#time example (x : ℝ) : 0 < exp x      := exp_pos _ -- 250ms
#time example (x : ℝ) : 0 < Real.exp x := exp_pos _ -- 2ms
```
This is because `exp x` tries the `NormedSpace.exp` function defined here,
and generates a slow coercion search from `Real` to `Type`, to fit the first argument here.
We will resolve this slow coercion separately,
but we want to move `exp` out of the root namespace in any case to avoid this ambiguity.

In the long term is may be possible to replace `Real.exp` and `Complex.exp` with this one.

-/


namespace NormedSpace

open Filter RCLike ContinuousMultilinearMap NormedField Asymptotics

open scoped Nat Topology ENNReal

section TopologicalAlgebra

variable (𝕂 𝔸 : Type*) [Field 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [TopologicalRing 𝔸]

/-- `expSeries 𝕂 𝔸` is the `FormalMultilinearSeries` whose `n`-th term is the map
`(xᵢ) : 𝔸ⁿ ↦ (1/n! : 𝕂) • ∏ xᵢ`. Its sum is the exponential map `exp : 𝔸 → 𝔸`. -/
def expSeries : FormalMultilinearSeries 𝕂 𝔸 𝔸 := fun n =>
  (n !⁻¹ : 𝕂) • ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸
#align exp_series NormedSpace.expSeries

variable {𝔸}

/-- `exp : 𝔸 → 𝔸` is the exponential map determined by the action of `𝕂` on `𝔸`.
It is defined as the sum of the `FormalMultilinearSeries` `expSeries 𝕂 𝔸`.

Note that when `𝔸 = Matrix n n 𝕂`, this is the **Matrix Exponential**; see
[`Analysis.NormedSpace.MatrixExponential`](./MatrixExponential) for lemmas specific to that
case. -/
noncomputable def exp [Algebra ℚ 𝔸] (x : 𝔸) : 𝔸 :=
  (expSeries ℚ 𝔸).sum x
#align exp NormedSpace.exp

variable {𝕂}

theorem expSeries_apply_eq (x : 𝔸) (n : ℕ) :
    (expSeries 𝕂 𝔸 n fun _ => x) = (n !⁻¹ : 𝕂) • x ^ n := by simp [expSeries]
#align exp_series_apply_eq NormedSpace.expSeries_apply_eq

variable (𝕂) in
theorem expSeries_apply_eq' (x : 𝔸) :
    (fun n => expSeries 𝕂 𝔸 n fun _ => x) = fun n => (n !⁻¹ : 𝕂) • x ^ n :=
  funext (expSeries_apply_eq x)
#align exp_series_apply_eq' NormedSpace.expSeries_apply_eq'

theorem expSeries_sum_eq (x : 𝔸) : (expSeries 𝕂 𝔸).sum x = ∑' n : ℕ, (n !⁻¹ : 𝕂) • x ^ n :=
  tsum_congr fun n => expSeries_apply_eq x n
#align exp_series_sum_eq NormedSpace.expSeries_sum_eq

theorem expSeries_sum_eq_rat [Algebra ℚ 𝔸] : (expSeries 𝕂 𝔸).sum = (expSeries ℚ 𝔸).sum := by
  ext; simp_rw [expSeries_sum_eq, inv_nat_cast_smul_eq 𝕂 ℚ]
#align exp_series_sum_eq_rat NormedSpace.expSeries_sum_eq_rat

variable (𝕂) in
theorem expSeries_eq_expSeries_rat [Algebra ℚ 𝔸] (n : ℕ) :
    ⇑(expSeries 𝕂 𝔸 n) = expSeries ℚ 𝔸 n:= by
  ext c
  simp [expSeries, inv_nat_cast_smul_eq 𝕂 ℚ]
#align exp_series_eq_exp_series_rat NormedSpace.expSeries_eq_expSeries_rat

theorem exp_eq_tsum [Algebra ℚ 𝔸] : exp = fun x : 𝔸 => ∑' n : ℕ, (n !⁻¹ : ℚ) • x ^ n :=
  funext expSeries_sum_eq
#align exp_eq_tsum NormedSpace.exp_eq_tsum

theorem expSeries_apply_zero (n : ℕ) :
    (expSeries 𝕂 𝔸 n fun _ => (0 : 𝔸)) = Pi.single (f := fun _ => 𝔸) 0 1 n := by
  rw [expSeries_apply_eq]
  cases' n with n
  · rw [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, Pi.single_eq_same]
  · rw [zero_pow (Nat.succ_ne_zero _), smul_zero, Pi.single_eq_of_ne n.succ_ne_zero]
#align exp_series_apply_zero NormedSpace.expSeries_apply_zero

@[simp]
theorem exp_zero [Algebra ℚ 𝔸] : exp (0 : 𝔸) = 1 := by
  simp_rw [exp_eq_tsum, ← expSeries_apply_eq, expSeries_apply_zero, tsum_pi_single]
#align exp_zero NormedSpace.exp_zero

@[simp]
theorem exp_op [Algebra ℚ 𝔸] [T2Space 𝔸] (x : 𝔸) :
    exp (MulOpposite.op x) = MulOpposite.op (exp x) := by
  simp_rw [exp, expSeries_sum_eq, ← MulOpposite.op_pow, ← MulOpposite.op_smul, tsum_op]
#align exp_op NormedSpace.exp_op

@[simp]
theorem exp_unop [Algebra ℚ 𝔸] [T2Space 𝔸] (x : 𝔸ᵐᵒᵖ) :
    exp (MulOpposite.unop x) = MulOpposite.unop (exp x) := by
  simp_rw [exp, expSeries_sum_eq, ← MulOpposite.unop_pow, ← MulOpposite.unop_smul, tsum_unop]
#align exp_unop NormedSpace.exp_unop

theorem star_exp [Algebra ℚ 𝔸] [T2Space 𝔸] [StarRing 𝔸] [ContinuousStar 𝔸] (x : 𝔸) :
    star (exp x) = exp (star x) := by
  simp_rw [exp_eq_tsum, ← star_pow, ← star_inv_nat_cast_smul, ← tsum_star]
#align star_exp NormedSpace.star_exp

variable (𝕂)

theorem _root_.IsSelfAdjoint.exp [Algebra ℚ 𝔸] [T2Space 𝔸] [StarRing 𝔸] [ContinuousStar 𝔸] {x : 𝔸}
    (h : IsSelfAdjoint x) : IsSelfAdjoint (exp x) :=
  (star_exp x).trans <| h.symm ▸ rfl
#align is_self_adjoint.exp IsSelfAdjoint.exp

theorem _root_.Commute.exp_right [Algebra ℚ 𝔸] [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) :
    Commute x (exp y) := by
  rw [exp_eq_tsum]
  exact Commute.tsum_right x fun n => (h.pow_right n).smul_right _
#align commute.exp_right Commute.exp_right

theorem _root_.Commute.exp_left [Algebra ℚ 𝔸] [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) :
    Commute (exp x) y :=
  h.symm.exp_right.symm
#align commute.exp_left Commute.exp_left

theorem _root_.Commute.exp [Algebra ℚ 𝔸] [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) :
    Commute (exp x) (exp y) :=
  h.exp_left.exp_right
#align commute.exp Commute.exp

end TopologicalAlgebra

section TopologicalDivisionAlgebra

variable {𝕂 𝔸 : Type*} [Field 𝕂] [DivisionRing 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸]
  [TopologicalRing 𝔸]

theorem expSeries_apply_eq_div (x : 𝔸) (n : ℕ) : (expSeries 𝕂 𝔸 n fun _ => x) = x ^ n / n ! := by
  rw [div_eq_mul_inv, ← (Nat.cast_commute n ! (x ^ n)).inv_left₀.eq, ← smul_eq_mul,
    expSeries_apply_eq, inv_natCast_smul_eq 𝕂 𝔸]
#align exp_series_apply_eq_div NormedSpace.expSeries_apply_eq_div

theorem expSeries_apply_eq_div' (x : 𝔸) :
    (fun n => expSeries 𝕂 𝔸 n fun _ => x) = fun n => x ^ n / n ! :=
  funext (expSeries_apply_eq_div x)
#align exp_series_apply_eq_div' NormedSpace.expSeries_apply_eq_div'

theorem expSeries_sum_eq_div (x : 𝔸) : (expSeries 𝕂 𝔸).sum x = ∑' n : ℕ, x ^ n / n ! :=
  tsum_congr (expSeries_apply_eq_div x)
#align exp_series_sum_eq_div NormedSpace.expSeries_sum_eq_div

theorem exp_eq_tsum_div [Algebra ℚ 𝔸] : exp = fun x : 𝔸 => ∑' n : ℕ, x ^ n / n ! :=
  funext expSeries_sum_eq_div
#align exp_eq_tsum_div NormedSpace.exp_eq_tsum_div

end TopologicalDivisionAlgebra

section Normed

section AnyFieldAnyAlgebra

variable {𝕂 𝔸 𝔹 : Type*} [NontriviallyNormedField 𝕂]
variable [NormedRing 𝔸] [NormedRing 𝔹] [NormedAlgebra 𝕂 𝔸]

theorem norm_expSeries_summable_of_mem_ball (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => ‖expSeries 𝕂 𝔸 n fun _ => x‖ :=
  (expSeries 𝕂 𝔸).summable_norm_apply hx
#align norm_exp_series_summable_of_mem_ball NormedSpace.norm_expSeries_summable_of_mem_ball

theorem norm_expSeries_summable_of_mem_ball' [Algebra ℚ 𝔸] (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => ‖(n !⁻¹ : ℚ) • x ^ n‖ := by
  change Summable (norm ∘ _)
  rw [← expSeries_apply_eq']
  convert norm_expSeries_summable_of_mem_ball x hx
  simp_rw [expSeries_eq_expSeries_rat, Function.comp_apply]
#align norm_exp_series_summable_of_mem_ball' NormedSpace.norm_expSeries_summable_of_mem_ball'

section CompleteAlgebra

variable [CompleteSpace 𝔸]

theorem expSeries_summable_of_mem_ball (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => expSeries 𝕂 𝔸 n fun _ => x :=
  (norm_expSeries_summable_of_mem_ball x hx).of_norm
#align exp_series_summable_of_mem_ball NormedSpace.expSeries_summable_of_mem_ball

theorem expSeries_summable_of_mem_ball' [Algebra ℚ 𝔸] (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => (n !⁻¹ : ℚ) • x ^ n :=
  (norm_expSeries_summable_of_mem_ball' x hx).of_norm
#align exp_series_summable_of_mem_ball' NormedSpace.expSeries_summable_of_mem_ball'

theorem expSeries_hasSum_exp_of_mem_ball [Algebra ℚ 𝔸] (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasSum (fun n => expSeries 𝕂 𝔸 n fun _ => x) (exp x) := by
  simpa only [exp, expSeries_sum_eq_rat] using FormalMultilinearSeries.hasSum (expSeries 𝕂 𝔸) hx
#align exp_series_has_sum_exp_of_mem_ball NormedSpace.expSeries_hasSum_exp_of_mem_ball

theorem expSeries_hasSum_exp_of_mem_ball' [Algebra ℚ 𝔸] (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasSum (fun n => (n !⁻¹ : 𝕂) • x ^ n) (exp x) := by
  rw [← expSeries_apply_eq']
  exact expSeries_hasSum_exp_of_mem_ball x hx
#align exp_series_has_sum_exp_of_mem_ball' NormedSpace.expSeries_hasSum_exp_of_mem_ball'

theorem hasFPowerSeriesOnBall_exp_of_radius_pos [Algebra ℚ 𝔸] (h : 0 < (expSeries 𝕂 𝔸).radius) :
    HasFPowerSeriesOnBall exp (expSeries 𝕂 𝔸) 0 (expSeries 𝕂 𝔸).radius := by
  simpa only [exp, expSeries_sum_eq_rat] using (expSeries 𝕂 𝔸).hasFPowerSeriesOnBall h
#align has_fpower_series_on_ball_exp_of_radius_pos NormedSpace.hasFPowerSeriesOnBall_exp_of_radius_pos

theorem hasFPowerSeriesAt_exp_zero_of_radius_pos [Algebra ℚ 𝔸] (h : 0 < (expSeries 𝕂 𝔸).radius) :
    HasFPowerSeriesAt exp (expSeries 𝕂 𝔸) 0 := by
  simpa only [exp, expSeries_sum_eq_rat] using
  (hasFPowerSeriesOnBall_exp_of_radius_pos h).hasFPowerSeriesAt
#align has_fpower_series_at_exp_zero_of_radius_pos NormedSpace.hasFPowerSeriesAt_exp_zero_of_radius_pos

theorem continuousOn_exp [Algebra ℚ 𝔸] :
    ContinuousOn (exp : 𝔸 → 𝔸) (EMetric.ball 0 (expSeries 𝕂 𝔸).radius) := by
  have := @FormalMultilinearSeries.continuousOn _ _ _ _ _ _ _ _ (expSeries 𝕂 𝔸)
  simpa only [exp, expSeries_sum_eq_rat] using this
#align continuous_on_exp NormedSpace.continuousOn_exp

theorem analyticAt_exp_of_mem_ball [Algebra ℚ 𝔸] (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : AnalyticAt 𝕂 exp x := by
  by_cases h : (expSeries 𝕂 𝔸).radius = 0
  · rw [h] at hx; exact (ENNReal.not_lt_zero hx).elim
  · have h := pos_iff_ne_zero.mpr h
    exact (hasFPowerSeriesOnBall_exp_of_radius_pos h).analyticAt_of_mem hx
#align analytic_at_exp_of_mem_ball NormedSpace.analyticAt_exp_of_mem_ball

variable (𝕂)

/-- In a Banach-algebra `𝔸` over a normed field `𝕂` of characteristic zero, if `x` and `y` are
in the disk of convergence and commute, then `exp (x + y) = (exp x) * (exp y)`. -/
theorem exp_add_of_commute_of_mem_ball [Algebra ℚ 𝔸] {x y : 𝔸} (hxy : Commute x y)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius)
    (hy : y ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : exp (x + y) = exp x * exp y := by
  rw [exp_eq_tsum,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
      (norm_expSeries_summable_of_mem_ball' x hx) (norm_expSeries_summable_of_mem_ball' y hy)]
  dsimp only
  conv_lhs =>
    congr
    ext
    rw [hxy.add_pow' _, Finset.smul_sum]
  refine tsum_congr fun n => Finset.sum_congr rfl fun kl hkl => ?_
  rw [nsmul_eq_smul_cast ℚ, smul_smul, smul_mul_smul, ← Finset.mem_antidiagonal.mp hkl,
    Nat.cast_add_choose, Finset.mem_antidiagonal.mp hkl]
  congr 1
  have : (n ! : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp [this]
#align exp_add_of_commute_of_mem_ball NormedSpace.exp_add_of_commute_of_mem_ball

/-- `exp x` has explicit two-sided inverse `exp (-x)`. -/
noncomputable def invertibleExpOfMemBall [Algebra ℚ 𝔸] {x : 𝔸}
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : Invertible (exp x)
    where
  invOf := exp (-x)
  invOf_mul_self := by
    have hnx : -x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius := by
      rw [EMetric.mem_ball, ← neg_zero, edist_neg_neg]
      exact hx
    rw [← exp_add_of_commute_of_mem_ball _ (Commute.neg_left <| Commute.refl x) hnx hx,
      neg_add_self, exp_zero]
  mul_invOf_self := by
    have hnx : -x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius := by
      rw [EMetric.mem_ball, ← neg_zero, edist_neg_neg]
      exact hx
    rw [← exp_add_of_commute_of_mem_ball _ (Commute.neg_right <| Commute.refl x) hx hnx,
      add_neg_self, exp_zero]
#align invertible_exp_of_mem_ball NormedSpace.invertibleExpOfMemBall

theorem isUnit_exp_of_mem_ball [Algebra ℚ 𝔸] {x : 𝔸}
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : IsUnit (exp x) :=
  @isUnit_of_invertible _ _ _ (invertibleExpOfMemBall _ hx)
#align is_unit_exp_of_mem_ball NormedSpace.isUnit_exp_of_mem_ball

theorem invOf_exp_of_mem_ball [Algebra ℚ 𝔸] {x : 𝔸}
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) [Invertible (exp x)] :
    ⅟ (exp x) = exp (-x) := by
  letI := invertibleExpOfMemBall _ hx; convert (rfl : ⅟ (exp x) = _)
#align inv_of_exp_of_mem_ball NormedSpace.invOf_exp_of_mem_ball

/-- Any continuous ring homomorphism commutes with `exp`. -/
theorem map_exp_of_mem_ball [Algebra ℚ 𝔸] [Algebra ℚ 𝔹] {F} [FunLike F 𝔸 𝔹] [RingHomClass F 𝔸 𝔹]
    (f : F) (hf : Continuous f) (x : 𝔸) (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    f (exp x) = exp (f x) := by
  rw [exp_eq_tsum, exp_eq_tsum]
  refine ((expSeries_summable_of_mem_ball' _ hx).hasSum.map f hf).tsum_eq.symm.trans ?_
  dsimp only [Function.comp_def]
  simp_rw [map_inv_natCast_smul f ℚ ℚ, map_pow]
#align map_exp_of_mem_ball NormedSpace.map_exp_of_mem_ball

end CompleteAlgebra

theorem algebraMap_exp_comm_of_mem_ball [Algebra ℚ 𝔸] [CharZero 𝕂] [CompleteSpace 𝕂] (x : 𝕂)
    (hx : x ∈ EMetric.ball (0 : 𝕂) (expSeries 𝕂 𝕂).radius) :
    algebraMap 𝕂 𝔸 (exp x) = exp (algebraMap 𝕂 𝔸 x) :=
  map_exp_of_mem_ball _ (algebraMap _ _) (algebraMapCLM _ _).continuous _ hx
#align algebra_map_exp_comm_of_mem_ball NormedSpace.algebraMap_exp_comm_of_mem_ball

end AnyFieldAnyAlgebra

section AnyFieldDivisionAlgebra

variable {𝕂 𝔸 : Type*} [NontriviallyNormedField 𝕂] [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸]
variable (𝕂)

theorem norm_expSeries_div_summable_of_mem_ball (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : Summable fun n => ‖x ^ n / (n !)‖ := by
  change Summable (norm ∘ _)
  rw [← expSeries_apply_eq_div' (𝕂 := 𝕂) x]
  exact norm_expSeries_summable_of_mem_ball x hx
#align norm_exp_series_div_summable_of_mem_ball NormedSpace.norm_expSeries_div_summable_of_mem_ball

theorem expSeries_div_summable_of_mem_ball [CompleteSpace 𝔸] (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : Summable fun n => x ^ n / n ! :=
  (norm_expSeries_div_summable_of_mem_ball 𝕂 x hx).of_norm
#align exp_series_div_summable_of_mem_ball NormedSpace.expSeries_div_summable_of_mem_ball

theorem expSeries_div_hasSum_exp_of_mem_ball [Algebra ℚ 𝔸] [CompleteSpace 𝔸] (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasSum (fun n => x ^ n / n !) (exp x) := by
  rw [← expSeries_apply_eq_div' (𝕂 := 𝕂) x]
  exact expSeries_hasSum_exp_of_mem_ball x hx
#align exp_series_div_has_sum_exp_of_mem_ball NormedSpace.expSeries_div_hasSum_exp_of_mem_ball

theorem exp_neg_of_mem_ball [Algebra ℚ 𝔸] [CompleteSpace 𝔸] {x : 𝔸}
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : exp (-x) = (exp x)⁻¹ :=
  letI := invertibleExpOfMemBall _ hx
  invOf_eq_inv (exp x)
#align exp_neg_of_mem_ball NormedSpace.exp_neg_of_mem_ball

end AnyFieldDivisionAlgebra

section AnyFieldCommAlgebra

variable {𝕂 𝔸 : Type*} [NontriviallyNormedField 𝕂] [NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸]

variable (𝕂)

/-- In a commutative Banach-algebra `𝔸` over a normed field `𝕂` of characteristic zero,
`exp (x+y) = (exp x) * (exp y)` for all `x`, `y` in the disk of convergence. -/
theorem exp_add_of_mem_ball [Algebra ℚ 𝔸] {x y : 𝔸}
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius)
    (hy : y ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : exp (x + y) = exp x * exp y :=
  exp_add_of_commute_of_mem_ball 𝕂 (Commute.all x y) hx hy
#align exp_add_of_mem_ball NormedSpace.exp_add_of_mem_ball

end AnyFieldCommAlgebra

section RCLike

section AnyAlgebra

variable (𝕂 𝔸 𝔹 : Type*) [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
variable [NormedRing 𝔹]

/-- In a normed algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, the series defining the exponential map
has an infinite radius of convergence. -/
theorem expSeries_radius_eq_top : (expSeries 𝕂 𝔸).radius = ∞ := by
  refine (expSeries 𝕂 𝔸).radius_eq_top_of_summable_norm fun r => ?_
  refine .of_norm_bounded_eventually _ (Real.summable_pow_div_factorial r) ?_
  filter_upwards [eventually_cofinite_ne 0] with n hn
  rw [norm_mul, norm_norm (expSeries 𝕂 𝔸 n), expSeries]
  rw [norm_smul (n ! : 𝕂)⁻¹ (ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸)]
  -- Porting note: Lean needed this to be explicit for some reason
  rw [norm_inv, norm_pow, NNReal.norm_eq, norm_natCast, mul_comm, ← mul_assoc, ← div_eq_mul_inv]
  have : ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸‖ ≤ 1 :=
    norm_mkPiAlgebraFin_le_of_pos (Ei := fun _ => 𝔸) (Nat.pos_of_ne_zero hn)
  exact mul_le_of_le_one_right (div_nonneg (pow_nonneg r.coe_nonneg n) n !.cast_nonneg) this
#align exp_series_radius_eq_top NormedSpace.expSeries_radius_eq_top

theorem expSeries_radius_pos : 0 < (expSeries 𝕂 𝔸).radius := by
  rw [expSeries_radius_eq_top]
  exact WithTop.zero_lt_top
#align exp_series_radius_pos NormedSpace.expSeries_radius_pos

variable {𝕂 𝔸 𝔹}

theorem norm_expSeries_summable (x : 𝔸) : Summable fun n => ‖expSeries 𝕂 𝔸 n fun _ => x‖ :=
  norm_expSeries_summable_of_mem_ball x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
#align norm_exp_series_summable NormedSpace.norm_expSeries_summable

variable (𝕂)

theorem norm_expSeries_summable' [Algebra ℚ 𝔸] (x : 𝔸) : Summable fun n => ‖(n !⁻¹ : ℚ) • x ^ n‖ :=
  norm_expSeries_summable_of_mem_ball' x
    (show x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius from
      (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
#align norm_exp_series_summable' NormedSpace.norm_expSeries_summable'

variable {𝕂}

section CompleteAlgebra

variable [CompleteSpace 𝔸]

theorem expSeries_summable (x : 𝔸) : Summable fun n => expSeries 𝕂 𝔸 n fun _ => x :=
  (norm_expSeries_summable x).of_norm
#align exp_series_summable NormedSpace.expSeries_summable

variable (𝕂) in
theorem expSeries_summable' [Algebra ℚ 𝔸] (x : 𝔸) : Summable fun n => (n !⁻¹ : ℚ) • x ^ n :=
  (norm_expSeries_summable' 𝕂 x).of_norm
#align exp_series_summable' NormedSpace.expSeries_summable'

variable [Algebra ℚ 𝔸] [Algebra ℚ 𝔹]

theorem expSeries_hasSum_exp (x : 𝔸) : HasSum (fun n => expSeries 𝕂 𝔸 n fun _ => x) (exp x) :=
  expSeries_hasSum_exp_of_mem_ball x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
#align exp_series_has_sum_exp NormedSpace.expSeries_hasSum_exp

theorem exp_series_hasSum_exp' (x : 𝔸) : HasSum (fun n => (n !⁻¹ : 𝕂) • x ^ n) (exp x) :=
  expSeries_hasSum_exp_of_mem_ball' x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
#align exp_series_has_sum_exp' NormedSpace.exp_series_hasSum_exp'

theorem exp_hasFPowerSeriesOnBall : HasFPowerSeriesOnBall exp (expSeries 𝕂 𝔸) 0 ∞ :=
  expSeries_radius_eq_top 𝕂 𝔸 ▸ hasFPowerSeriesOnBall_exp_of_radius_pos (expSeries_radius_pos _ _)
#align exp_has_fpower_series_on_ball NormedSpace.exp_hasFPowerSeriesOnBall

theorem exp_hasFPowerSeriesAt_zero : HasFPowerSeriesAt exp (expSeries 𝕂 𝔸) 0 :=
  exp_hasFPowerSeriesOnBall.hasFPowerSeriesAt
#align exp_has_fpower_series_at_zero NormedSpace.exp_hasFPowerSeriesAt_zero

section
variable (𝕂)

@[continuity]
theorem exp_continuous : Continuous (exp : 𝔸 → 𝔸) := by
  rw [continuous_iff_continuousOn_univ, ← Metric.eball_top_eq_univ (0 : 𝔸), ←
    expSeries_radius_eq_top 𝕂 𝔸]
  exact continuousOn_exp
#align exp_continuous NormedSpace.exp_continuous

open Topology in
lemma _root_.Filter.Tendsto.exp {α : Type*} {l : Filter α} {f : α → 𝔸} {a : 𝔸}
    (hf : Tendsto f l (𝓝 a)) :
    Tendsto (fun x => exp (f x)) l (𝓝 (exp a)) :=
  (exp_continuous 𝕂 |>.tendsto _).comp hf

end

theorem exp_analytic (x : 𝔸) : AnalyticAt 𝕂 exp x :=
  analyticAt_exp_of_mem_ball x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
#align exp_analytic NormedSpace.exp_analytic

variable (𝕂)

/-- In a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, if `x` and `y` commute, then
`exp (x+y) = (exp x) * (exp y)`. -/
theorem exp_add_of_commute {x y : 𝔸} (hxy : Commute x y) : exp (x + y) = exp x * exp y :=
  exp_add_of_commute_of_mem_ball 𝕂 hxy ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
#align exp_add_of_commute NormedSpace.exp_add_of_commute

section

/-- `exp x` has explicit two-sided inverse `exp (-x)`. -/
noncomputable def invertibleExp (x : 𝔸) : Invertible (exp x) :=
  invertibleExpOfMemBall 𝕂 <| (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _
#align invertible_exp NormedSpace.invertibleExp

theorem isUnit_exp (x : 𝔸) : IsUnit (exp x) :=
  isUnit_exp_of_mem_ball 𝕂 <| (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _
#align is_unit_exp NormedSpace.isUnit_exp

theorem invOf_exp (x : 𝔸) [Invertible (exp x)] : ⅟ (exp x) = exp (-x) :=
  invOf_exp_of_mem_ball 𝕂 <| (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _
#align inv_of_exp NormedSpace.invOf_exp

theorem _root_.Ring.inverse_exp (x : 𝔸) : Ring.inverse (exp x) = exp (-x) :=
  letI := invertibleExp 𝕂 x
  Ring.inverse_invertible _
#align ring.inverse_exp Ring.inverse_exp

theorem exp_mem_unitary_of_mem_skewAdjoint [StarRing 𝔸] [ContinuousStar 𝔸] {x : 𝔸}
    (h : x ∈ skewAdjoint 𝔸) : exp x ∈ unitary 𝔸 := by
  rw [unitary.mem_iff, star_exp, skewAdjoint.mem_iff.mp h, ←
    exp_add_of_commute 𝕂 (Commute.refl x).neg_left, ←
    exp_add_of_commute 𝕂 (Commute.refl x).neg_right, add_left_neg, add_right_neg, exp_zero,
    and_self_iff]
#align exp_mem_unitary_of_mem_skew_adjoint NormedSpace.exp_mem_unitary_of_mem_skewAdjoint

end

/-- In a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, if a family of elements `f i` mutually
commute then `exp (∑ i, f i) = ∏ i, exp (f i)`. -/
theorem exp_sum_of_commute {ι} (s : Finset ι) (f : ι → 𝔸)
    (h : (s : Set ι).Pairwise fun i j => Commute (f i) (f j)) :
    exp (∑ i ∈ s, f i) =
      s.noncommProd (fun i => exp (f i)) fun i hi j hj _ => (h.of_refl hi hj).exp := by
  classical
    induction' s using Finset.induction_on with a s ha ih
    · simp
    rw [Finset.noncommProd_insert_of_not_mem _ _ _ _ ha, Finset.sum_insert ha, exp_add_of_commute 𝕂,
      ih (h.mono <| Finset.subset_insert _ _)]
    refine Commute.sum_right _ _ _ fun i hi => ?_
    exact h.of_refl (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hi)
#align exp_sum_of_commute NormedSpace.exp_sum_of_commute

theorem exp_nsmul (n : ℕ) (x : 𝔸) : exp (n • x) = exp x ^ n := by
  induction' n with n ih
  · rw [zero_smul, pow_zero, exp_zero]
  · rw [succ_nsmul, pow_succ, exp_add_of_commute 𝕂 ((Commute.refl x).smul_left n), ih]
#align exp_nsmul NormedSpace.exp_nsmul

/-- Any continuous ring homomorphism commutes with `NormedSpace.exp`. -/
theorem map_exp {F} [FunLike F 𝔸 𝔹] [RingHomClass F 𝔸 𝔹] (f : F) (hf : Continuous f) (x : 𝔸) :
    f (exp x) = exp (f x) :=
  map_exp_of_mem_ball 𝕂 f hf x <| (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _
#align map_exp NormedSpace.map_exp

theorem exp_smul {G} [Monoid G] [MulSemiringAction G 𝔸] [ContinuousConstSMul G 𝔸] (g : G) (x : 𝔸) :
    exp (g • x) = g • exp x :=
  (map_exp 𝕂 (MulSemiringAction.toRingHom G 𝔸 g) (continuous_const_smul g) x).symm
#align exp_smul NormedSpace.exp_smul

theorem exp_units_conj (y : 𝔸ˣ) (x : 𝔸) : exp (y * x * ↑y⁻¹ : 𝔸) = y * exp x * ↑y⁻¹ :=
  exp_smul 𝕂 (ConjAct.toConjAct y) x
#align exp_units_conj NormedSpace.exp_units_conj

theorem exp_units_conj' (y : 𝔸ˣ) (x : 𝔸) : exp (↑y⁻¹ * x * y) = ↑y⁻¹ * exp x * y :=
  exp_units_conj 𝕂 _ _
#align exp_units_conj' NormedSpace.exp_units_conj'

-- @[simp]
theorem _root_.Prod.fst_exp [NormedAlgebra 𝕂 𝔹] [CompleteSpace 𝔹] (x : 𝔸 × 𝔹) :
    (exp x).fst = exp x.fst :=
  map_exp 𝕂 (RingHom.fst 𝔸 𝔹) continuous_fst x
#align prod.fst_exp Prod.fst_exp

-- @[simp]
theorem _root_.Prod.snd_exp [NormedAlgebra 𝕂 𝔹] [CompleteSpace 𝔹] (x : 𝔸 × 𝔹) :
    (exp x).snd = exp x.snd :=
  map_exp 𝕂 (RingHom.snd 𝔸 𝔹) continuous_snd x
#align prod.snd_exp Prod.snd_exp

-- @[simp]
theorem _root_.Pi.exp_apply {ι : Type*} {𝔸 : ι → Type*} [Fintype ι] [∀ i, NormedRing (𝔸 i)]
    [∀ i, Algebra ℚ (𝔸 i)] [∀ i, NormedAlgebra 𝕂 (𝔸 i)] [∀ i, CompleteSpace (𝔸 i)] (x : ∀ i, 𝔸 i)
    (i : ι) :
    exp x i = exp (x i) :=
  -- porting note: Lean can now handle Π-types in type class inference!
  map_exp 𝕂 (Pi.evalRingHom 𝔸 i) (continuous_apply _) x
#align pi.exp_apply Pi.exp_apply

theorem _root_.Pi.exp_def {ι : Type*} {𝔸 : ι → Type*} [Fintype ι] [∀ i, NormedRing (𝔸 i)]
    [∀ i, NormedAlgebra 𝕂 (𝔸 i)] [∀ i, Algebra ℚ (𝔸 i)] [∀ i, CompleteSpace (𝔸 i)] (x : ∀ i, 𝔸 i) :
    exp x = fun i => exp (x i) :=
  funext <| Pi.exp_apply 𝕂 x
#align pi.exp_def Pi.exp_def

theorem _root_.Function.update_exp {ι : Type*} {𝔸 : ι → Type*} [Fintype ι] [DecidableEq ι]
    [∀ i, NormedRing (𝔸 i)] [∀ i, Algebra ℚ (𝔸 i)] [∀ i, NormedAlgebra 𝕂 (𝔸 i)]
    [∀ i, CompleteSpace (𝔸 i)] (x : ∀ i, 𝔸 i) (j : ι) (xj : 𝔸 j) :
    Function.update (exp x) j (exp xj) = exp (Function.update x j xj) := by
  ext i
  simp_rw [Pi.exp_def 𝕂]
  exact (Function.apply_update (fun i => exp) x j xj i).symm
#align function.update_exp Function.update_exp

end CompleteAlgebra

theorem algebraMap_exp_comm [Algebra ℚ 𝔸] (x : 𝕂) :
    algebraMap 𝕂 𝔸 (exp x) = exp (algebraMap 𝕂 𝔸 x) :=
  algebraMap_exp_comm_of_mem_ball x <| (expSeries_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _
#align algebra_map_exp_comm NormedSpace.algebraMap_exp_comm

end AnyAlgebra

section DivisionAlgebra

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸]
variable (𝕂)

theorem norm_expSeries_div_summable (x : 𝔸) : Summable fun n => ‖(x ^ n / n ! : 𝔸)‖ :=
  norm_expSeries_div_summable_of_mem_ball 𝕂 x
    ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
#align norm_exp_series_div_summable NormedSpace.norm_expSeries_div_summable

variable [CompleteSpace 𝔸]

theorem expSeries_div_summable (x : 𝔸) : Summable fun n => x ^ n / n ! :=
  (norm_expSeries_div_summable 𝕂 x).of_norm
#align exp_series_div_summable NormedSpace.expSeries_div_summable

variable [Algebra ℚ 𝔸]

theorem expSeries_div_hasSum_exp (x : 𝔸) : HasSum (fun n => x ^ n / n !) (exp x) :=
  expSeries_div_hasSum_exp_of_mem_ball 𝕂 x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
#align exp_series_div_has_sum_exp NormedSpace.expSeries_div_hasSum_exp

theorem exp_neg (x : 𝔸) : exp (-x) = (exp x)⁻¹ :=
  exp_neg_of_mem_ball 𝕂 <| (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _
#align exp_neg NormedSpace.exp_neg

theorem exp_zsmul (z : ℤ) (x : 𝔸) : exp (z • x) = exp x ^ z := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · rw [zpow_natCast, natCast_zsmul, exp_nsmul 𝕂]
  · rw [zpow_neg, zpow_natCast, neg_smul, exp_neg 𝕂, natCast_zsmul, exp_nsmul 𝕂]
#align exp_zsmul NormedSpace.exp_zsmul

theorem exp_conj (y : 𝔸) (x : 𝔸) (hy : y ≠ 0) : exp (y * x * y⁻¹) = y * exp x * y⁻¹ :=
  exp_units_conj 𝕂 (Units.mk0 y hy) x
#align exp_conj NormedSpace.exp_conj

theorem exp_conj' (y : 𝔸) (x : 𝔸) (hy : y ≠ 0) : exp (y⁻¹ * x * y) = y⁻¹ * exp x * y :=
  exp_units_conj' 𝕂 (Units.mk0 y hy) x
#align exp_conj' NormedSpace.exp_conj'

end DivisionAlgebra

section CommAlgebra

variable {𝕂 𝔸 : Type _} [RCLike 𝕂] [NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

variable [Algebra ℚ 𝔸]

/-- In a commutative Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`,
`exp (x+y) = (exp x) * (exp y)`. -/
theorem exp_add {x y : 𝔸} : exp (x + y) = exp x * exp y :=
  exp_add_of_mem_ball 𝕂 ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
#align exp_add NormedSpace.exp_add

/-- A version of `NormedSpace.exp_sum_of_commute` for a commutative Banach-algebra. -/
theorem exp_sum {ι} (s : Finset ι) (f : ι → 𝔸) : exp (∑ i ∈ s, f i) = ∏ i ∈ s, exp (f i) := by
  rw [exp_sum_of_commute 𝕂, Finset.noncommProd_eq_prod]
  exact fun i _hi j _hj _ => Commute.all _ _
#align exp_sum NormedSpace.exp_sum

end CommAlgebra

end RCLike

end Normed

section ScalarTower

variable (𝕂 𝕂' 𝔸 : Type*) [Field 𝕂] [Field 𝕂'] [Ring 𝔸] [Algebra 𝕂 𝔸] [Algebra 𝕂' 𝔸]
  [TopologicalSpace 𝔸] [TopologicalRing 𝔸]

/-- If a normed ring `𝔸` is a normed algebra over two fields, then they define the same
`expSeries` on `𝔸`. -/
theorem expSeries_eq_expSeries (n : ℕ) (x : 𝔸) :
    (expSeries 𝕂 𝔸 n fun _ => x) = expSeries 𝕂' 𝔸 n fun _ => x := by
  rw [expSeries_apply_eq, expSeries_apply_eq, inv_natCast_smul_eq 𝕂 𝕂']
#align exp_series_eq_exp_series NormedSpace.expSeries_eq_expSeries

/-- A version of `Complex.ofReal_exp` for `NormedSpace.exp` instead of `Complex.exp` -/
@[simp, norm_cast]
theorem of_real_exp_ℝ_ℝ (r : ℝ) : ↑(exp r) = exp (r : ℂ) :=
  map_exp ℝ (algebraMap ℝ ℂ) (continuous_algebraMap _ _) r
#align of_real_exp_ℝ_ℝ NormedSpace.of_real_exp_ℝ_ℝ

end ScalarTower
