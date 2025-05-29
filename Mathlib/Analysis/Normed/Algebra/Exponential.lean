/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Eric Wieser
-/
import Mathlib.Algebra.Ring.Action.ConjAct
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.SpecificLimits.RCLike

/-!
# Exponential in a Banach algebra

In this file, we define `NormedSpace.exp 𝕂 : 𝔸 → 𝔸`,
the exponential map in a topological algebra `𝔸` over a field `𝕂`.

While for most interesting results we need `𝔸` to be normed algebra, we do not require this in the
definition in order to make `NormedSpace.exp` independent of a particular choice of norm. The
definition also does not require that `𝔸` be complete, but we need to assume it for most results.

We then prove some basic results, but we avoid importing derivatives here to minimize dependencies.
Results involving derivatives and comparisons with `Real.exp` and `Complex.exp` can be found in
`Analysis.SpecialFunctions.Exponential`.

## Main results

We prove most result for an arbitrary field `𝕂`, and then specialize to `𝕂 = ℝ` or `𝕂 = ℂ`.

### General case

- `NormedSpace.exp_add_of_commute_of_mem_ball` : if `𝕂` has characteristic zero,
  then given two commuting elements `x` and `y` in the disk of convergence, we have
  `NormedSpace.exp 𝕂 (x+y) = (NormedSpace.exp 𝕂 x) * (NormedSpace.exp 𝕂 y)`
- `NormedSpace.exp_add_of_mem_ball` : if `𝕂` has characteristic zero and `𝔸` is commutative,
  then given two elements `x` and `y` in the disk of convergence, we have
  `NormedSpace.exp 𝕂 (x+y) = (NormedSpace.exp 𝕂 x) * (NormedSpace.exp 𝕂 y)`
- `NormedSpace.exp_neg_of_mem_ball` : if `𝕂` has characteristic zero and `𝔸` is a division ring,
  then given an element `x` in the disk of convergence,
  we have `NormedSpace.exp 𝕂 (-x) = (NormedSpace.exp 𝕂 x)⁻¹`.

### `𝕂 = ℝ` or `𝕂 = ℂ`

- `expSeries_radius_eq_top` : the `FormalMultilinearSeries` defining `NormedSpace.exp 𝕂`
  has infinite radius of convergence
- `NormedSpace.exp_add_of_commute` : given two commuting elements `x` and `y`, we have
  `NormedSpace.exp 𝕂 (x+y) = (NormedSpace.exp 𝕂 x) * (NormedSpace.exp 𝕂 y)`
- `NormedSpace.exp_add` : if `𝔸` is commutative, then we have
  `NormedSpace.exp 𝕂 (x+y) = (NormedSpace.exp 𝕂 x) * (NormedSpace.exp 𝕂 y)` for any `x` and `y`
- `NormedSpace.exp_neg` : if `𝔸` is a division ring, then we have
  `NormedSpace.exp 𝕂 (-x) = (NormedSpace.exp 𝕂 x)⁻¹`.
- `NormedSpace.exp_sum_of_commute` : the analogous result to `NormedSpace.exp_add_of_commute`
  for `Finset.sum`.
- `NormedSpace.exp_sum` : the analogous result to `NormedSpace.exp_add` for `Finset.sum`.
- `NormedSpace.exp_nsmul` : repeated addition in the domain corresponds to
  repeated multiplication in the codomain.
- `NormedSpace.exp_zsmul` : repeated addition in the domain corresponds to
  repeated multiplication in the codomain.

### Other useful compatibility results

- `NormedSpace.exp_eq_exp` : if `𝔸` is a normed algebra over two fields `𝕂` and `𝕂'`,
  then `NormedSpace.exp 𝕂 = NormedSpace.exp 𝕂' 𝔸`

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

open Filter RCLike ContinuousMultilinearMap NormedField Asymptotics FormalMultilinearSeries

open scoped Nat Topology ENNReal

section TopologicalAlgebra

variable (𝕂 𝔸 : Type*) [Field 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸]

/-- `expSeries 𝕂 𝔸` is the `FormalMultilinearSeries` whose `n`-th term is the map
`(xᵢ) : 𝔸ⁿ ↦ (1/n! : 𝕂) • ∏ xᵢ`. Its sum is the exponential map `NormedSpace.exp 𝕂 : 𝔸 → 𝔸`. -/
def expSeries : FormalMultilinearSeries 𝕂 𝔸 𝔸 := fun n =>
  (n !⁻¹ : 𝕂) • ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸

/-- The exponential series as an `ofScalars` series. -/
theorem expSeries_eq_ofScalars : expSeries 𝕂 𝔸 = ofScalars 𝔸 fun n ↦ (n !⁻¹ : 𝕂) := by
  simp_rw [FormalMultilinearSeries.ext_iff, expSeries, ofScalars, implies_true]

variable {𝔸}

/-- `NormedSpace.exp 𝕂 : 𝔸 → 𝔸` is the exponential map determined by the action of `𝕂` on `𝔸`.
It is defined as the sum of the `FormalMultilinearSeries` `expSeries 𝕂 𝔸`.

Note that when `𝔸 = Matrix n n 𝕂`, this is the **Matrix Exponential**; see
[`MatrixExponential`](./Mathlib/Analysis/Normed/Algebra/MatrixExponential) for lemmas
specific to that case. -/
noncomputable def exp (x : 𝔸) : 𝔸 :=
  (expSeries 𝕂 𝔸).sum x

variable {𝕂}

theorem expSeries_apply_eq (x : 𝔸) (n : ℕ) :
    (expSeries 𝕂 𝔸 n fun _ => x) = (n !⁻¹ : 𝕂) • x ^ n := by simp [expSeries]

theorem expSeries_apply_eq' (x : 𝔸) :
    (fun n => expSeries 𝕂 𝔸 n fun _ => x) = fun n => (n !⁻¹ : 𝕂) • x ^ n :=
  funext (expSeries_apply_eq x)

theorem expSeries_sum_eq (x : 𝔸) : (expSeries 𝕂 𝔸).sum x = ∑' n : ℕ, (n !⁻¹ : 𝕂) • x ^ n :=
  tsum_congr fun n => expSeries_apply_eq x n

theorem exp_eq_tsum : exp 𝕂 = fun x : 𝔸 => ∑' n : ℕ, (n !⁻¹ : 𝕂) • x ^ n :=
  funext expSeries_sum_eq

/-- The exponential sum as an `ofScalarsSum`. -/
theorem exp_eq_ofScalarsSum : exp 𝕂 = ofScalarsSum (E := 𝔸) fun n ↦ (n !⁻¹ : 𝕂) := by
  rw [exp_eq_tsum, ofScalarsSum_eq_tsum]

theorem expSeries_apply_zero (n : ℕ) :
    expSeries 𝕂 𝔸 n (fun _ => (0 : 𝔸)) = Pi.single (M := fun _ => 𝔸) 0 1 n := by
  rw [expSeries_apply_eq]
  rcases n with - | n
  · rw [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, Pi.single_eq_same]
  · rw [zero_pow (Nat.succ_ne_zero _), smul_zero, Pi.single_eq_of_ne n.succ_ne_zero]

@[simp]
theorem exp_zero : exp 𝕂 (0 : 𝔸) = 1 := by
  simp_rw [exp_eq_tsum, ← expSeries_apply_eq, expSeries_apply_zero, tsum_pi_single]

@[simp]
theorem exp_op [T2Space 𝔸] (x : 𝔸) : exp 𝕂 (MulOpposite.op x) = MulOpposite.op (exp 𝕂 x) := by
  simp_rw [exp, expSeries_sum_eq, ← MulOpposite.op_pow, ← MulOpposite.op_smul, tsum_op]

@[simp]
theorem exp_unop [T2Space 𝔸] (x : 𝔸ᵐᵒᵖ) :
    exp 𝕂 (MulOpposite.unop x) = MulOpposite.unop (exp 𝕂 x) := by
  simp_rw [exp, expSeries_sum_eq, ← MulOpposite.unop_pow, ← MulOpposite.unop_smul, tsum_unop]

theorem star_exp [T2Space 𝔸] [StarRing 𝔸] [ContinuousStar 𝔸] (x : 𝔸) :
    star (exp 𝕂 x) = exp 𝕂 (star x) := by
  simp_rw [exp_eq_tsum, ← star_pow, ← star_inv_natCast_smul, ← tsum_star]

variable (𝕂)

@[aesop safe apply]
theorem _root_.IsSelfAdjoint.exp [T2Space 𝔸] [StarRing 𝔸] [ContinuousStar 𝔸] {x : 𝔸}
    (h : IsSelfAdjoint x) : IsSelfAdjoint (exp 𝕂 x) :=
  (star_exp x).trans <| h.symm ▸ rfl

theorem _root_.Commute.exp_right [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) :
    Commute x (exp 𝕂 y) := by
  rw [exp_eq_tsum]
  exact Commute.tsum_right x fun n => (h.pow_right n).smul_right _

theorem _root_.Commute.exp_left [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) : Commute (exp 𝕂 x) y :=
  (h.symm.exp_right 𝕂).symm

theorem _root_.Commute.exp [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) : Commute (exp 𝕂 x) (exp 𝕂 y) :=
  (h.exp_left _).exp_right _

end TopologicalAlgebra

section TopologicalDivisionAlgebra

variable {𝕂 𝔸 : Type*} [Field 𝕂] [DivisionRing 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸]
  [IsTopologicalRing 𝔸]

theorem expSeries_apply_eq_div (x : 𝔸) (n : ℕ) : (expSeries 𝕂 𝔸 n fun _ => x) = x ^ n / n ! := by
  rw [div_eq_mul_inv, ← (Nat.cast_commute n ! (x ^ n)).inv_left₀.eq, ← smul_eq_mul,
    expSeries_apply_eq, inv_natCast_smul_eq 𝕂 𝔸]

theorem expSeries_apply_eq_div' (x : 𝔸) :
    (fun n => expSeries 𝕂 𝔸 n fun _ => x) = fun n => x ^ n / n ! :=
  funext (expSeries_apply_eq_div x)

theorem expSeries_sum_eq_div (x : 𝔸) : (expSeries 𝕂 𝔸).sum x = ∑' n : ℕ, x ^ n / n ! :=
  tsum_congr (expSeries_apply_eq_div x)

theorem exp_eq_tsum_div : exp 𝕂 = fun x : 𝔸 => ∑' n : ℕ, x ^ n / n ! :=
  funext expSeries_sum_eq_div

end TopologicalDivisionAlgebra

section Normed

section AnyFieldAnyAlgebra

variable {𝕂 𝔸 𝔹 : Type*} [NontriviallyNormedField 𝕂]
variable [NormedRing 𝔸] [NormedRing 𝔹] [NormedAlgebra 𝕂 𝔸] [NormedAlgebra 𝕂 𝔹]

theorem norm_expSeries_summable_of_mem_ball (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => ‖expSeries 𝕂 𝔸 n fun _ => x‖ :=
  (expSeries 𝕂 𝔸).summable_norm_apply hx

theorem norm_expSeries_summable_of_mem_ball' (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => ‖(n !⁻¹ : 𝕂) • x ^ n‖ := by
  change Summable (norm ∘ _)
  rw [← expSeries_apply_eq']
  exact norm_expSeries_summable_of_mem_ball x hx

section CompleteAlgebra

variable [CompleteSpace 𝔸]

theorem expSeries_summable_of_mem_ball (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => expSeries 𝕂 𝔸 n fun _ => x :=
  (norm_expSeries_summable_of_mem_ball x hx).of_norm

theorem expSeries_summable_of_mem_ball' (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => (n !⁻¹ : 𝕂) • x ^ n :=
  (norm_expSeries_summable_of_mem_ball' x hx).of_norm

theorem expSeries_hasSum_exp_of_mem_ball (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasSum (fun n => expSeries 𝕂 𝔸 n fun _ => x) (exp 𝕂 x) :=
  FormalMultilinearSeries.hasSum (expSeries 𝕂 𝔸) hx

theorem expSeries_hasSum_exp_of_mem_ball' (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasSum (fun n => (n !⁻¹ : 𝕂) • x ^ n) (exp 𝕂 x) := by
  rw [← expSeries_apply_eq']
  exact expSeries_hasSum_exp_of_mem_ball x hx

theorem hasFPowerSeriesOnBall_exp_of_radius_pos (h : 0 < (expSeries 𝕂 𝔸).radius) :
    HasFPowerSeriesOnBall (exp 𝕂) (expSeries 𝕂 𝔸) 0 (expSeries 𝕂 𝔸).radius :=
  (expSeries 𝕂 𝔸).hasFPowerSeriesOnBall h

theorem hasFPowerSeriesAt_exp_zero_of_radius_pos (h : 0 < (expSeries 𝕂 𝔸).radius) :
    HasFPowerSeriesAt (exp 𝕂) (expSeries 𝕂 𝔸) 0 :=
  (hasFPowerSeriesOnBall_exp_of_radius_pos h).hasFPowerSeriesAt

theorem continuousOn_exp : ContinuousOn (exp 𝕂 : 𝔸 → 𝔸) (EMetric.ball 0 (expSeries 𝕂 𝔸).radius) :=
  FormalMultilinearSeries.continuousOn

theorem analyticAt_exp_of_mem_ball (x : 𝔸) (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    AnalyticAt 𝕂 (exp 𝕂) x := by
  by_cases h : (expSeries 𝕂 𝔸).radius = 0
  · rw [h] at hx; exact (ENNReal.not_lt_zero hx).elim
  · have h := pos_iff_ne_zero.mpr h
    exact (hasFPowerSeriesOnBall_exp_of_radius_pos h).analyticAt_of_mem hx

/-- In a Banach-algebra `𝔸` over a normed field `𝕂` of characteristic zero, if `x` and `y` are
in the disk of convergence and commute, then
`NormedSpace.exp 𝕂 (x + y) = (NormedSpace.exp 𝕂 x) * (NormedSpace.exp 𝕂 y)`. -/
theorem exp_add_of_commute_of_mem_ball [CharZero 𝕂] {x y : 𝔸} (hxy : Commute x y)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius)
    (hy : y ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : exp 𝕂 (x + y) = exp 𝕂 x * exp 𝕂 y := by
  rw [exp_eq_tsum,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
      (norm_expSeries_summable_of_mem_ball' x hx) (norm_expSeries_summable_of_mem_ball' y hy)]
  dsimp only
  conv_lhs =>
    congr
    ext
    rw [hxy.add_pow' _, Finset.smul_sum]
  refine tsum_congr fun n => Finset.sum_congr rfl fun kl hkl => ?_
  rw [← Nat.cast_smul_eq_nsmul 𝕂, smul_smul, smul_mul_smul_comm, ← Finset.mem_antidiagonal.mp hkl,
    Nat.cast_add_choose, Finset.mem_antidiagonal.mp hkl]
  congr 1
  have : (n ! : 𝕂) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp [this]

/-- `NormedSpace.exp 𝕂 x` has explicit two-sided inverse `NormedSpace.exp 𝕂 (-x)`. -/
noncomputable def invertibleExpOfMemBall [CharZero 𝕂] {x : 𝔸}
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : Invertible (exp 𝕂 x) where
  invOf := exp 𝕂 (-x)
  invOf_mul_self := by
    have hnx : -x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius := by
      rw [EMetric.mem_ball, ← neg_zero, edist_neg_neg]
      exact hx
    rw [← exp_add_of_commute_of_mem_ball (Commute.neg_left <| Commute.refl x) hnx hx,
      neg_add_cancel, exp_zero]
  mul_invOf_self := by
    have hnx : -x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius := by
      rw [EMetric.mem_ball, ← neg_zero, edist_neg_neg]
      exact hx
    rw [← exp_add_of_commute_of_mem_ball (Commute.neg_right <| Commute.refl x) hx hnx,
      add_neg_cancel, exp_zero]

theorem isUnit_exp_of_mem_ball [CharZero 𝕂] {x : 𝔸}
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : IsUnit (exp 𝕂 x) :=
  @isUnit_of_invertible _ _ _ (invertibleExpOfMemBall hx)

theorem invOf_exp_of_mem_ball [CharZero 𝕂] {x : 𝔸}
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) [Invertible (exp 𝕂 x)] :
    ⅟ (exp 𝕂 x) = exp 𝕂 (-x) := by
  letI := invertibleExpOfMemBall hx; convert (rfl : ⅟ (exp 𝕂 x) = _)

/-- Any continuous ring homomorphism commutes with `NormedSpace.exp`. -/
theorem map_exp_of_mem_ball {F} [FunLike F 𝔸 𝔹] [RingHomClass F 𝔸 𝔹] (f : F) (hf : Continuous f)
    (x : 𝔸) (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    f (exp 𝕂 x) = exp 𝕂 (f x) := by
  rw [exp_eq_tsum, exp_eq_tsum]
  refine ((expSeries_summable_of_mem_ball' _ hx).hasSum.map f hf).tsum_eq.symm.trans ?_
  dsimp only [Function.comp_def]
  simp_rw [map_inv_natCast_smul f 𝕂 𝕂, map_pow]

end CompleteAlgebra

theorem algebraMap_exp_comm_of_mem_ball [CompleteSpace 𝕂] (x : 𝕂)
    (hx : x ∈ EMetric.ball (0 : 𝕂) (expSeries 𝕂 𝕂).radius) :
    algebraMap 𝕂 𝔸 (exp 𝕂 x) = exp 𝕂 (algebraMap 𝕂 𝔸 x) :=
  map_exp_of_mem_ball _ (continuous_algebraMap 𝕂 𝔸) _ hx

end AnyFieldAnyAlgebra

section AnyFieldDivisionAlgebra

variable {𝕂 𝔸 : Type*} [NontriviallyNormedField 𝕂] [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸]
variable (𝕂)

theorem norm_expSeries_div_summable_of_mem_ball (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => ‖x ^ n / (n ! : 𝔸)‖ := by
  change Summable (norm ∘ _)
  rw [← expSeries_apply_eq_div' (𝕂 := 𝕂) x]
  exact norm_expSeries_summable_of_mem_ball x hx

theorem expSeries_div_summable_of_mem_ball [CompleteSpace 𝔸] (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : Summable fun n => x ^ n / n ! :=
  (norm_expSeries_div_summable_of_mem_ball 𝕂 x hx).of_norm

theorem expSeries_div_hasSum_exp_of_mem_ball [CompleteSpace 𝔸] (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasSum (fun n => x ^ n / n !) (exp 𝕂 x) := by
  rw [← expSeries_apply_eq_div' (𝕂 := 𝕂) x]
  exact expSeries_hasSum_exp_of_mem_ball x hx

variable {𝕂}

theorem exp_neg_of_mem_ball [CharZero 𝕂] [CompleteSpace 𝔸] {x : 𝔸}
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : exp 𝕂 (-x) = (exp 𝕂 x)⁻¹ :=
  letI := invertibleExpOfMemBall hx
  invOf_eq_inv (exp 𝕂 x)

end AnyFieldDivisionAlgebra

section AnyFieldCommAlgebra

variable {𝕂 𝔸 : Type*} [NontriviallyNormedField 𝕂] [NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸]

/-- In a commutative Banach-algebra `𝔸` over a normed field `𝕂` of characteristic zero,
`NormedSpace.exp 𝕂 (x+y) = (NormedSpace.exp 𝕂 x) * (NormedSpace.exp 𝕂 y)`
for all `x`, `y` in the disk of convergence. -/
theorem exp_add_of_mem_ball [CharZero 𝕂] {x y : 𝔸}
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius)
    (hy : y ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : exp 𝕂 (x + y) = exp 𝕂 x * exp 𝕂 y :=
  exp_add_of_commute_of_mem_ball (Commute.all x y) hx hy

end AnyFieldCommAlgebra

section RCLike

section AnyAlgebra

variable (𝕂 𝔸 𝔹 : Type*) [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
variable [NormedRing 𝔹] [NormedAlgebra 𝕂 𝔹]

/-- In a normed algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, the series defining the exponential map
has an infinite radius of convergence. -/
theorem expSeries_radius_eq_top : (expSeries 𝕂 𝔸).radius = ∞ := by
  have {n : ℕ} : (Nat.factorial n : 𝕂) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  apply expSeries_eq_ofScalars 𝕂 𝔸 ▸
    ofScalars_radius_eq_top_of_tendsto 𝔸 _ (Eventually.of_forall fun n => ?_)
  · simp_rw [← norm_div, Nat.factorial_succ, Nat.cast_mul, mul_inv_rev, mul_div_right_comm,
      inv_div_inv, norm_mul, div_self this, norm_one, one_mul]
    apply norm_zero (E := 𝕂) ▸ Filter.Tendsto.norm
    apply (Filter.tendsto_add_atTop_iff_nat (f := fun n => (n : 𝕂)⁻¹) 1).mpr
    exact RCLike.tendsto_inverse_atTop_nhds_zero_nat 𝕂
  · simp [this]

theorem expSeries_radius_pos : 0 < (expSeries 𝕂 𝔸).radius := by
  rw [expSeries_radius_eq_top]
  exact WithTop.top_pos

variable {𝕂 𝔸 𝔹}

theorem norm_expSeries_summable (x : 𝔸) : Summable fun n => ‖expSeries 𝕂 𝔸 n fun _ => x‖ :=
  norm_expSeries_summable_of_mem_ball x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

theorem norm_expSeries_summable' (x : 𝔸) : Summable fun n => ‖(n !⁻¹ : 𝕂) • x ^ n‖ :=
  norm_expSeries_summable_of_mem_ball' x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

section CompleteAlgebra

variable [CompleteSpace 𝔸]

theorem expSeries_summable (x : 𝔸) : Summable fun n => expSeries 𝕂 𝔸 n fun _ => x :=
  (norm_expSeries_summable x).of_norm

theorem expSeries_summable' (x : 𝔸) : Summable fun n => (n !⁻¹ : 𝕂) • x ^ n :=
  (norm_expSeries_summable' x).of_norm

theorem expSeries_hasSum_exp (x : 𝔸) : HasSum (fun n => expSeries 𝕂 𝔸 n fun _ => x) (exp 𝕂 x) :=
  expSeries_hasSum_exp_of_mem_ball x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

theorem exp_series_hasSum_exp' (x : 𝔸) : HasSum (fun n => (n !⁻¹ : 𝕂) • x ^ n) (exp 𝕂 x) :=
  expSeries_hasSum_exp_of_mem_ball' x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

theorem exp_hasFPowerSeriesOnBall : HasFPowerSeriesOnBall (exp 𝕂) (expSeries 𝕂 𝔸) 0 ∞ :=
  expSeries_radius_eq_top 𝕂 𝔸 ▸ hasFPowerSeriesOnBall_exp_of_radius_pos (expSeries_radius_pos _ _)

theorem exp_hasFPowerSeriesAt_zero : HasFPowerSeriesAt (exp 𝕂) (expSeries 𝕂 𝔸) 0 :=
  exp_hasFPowerSeriesOnBall.hasFPowerSeriesAt

@[continuity, fun_prop]
theorem exp_continuous : Continuous (exp 𝕂 : 𝔸 → 𝔸) := by
  rw [continuous_iff_continuousOn_univ, ← Metric.eball_top_eq_univ (0 : 𝔸), ←
    expSeries_radius_eq_top 𝕂 𝔸]
  exact continuousOn_exp

open Topology in
lemma _root_.Filter.Tendsto.exp {α : Type*} {l : Filter α} {f : α → 𝔸} {a : 𝔸}
    (hf : Tendsto f l (𝓝 a)) :
    Tendsto (fun x => exp 𝕂 (f x)) l (𝓝 (exp 𝕂 a)) :=
  (exp_continuous.tendsto _).comp hf

theorem exp_analytic (x : 𝔸) : AnalyticAt 𝕂 (exp 𝕂) x :=
  analyticAt_exp_of_mem_ball x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

/-- In a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, if `x` and `y` commute, then
`NormedSpace.exp 𝕂 (x+y) = (NormedSpace.exp 𝕂 x) * (NormedSpace.exp 𝕂 y)`. -/
theorem exp_add_of_commute {x y : 𝔸} (hxy : Commute x y) : exp 𝕂 (x + y) = exp 𝕂 x * exp 𝕂 y :=
  exp_add_of_commute_of_mem_ball hxy ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

section

variable (𝕂)

/-- `NormedSpace.exp 𝕂 x` has explicit two-sided inverse `NormedSpace.exp 𝕂 (-x)`. -/
noncomputable def invertibleExp (x : 𝔸) : Invertible (exp 𝕂 x) :=
  invertibleExpOfMemBall <| (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

theorem isUnit_exp (x : 𝔸) : IsUnit (exp 𝕂 x) :=
  isUnit_exp_of_mem_ball <| (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

theorem invOf_exp (x : 𝔸) [Invertible (exp 𝕂 x)] : ⅟ (exp 𝕂 x) = exp 𝕂 (-x) :=
  invOf_exp_of_mem_ball <| (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

theorem _root_.Ring.inverse_exp (x : 𝔸) : Ring.inverse (exp 𝕂 x) = exp 𝕂 (-x) :=
  letI := invertibleExp 𝕂 x
  Ring.inverse_invertible _

theorem exp_mem_unitary_of_mem_skewAdjoint [StarRing 𝔸] [ContinuousStar 𝔸] {x : 𝔸}
    (h : x ∈ skewAdjoint 𝔸) : exp 𝕂 x ∈ unitary 𝔸 := by
  rw [unitary.mem_iff, star_exp, skewAdjoint.mem_iff.mp h, ←
    exp_add_of_commute (Commute.refl x).neg_left, ← exp_add_of_commute (Commute.refl x).neg_right,
    neg_add_cancel, add_neg_cancel, exp_zero, and_self_iff]

end

open scoped Function in -- required for scoped `on` notation
/-- In a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, if a family of elements `f i` mutually
commute then `NormedSpace.exp 𝕂 (∑ i, f i) = ∏ i, NormedSpace.exp 𝕂 (f i)`. -/
theorem exp_sum_of_commute {ι} (s : Finset ι) (f : ι → 𝔸)
    (h : (s : Set ι).Pairwise (Commute on f)) :
    exp 𝕂 (∑ i ∈ s, f i) =
      s.noncommProd (fun i => exp 𝕂 (f i)) fun _ hi _ hj _ => (h.of_refl hi hj).exp 𝕂 := by
  classical
    induction' s using Finset.induction_on with a s ha ih
    · simp
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha, Finset.sum_insert ha, exp_add_of_commute,
      ih (h.mono <| Finset.subset_insert _ _)]
    refine Commute.sum_right _ _ _ fun i hi => ?_
    exact h.of_refl (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hi)

theorem exp_nsmul (n : ℕ) (x : 𝔸) : exp 𝕂 (n • x) = exp 𝕂 x ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, exp_zero]
  | succ n ih => rw [succ_nsmul, pow_succ, exp_add_of_commute ((Commute.refl x).smul_left n), ih]

variable (𝕂)

/-- Any continuous ring homomorphism commutes with `NormedSpace.exp`. -/
theorem map_exp {F} [FunLike F 𝔸 𝔹] [RingHomClass F 𝔸 𝔹] (f : F) (hf : Continuous f) (x : 𝔸) :
    f (exp 𝕂 x) = exp 𝕂 (f x) :=
  map_exp_of_mem_ball f hf x <| (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

theorem exp_smul {G} [Monoid G] [MulSemiringAction G 𝔸] [ContinuousConstSMul G 𝔸] (g : G) (x : 𝔸) :
    exp 𝕂 (g • x) = g • exp 𝕂 x :=
  (map_exp 𝕂 (MulSemiringAction.toRingHom G 𝔸 g) (continuous_const_smul g) x).symm

theorem exp_units_conj (y : 𝔸ˣ) (x : 𝔸) : exp 𝕂 (y * x * ↑y⁻¹ : 𝔸) = y * exp 𝕂 x * ↑y⁻¹ :=
  exp_smul _ (ConjAct.toConjAct y) x

theorem exp_units_conj' (y : 𝔸ˣ) (x : 𝔸) : exp 𝕂 (↑y⁻¹ * x * y) = ↑y⁻¹ * exp 𝕂 x * y :=
  exp_units_conj _ _ _

@[simp]
theorem _root_.Prod.fst_exp [CompleteSpace 𝔹] (x : 𝔸 × 𝔹) : (exp 𝕂 x).fst = exp 𝕂 x.fst :=
  map_exp _ (RingHom.fst 𝔸 𝔹) continuous_fst x

@[simp]
theorem _root_.Prod.snd_exp [CompleteSpace 𝔹] (x : 𝔸 × 𝔹) : (exp 𝕂 x).snd = exp 𝕂 x.snd :=
  map_exp _ (RingHom.snd 𝔸 𝔹) continuous_snd x

@[simp]
theorem _root_.Pi.coe_exp {ι : Type*} {𝔸 : ι → Type*} [Finite ι] [∀ i, NormedRing (𝔸 i)]
    [∀ i, NormedAlgebra 𝕂 (𝔸 i)] [∀ i, CompleteSpace (𝔸 i)] (x : ∀ i, 𝔸 i) (i : ι) :
    exp 𝕂 x i = exp 𝕂 (x i) :=
  let ⟨_⟩ := nonempty_fintype ι
  map_exp _ (Pi.evalRingHom 𝔸 i) (continuous_apply _) x

theorem _root_.Pi.exp_def {ι : Type*} {𝔸 : ι → Type*} [Finite ι] [∀ i, NormedRing (𝔸 i)]
    [∀ i, NormedAlgebra 𝕂 (𝔸 i)] [∀ i, CompleteSpace (𝔸 i)] (x : ∀ i, 𝔸 i) :
    exp 𝕂 x = fun i => exp 𝕂 (x i) :=
  funext <| Pi.coe_exp 𝕂 x

theorem _root_.Function.update_exp {ι : Type*} {𝔸 : ι → Type*} [Finite ι] [DecidableEq ι]
    [∀ i, NormedRing (𝔸 i)] [∀ i, NormedAlgebra 𝕂 (𝔸 i)] [∀ i, CompleteSpace (𝔸 i)] (x : ∀ i, 𝔸 i)
    (j : ι) (xj : 𝔸 j) :
    Function.update (exp 𝕂 x) j (exp 𝕂 xj) = exp 𝕂 (Function.update x j xj) := by
  ext i
  simp_rw [Pi.exp_def]
  exact (Function.apply_update (fun i => exp 𝕂) x j xj i).symm

end CompleteAlgebra

theorem algebraMap_exp_comm (x : 𝕂) : algebraMap 𝕂 𝔸 (exp 𝕂 x) = exp 𝕂 (algebraMap 𝕂 𝔸 x) :=
  algebraMap_exp_comm_of_mem_ball x <| (expSeries_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _

end AnyAlgebra

section DivisionAlgebra

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸]
variable (𝕂)
include 𝕂

theorem norm_expSeries_div_summable (x : 𝔸) : Summable fun n => ‖(x ^ n / n ! : 𝔸)‖ :=
  norm_expSeries_div_summable_of_mem_ball 𝕂 x
    ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

variable [CompleteSpace 𝔸]

theorem expSeries_div_summable (x : 𝔸) : Summable fun n => x ^ n / n ! :=
  (norm_expSeries_div_summable 𝕂 x).of_norm

theorem expSeries_div_hasSum_exp (x : 𝔸) : HasSum (fun n => x ^ n / n !) (exp 𝕂 x) :=
  expSeries_div_hasSum_exp_of_mem_ball 𝕂 x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

variable {𝕂}

theorem exp_neg (x : 𝔸) : exp 𝕂 (-x) = (exp 𝕂 x)⁻¹ :=
  exp_neg_of_mem_ball <| (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

theorem exp_zsmul (z : ℤ) (x : 𝔸) : exp 𝕂 (z • x) = exp 𝕂 x ^ z := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · rw [zpow_natCast, natCast_zsmul, exp_nsmul]
  · rw [zpow_neg, zpow_natCast, neg_smul, exp_neg, natCast_zsmul, exp_nsmul]

theorem exp_conj (y : 𝔸) (x : 𝔸) (hy : y ≠ 0) : exp 𝕂 (y * x * y⁻¹) = y * exp 𝕂 x * y⁻¹ :=
  exp_units_conj _ (Units.mk0 y hy) x

theorem exp_conj' (y : 𝔸) (x : 𝔸) (hy : y ≠ 0) : exp 𝕂 (y⁻¹ * x * y) = y⁻¹ * exp 𝕂 x * y :=
  exp_units_conj' _ (Units.mk0 y hy) x

end DivisionAlgebra

section CommAlgebra

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-- In a commutative Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`,
`NormedSpace.exp 𝕂 (x+y) = (NormedSpace.exp 𝕂 x) * (NormedSpace.exp 𝕂 y)`. -/
theorem exp_add {x y : 𝔸} : exp 𝕂 (x + y) = exp 𝕂 x * exp 𝕂 y :=
  exp_add_of_mem_ball ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

/-- A version of `NormedSpace.exp_sum_of_commute` for a commutative Banach-algebra. -/
theorem exp_sum {ι} (s : Finset ι) (f : ι → 𝔸) : exp 𝕂 (∑ i ∈ s, f i) = ∏ i ∈ s, exp 𝕂 (f i) := by
  rw [exp_sum_of_commute, Finset.noncommProd_eq_prod]
  exact fun i _hi j _hj _ => Commute.all _ _

end CommAlgebra

end RCLike

end Normed

section ScalarTower

variable (𝕂 𝕂' 𝔸 : Type*) [Field 𝕂] [Field 𝕂'] [Ring 𝔸] [Algebra 𝕂 𝔸] [Algebra 𝕂' 𝔸]
  [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸]

/-- If a normed ring `𝔸` is a normed algebra over two fields, then they define the same
`expSeries` on `𝔸`. -/
theorem expSeries_eq_expSeries (n : ℕ) (x : 𝔸) :
    (expSeries 𝕂 𝔸 n fun _ => x) = expSeries 𝕂' 𝔸 n fun _ => x := by
  rw [expSeries_apply_eq, expSeries_apply_eq, inv_natCast_smul_eq 𝕂 𝕂']

/-- If a normed ring `𝔸` is a normed algebra over two fields, then they define the same
exponential function on `𝔸`. -/
theorem exp_eq_exp : (exp 𝕂 : 𝔸 → 𝔸) = exp 𝕂' := by
  ext x
  rw [exp, exp]
  refine tsum_congr fun n => ?_
  rw [expSeries_eq_expSeries 𝕂 𝕂' 𝔸 n x]

theorem exp_ℝ_ℂ_eq_exp_ℂ_ℂ : (exp ℝ : ℂ → ℂ) = exp ℂ :=
  exp_eq_exp ℝ ℂ ℂ

/-- A version of `Complex.ofReal_exp` for `NormedSpace.exp` instead of `Complex.exp` -/
@[simp, norm_cast]
theorem of_real_exp_ℝ_ℝ (r : ℝ) : ↑(exp ℝ r) = exp ℂ (r : ℂ) :=
  (map_exp ℝ (algebraMap ℝ ℂ) (continuous_algebraMap _ _) r).trans (congr_fun exp_ℝ_ℂ_eq_exp_ℂ_ℂ _)

end ScalarTower

end NormedSpace
