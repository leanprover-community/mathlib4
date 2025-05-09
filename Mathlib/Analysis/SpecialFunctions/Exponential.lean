/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Eric Wieser
-/
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Data.Complex.Exponential
import Mathlib.Topology.MetricSpace.CauSeqFilter

/-!
# Calculus results on exponential in a Banach algebra

In this file, we prove basic properties about the derivative of the exponential map `exp 𝕂`
in a Banach algebra `𝔸` over a field `𝕂`. We keep them separate from the main file
`Analysis.Normed.Algebra.Exponential` in order to minimize dependencies.

## Main results

We prove most results for an arbitrary field `𝕂`, and then specialize to `𝕂 = ℝ` or `𝕂 = ℂ`.

### General case

- `hasStrictFDerivAt_exp_zero_of_radius_pos` : `NormedSpace.exp 𝕂` has strict Fréchet derivative
  `1 : 𝔸 →L[𝕂] 𝔸` at zero, as long as it converges on a neighborhood of zero
  (see also `hasStrictDerivAt_exp_zero_of_radius_pos` for the case `𝔸 = 𝕂`)
- `hasStrictFDerivAt_exp_of_lt_radius` : if `𝕂` has characteristic zero and `𝔸` is commutative,
  then given a point `x` in the disk of convergence, `NormedSpace.exp 𝕂` has strict Fréchet
  derivative `NormedSpace.exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸` at x
  (see also `hasStrictDerivAt_exp_of_lt_radius` for the case `𝔸 = 𝕂`)
- `hasStrictFDerivAt_exp_smul_const_of_mem_ball`: even when `𝔸` is non-commutative,
  if we have an intermediate algebra `𝕊` which is commutative, the function
  `(u : 𝕊) ↦ NormedSpace.exp 𝕂 (u • x)`, still has strict Fréchet derivative
  `NormedSpace.exp 𝕂 (t • x) • (1 : 𝕊 →L[𝕂] 𝕊).smulRight x` at `t` if
  `t • x` is in the radius of convergence.

### `𝕂 = ℝ` or `𝕂 = ℂ`

- `hasStrictFDerivAt_exp_zero` : `NormedSpace.exp 𝕂` has strict Fréchet derivative `1 : 𝔸 →L[𝕂] 𝔸`
  at zero (see also `hasStrictDerivAt_exp_zero` for the case `𝔸 = 𝕂`)
- `hasStrictFDerivAt_exp` : if `𝔸` is commutative, then given any point `x`, `NormedSpace.exp 𝕂`
  has strict Fréchet derivative `NormedSpace.exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸` at x
  (see also `hasStrictDerivAt_exp` for the case `𝔸 = 𝕂`)
- `hasStrictFDerivAt_exp_smul_const`: even when `𝔸` is non-commutative, if we have
  an intermediate algebra `𝕊` which is commutative, the function
  `(u : 𝕊) ↦ NormedSpace.exp 𝕂 (u • x)` still has strict Fréchet derivative
  `NormedSpace.exp 𝕂 (t • x) • (1 : 𝔸 →L[𝕂] 𝔸).smulRight x` at `t`.

### Compatibility with `Real.exp` and `Complex.exp`

- `Complex.exp_eq_exp_ℂ` : `Complex.exp = NormedSpace.exp ℂ ℂ`
- `Real.exp_eq_exp_ℝ` : `Real.exp = NormedSpace.exp ℝ ℝ`

-/


open Filter RCLike ContinuousMultilinearMap NormedField NormedSpace Asymptotics

open scoped Nat Topology ENNReal

section AnyFieldAnyAlgebra

variable {𝕂 𝔸 : Type*} [NontriviallyNormedField 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸]

/-- The exponential in a Banach algebra `𝔸` over a normed field `𝕂` has strict Fréchet derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero, as long as it converges on a neighborhood of zero. -/
theorem hasStrictFDerivAt_exp_zero_of_radius_pos (h : 0 < (expSeries 𝕂 𝔸).radius) :
    HasStrictFDerivAt (exp 𝕂) (1 : 𝔸 →L[𝕂] 𝔸) 0 := by
  convert (hasFPowerSeriesAt_exp_zero_of_radius_pos h).hasStrictFDerivAt
  ext x
  change x = expSeries 𝕂 𝔸 1 fun _ => x
  simp [expSeries_apply_eq, Nat.factorial]

/-- The exponential in a Banach algebra `𝔸` over a normed field `𝕂` has Fréchet derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero, as long as it converges on a neighborhood of zero. -/
theorem hasFDerivAt_exp_zero_of_radius_pos (h : 0 < (expSeries 𝕂 𝔸).radius) :
    HasFDerivAt (exp 𝕂) (1 : 𝔸 →L[𝕂] 𝔸) 0 :=
  (hasStrictFDerivAt_exp_zero_of_radius_pos h).hasFDerivAt

end AnyFieldAnyAlgebra

section AnyFieldCommAlgebra

variable {𝕂 𝔸 : Type*} [NontriviallyNormedField 𝕂] [NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸]

/-- The exponential map in a commutative Banach algebra `𝔸` over a normed field `𝕂` of
characteristic zero has Fréchet derivative `NormedSpace.exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸`
at any point `x`in the disk of convergence. -/
theorem hasFDerivAt_exp_of_mem_ball [CharZero 𝕂] {x : 𝔸}
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasFDerivAt (exp 𝕂) (exp 𝕂 x • (1 : 𝔸 →L[𝕂] 𝔸)) x := by
  have hpos : 0 < (expSeries 𝕂 𝔸).radius := (zero_le _).trans_lt hx
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  suffices
    (fun h => exp 𝕂 x * (exp 𝕂 (0 + h) - exp 𝕂 0 - ContinuousLinearMap.id 𝕂 𝔸 h)) =ᶠ[𝓝 0] fun h =>
      exp 𝕂 (x + h) - exp 𝕂 x - exp 𝕂 x • ContinuousLinearMap.id 𝕂 𝔸 h by
    refine (IsLittleO.const_mul_left ?_ _).congr' this (EventuallyEq.refl _ _)
    rw [← hasFDerivAt_iff_isLittleO_nhds_zero]
    exact hasFDerivAt_exp_zero_of_radius_pos hpos
  have : ∀ᶠ h in 𝓝 (0 : 𝔸), h ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius :=
    EMetric.ball_mem_nhds _ hpos
  filter_upwards [this] with _ hh
  rw [exp_add_of_mem_ball hx hh, exp_zero, zero_add, ContinuousLinearMap.id_apply, smul_eq_mul]
  ring

/-- The exponential map in a commutative Banach algebra `𝔸` over a normed field `𝕂` of
characteristic zero has strict Fréchet derivative `NormedSpace.exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸`
at any point `x` in the disk of convergence. -/
theorem hasStrictFDerivAt_exp_of_mem_ball [CharZero 𝕂] {x : 𝔸}
    (hx : x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasStrictFDerivAt (exp 𝕂) (exp 𝕂 x • (1 : 𝔸 →L[𝕂] 𝔸)) x :=
  let ⟨_, hp⟩ := analyticAt_exp_of_mem_ball x hx
  hp.hasFDerivAt.unique (hasFDerivAt_exp_of_mem_ball hx) ▸ hp.hasStrictFDerivAt

end AnyFieldCommAlgebra

section deriv

variable {𝕂 : Type*} [NontriviallyNormedField 𝕂] [CompleteSpace 𝕂]

/-- The exponential map in a complete normed field `𝕂` of characteristic zero has strict derivative
`NormedSpace.exp 𝕂 x` at any point `x` in the disk of convergence. -/
theorem hasStrictDerivAt_exp_of_mem_ball [CharZero 𝕂] {x : 𝕂}
    (hx : x ∈ EMetric.ball (0 : 𝕂) (expSeries 𝕂 𝕂).radius) :
    HasStrictDerivAt (exp 𝕂) (exp 𝕂 x) x := by
  simpa using (hasStrictFDerivAt_exp_of_mem_ball hx).hasStrictDerivAt

/-- The exponential map in a complete normed field `𝕂` of characteristic zero has derivative
`NormedSpace.exp 𝕂 x` at any point `x` in the disk of convergence. -/
theorem hasDerivAt_exp_of_mem_ball [CharZero 𝕂] {x : 𝕂}
    (hx : x ∈ EMetric.ball (0 : 𝕂) (expSeries 𝕂 𝕂).radius) : HasDerivAt (exp 𝕂) (exp 𝕂 x) x :=
  (hasStrictDerivAt_exp_of_mem_ball hx).hasDerivAt

/-- The exponential map in a complete normed field `𝕂` of characteristic zero has strict derivative
`1` at zero, as long as it converges on a neighborhood of zero. -/
theorem hasStrictDerivAt_exp_zero_of_radius_pos (h : 0 < (expSeries 𝕂 𝕂).radius) :
    HasStrictDerivAt (exp 𝕂) (1 : 𝕂) 0 :=
  (hasStrictFDerivAt_exp_zero_of_radius_pos h).hasStrictDerivAt

/-- The exponential map in a complete normed field `𝕂` of characteristic zero has derivative
`1` at zero, as long as it converges on a neighborhood of zero. -/
theorem hasDerivAt_exp_zero_of_radius_pos (h : 0 < (expSeries 𝕂 𝕂).radius) :
    HasDerivAt (exp 𝕂) (1 : 𝕂) 0 :=
  (hasStrictDerivAt_exp_zero_of_radius_pos h).hasDerivAt

end deriv

section RCLikeAnyAlgebra

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-- The exponential in a Banach algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has strict Fréchet derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero. -/
theorem hasStrictFDerivAt_exp_zero : HasStrictFDerivAt (exp 𝕂) (1 : 𝔸 →L[𝕂] 𝔸) 0 :=
  hasStrictFDerivAt_exp_zero_of_radius_pos (expSeries_radius_pos 𝕂 𝔸)

/-- The exponential in a Banach algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has Fréchet derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero. -/
theorem hasFDerivAt_exp_zero : HasFDerivAt (exp 𝕂) (1 : 𝔸 →L[𝕂] 𝔸) 0 :=
  hasStrictFDerivAt_exp_zero.hasFDerivAt

end RCLikeAnyAlgebra

section RCLikeCommAlgebra

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-- The exponential map in a commutative Banach algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has strict
Fréchet derivative `NormedSpace.exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸` at any point `x`. -/
theorem hasStrictFDerivAt_exp {x : 𝔸} : HasStrictFDerivAt (exp 𝕂) (exp 𝕂 x • (1 : 𝔸 →L[𝕂] 𝔸)) x :=
  hasStrictFDerivAt_exp_of_mem_ball ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

/-- The exponential map in a commutative Banach algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has
Fréchet derivative `NormedSpace.exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸` at any point `x`. -/
theorem hasFDerivAt_exp {x : 𝔸} : HasFDerivAt (exp 𝕂) (exp 𝕂 x • (1 : 𝔸 →L[𝕂] 𝔸)) x :=
  hasStrictFDerivAt_exp.hasFDerivAt

end RCLikeCommAlgebra

section DerivRCLike

variable {𝕂 : Type*} [RCLike 𝕂]

/-- The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has strict derivative `NormedSpace.exp 𝕂 x`
at any point `x`. -/
theorem hasStrictDerivAt_exp {x : 𝕂} : HasStrictDerivAt (exp 𝕂) (exp 𝕂 x) x :=
  hasStrictDerivAt_exp_of_mem_ball ((expSeries_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _)

/-- The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has derivative `NormedSpace.exp 𝕂 x`
at any point `x`. -/
theorem hasDerivAt_exp {x : 𝕂} : HasDerivAt (exp 𝕂) (exp 𝕂 x) x :=
  hasStrictDerivAt_exp.hasDerivAt

/-- The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has strict derivative `1` at zero. -/
theorem hasStrictDerivAt_exp_zero : HasStrictDerivAt (exp 𝕂) (1 : 𝕂) 0 :=
  hasStrictDerivAt_exp_zero_of_radius_pos (expSeries_radius_pos 𝕂 𝕂)

/-- The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has derivative `1` at zero. -/
theorem hasDerivAt_exp_zero : HasDerivAt (exp 𝕂) (1 : 𝕂) 0 :=
  hasStrictDerivAt_exp_zero.hasDerivAt

end DerivRCLike

theorem Complex.exp_eq_exp_ℂ : Complex.exp = NormedSpace.exp ℂ := by
  refine funext fun x => ?_
  rw [Complex.exp, exp_eq_tsum_div]
  have : CauSeq.IsComplete ℂ norm := Complex.instIsComplete
  exact tendsto_nhds_unique x.exp'.tendsto_limit (expSeries_div_summable ℝ x).hasSum.tendsto_sum_nat

theorem Real.exp_eq_exp_ℝ : Real.exp = NormedSpace.exp ℝ := by
  ext x; exact mod_cast congr_fun Complex.exp_eq_exp_ℂ x

/-! ### Derivative of $\exp (ux)$ by $u$

Note that since for `x : 𝔸` we have `NormedRing 𝔸` not `NormedCommRing 𝔸`, we cannot deduce
these results from `hasFDerivAt_exp_of_mem_ball` applied to the algebra `𝔸`.

One possible solution for that would be to apply `hasFDerivAt_exp_of_mem_ball` to the
commutative algebra `Algebra.elementalAlgebra 𝕊 x`. Unfortunately we don't have all the required
API, so we leave that to a future refactor (see https://github.com/leanprover-community/mathlib3/pull/19062 for discussion).

We could also go the other way around and deduce `hasFDerivAt_exp_of_mem_ball` from
`hasFDerivAt_exp_smul_const_of_mem_ball` applied to `𝕊 := 𝔸`, `x := (1 : 𝔸)`, and `t := x`.
However, doing so would make the aforementioned `elementalAlgebra` refactor harder, so for now we
just prove these two lemmas independently.

A last strategy would be to deduce everything from the more general non-commutative case,
$$\frac{d}{dt}e^{x(t)} = \int_0^1 e^{sx(t)} \left(\frac{d}{dt}e^{x(t)}\right) e^{(1-s)x(t)} ds$$
but this is harder to prove, and typically is shown by going via these results first.

TODO: prove this result too!
-/


section exp_smul

variable {𝕂 𝕊 𝔸 : Type*}
variable (𝕂)

open scoped Topology

open Asymptotics Filter

section MemBall

variable [NontriviallyNormedField 𝕂] [CharZero 𝕂]
variable [NormedCommRing 𝕊] [NormedRing 𝔸]
variable [NormedSpace 𝕂 𝕊] [NormedAlgebra 𝕂 𝔸] [Algebra 𝕊 𝔸] [ContinuousSMul 𝕊 𝔸]
variable [IsScalarTower 𝕂 𝕊 𝔸]
variable [CompleteSpace 𝔸]

theorem hasFDerivAt_exp_smul_const_of_mem_ball (x : 𝔸) (t : 𝕊)
    (htx : t • x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasFDerivAt (fun u : 𝕊 => exp 𝕂 (u • x)) (exp 𝕂 (t • x) • (1 : 𝕊 →L[𝕂] 𝕊).smulRight x) t := by
  -- TODO: prove this via `hasFDerivAt_exp_of_mem_ball` using the commutative ring
  -- `Algebra.elementalAlgebra 𝕊 x`. See https://github.com/leanprover-community/mathlib3/pull/19062 for discussion.
  have hpos : 0 < (expSeries 𝕂 𝔸).radius := (zero_le _).trans_lt htx
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  suffices (fun (h : 𝕊) => exp 𝕂 (t • x) *
      (exp 𝕂 ((0 + h) • x) - exp 𝕂 ((0 : 𝕊) • x) - ((1 : 𝕊 →L[𝕂] 𝕊).smulRight x) h)) =ᶠ[𝓝 0]
        fun h =>
          exp 𝕂 ((t + h) • x) - exp 𝕂 (t • x) - (exp 𝕂 (t • x) • (1 : 𝕊 →L[𝕂] 𝕊).smulRight x) h by
    apply (IsLittleO.const_mul_left _ _).congr' this (EventuallyEq.refl _ _)
    rw [← hasFDerivAt_iff_isLittleO_nhds_zero (f := fun u => exp 𝕂 (u • x))
      (f' := (1 : 𝕊 →L[𝕂] 𝕊).smulRight x) (x := 0)]
    have : HasFDerivAt (exp 𝕂) (1 : 𝔸 →L[𝕂] 𝔸) ((1 : 𝕊 →L[𝕂] 𝕊).smulRight x 0) := by
      rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, zero_smul]
      exact hasFDerivAt_exp_zero_of_radius_pos hpos
    exact this.comp 0 ((1 : 𝕊 →L[𝕂] 𝕊).smulRight x).hasFDerivAt
  have : Tendsto (fun h : 𝕊 => h • x) (𝓝 0) (𝓝 0) := by
    rw [← zero_smul 𝕊 x]
    exact tendsto_id.smul_const x
  have : ∀ᶠ h in 𝓝 (0 : 𝕊), h • x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius :=
    this.eventually (EMetric.ball_mem_nhds _ hpos)
  filter_upwards [this] with h hh
  have : Commute (t • x) (h • x) := ((Commute.refl x).smul_left t).smul_right h
  rw [add_smul t h, exp_add_of_commute_of_mem_ball this htx hh, zero_add, zero_smul, exp_zero,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul, mul_sub_left_distrib, mul_sub_left_distrib, mul_one]

theorem hasFDerivAt_exp_smul_const_of_mem_ball' (x : 𝔸) (t : 𝕊)
    (htx : t • x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasFDerivAt (fun u : 𝕊 => exp 𝕂 (u • x))
      (((1 : 𝕊 →L[𝕂] 𝕊).smulRight x).smulRight (exp 𝕂 (t • x))) t := by
  convert hasFDerivAt_exp_smul_const_of_mem_ball 𝕂 _ _ htx using 1
  ext t'
  show Commute (t' • x) (exp 𝕂 (t • x))
  exact (((Commute.refl x).smul_left t').smul_right t).exp_right 𝕂

theorem hasStrictFDerivAt_exp_smul_const_of_mem_ball (x : 𝔸) (t : 𝕊)
    (htx : t • x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasStrictFDerivAt (fun u : 𝕊 => exp 𝕂 (u • x))
      (exp 𝕂 (t • x) • (1 : 𝕊 →L[𝕂] 𝕊).smulRight x) t :=
  let ⟨_, hp⟩ := analyticAt_exp_of_mem_ball (t • x) htx
  have deriv₁ : HasStrictFDerivAt (fun u : 𝕊 => exp 𝕂 (u • x)) _ t :=
    hp.hasStrictFDerivAt.comp t ((ContinuousLinearMap.id 𝕂 𝕊).smulRight x).hasStrictFDerivAt
  have deriv₂ : HasFDerivAt (fun u : 𝕊 => exp 𝕂 (u • x)) _ t :=
    hasFDerivAt_exp_smul_const_of_mem_ball 𝕂 x t htx
  deriv₁.hasFDerivAt.unique deriv₂ ▸ deriv₁

theorem hasStrictFDerivAt_exp_smul_const_of_mem_ball' (x : 𝔸) (t : 𝕊)
    (htx : t • x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasStrictFDerivAt (fun u : 𝕊 => exp 𝕂 (u • x))
      (((1 : 𝕊 →L[𝕂] 𝕊).smulRight x).smulRight (exp 𝕂 (t • x))) t := by
  let ⟨_, _⟩ := analyticAt_exp_of_mem_ball (t • x) htx
  convert hasStrictFDerivAt_exp_smul_const_of_mem_ball 𝕂 _ _ htx using 1
  ext t'
  show Commute (t' • x) (exp 𝕂 (t • x))
  exact (((Commute.refl x).smul_left t').smul_right t).exp_right 𝕂

variable {𝕂}

theorem hasStrictDerivAt_exp_smul_const_of_mem_ball (x : 𝔸) (t : 𝕂)
    (htx : t • x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasStrictDerivAt (fun u : 𝕂 => exp 𝕂 (u • x)) (exp 𝕂 (t • x) * x) t := by
  simpa using (hasStrictFDerivAt_exp_smul_const_of_mem_ball 𝕂 x t htx).hasStrictDerivAt

theorem hasStrictDerivAt_exp_smul_const_of_mem_ball' (x : 𝔸) (t : 𝕂)
    (htx : t • x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasStrictDerivAt (fun u : 𝕂 => exp 𝕂 (u • x)) (x * exp 𝕂 (t • x)) t := by
  simpa using (hasStrictFDerivAt_exp_smul_const_of_mem_ball' 𝕂 x t htx).hasStrictDerivAt

theorem hasDerivAt_exp_smul_const_of_mem_ball (x : 𝔸) (t : 𝕂)
    (htx : t • x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasDerivAt (fun u : 𝕂 => exp 𝕂 (u • x)) (exp 𝕂 (t • x) * x) t :=
  (hasStrictDerivAt_exp_smul_const_of_mem_ball x t htx).hasDerivAt

theorem hasDerivAt_exp_smul_const_of_mem_ball' (x : 𝔸) (t : 𝕂)
    (htx : t • x ∈ EMetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasDerivAt (fun u : 𝕂 => exp 𝕂 (u • x)) (x * exp 𝕂 (t • x)) t :=
  (hasStrictDerivAt_exp_smul_const_of_mem_ball' x t htx).hasDerivAt

end MemBall

section RCLike

variable [RCLike 𝕂]
variable [NormedCommRing 𝕊] [NormedRing 𝔸]
variable [NormedAlgebra 𝕂 𝕊] [NormedAlgebra 𝕂 𝔸] [Algebra 𝕊 𝔸] [ContinuousSMul 𝕊 𝔸]
variable [IsScalarTower 𝕂 𝕊 𝔸]
variable [CompleteSpace 𝔸]

theorem hasFDerivAt_exp_smul_const (x : 𝔸) (t : 𝕊) :
    HasFDerivAt (fun u : 𝕊 => exp 𝕂 (u • x)) (exp 𝕂 (t • x) • (1 : 𝕊 →L[𝕂] 𝕊).smulRight x) t :=
  hasFDerivAt_exp_smul_const_of_mem_ball 𝕂 _ _ <|
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

theorem hasFDerivAt_exp_smul_const' (x : 𝔸) (t : 𝕊) :
    HasFDerivAt (fun u : 𝕊 => exp 𝕂 (u • x))
      (((1 : 𝕊 →L[𝕂] 𝕊).smulRight x).smulRight (exp 𝕂 (t • x))) t :=
  hasFDerivAt_exp_smul_const_of_mem_ball' 𝕂 _ _ <|
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

theorem hasStrictFDerivAt_exp_smul_const (x : 𝔸) (t : 𝕊) :
    HasStrictFDerivAt (fun u : 𝕊 => exp 𝕂 (u • x))
      (exp 𝕂 (t • x) • (1 : 𝕊 →L[𝕂] 𝕊).smulRight x) t :=
  hasStrictFDerivAt_exp_smul_const_of_mem_ball 𝕂 _ _ <|
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

theorem hasStrictFDerivAt_exp_smul_const' (x : 𝔸) (t : 𝕊) :
    HasStrictFDerivAt (fun u : 𝕊 => exp 𝕂 (u • x))
      (((1 : 𝕊 →L[𝕂] 𝕊).smulRight x).smulRight (exp 𝕂 (t • x))) t :=
  hasStrictFDerivAt_exp_smul_const_of_mem_ball' 𝕂 _ _ <|
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

variable {𝕂}

theorem hasStrictDerivAt_exp_smul_const (x : 𝔸) (t : 𝕂) :
    HasStrictDerivAt (fun u : 𝕂 => exp 𝕂 (u • x)) (exp 𝕂 (t • x) * x) t :=
  hasStrictDerivAt_exp_smul_const_of_mem_ball _ _ <|
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

theorem hasStrictDerivAt_exp_smul_const' (x : 𝔸) (t : 𝕂) :
    HasStrictDerivAt (fun u : 𝕂 => exp 𝕂 (u • x)) (x * exp 𝕂 (t • x)) t :=
  hasStrictDerivAt_exp_smul_const_of_mem_ball' _ _ <|
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

theorem hasDerivAt_exp_smul_const (x : 𝔸) (t : 𝕂) :
    HasDerivAt (fun u : 𝕂 => exp 𝕂 (u • x)) (exp 𝕂 (t • x) * x) t :=
  hasDerivAt_exp_smul_const_of_mem_ball _ _ <| (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

theorem hasDerivAt_exp_smul_const' (x : 𝔸) (t : 𝕂) :
    HasDerivAt (fun u : 𝕂 => exp 𝕂 (u • x)) (x * exp 𝕂 (t • x)) t :=
  hasDerivAt_exp_smul_const_of_mem_ball' _ _ <|
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

end RCLike

end exp_smul

section tsum_tprod

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-- If `f` has sum `a`, then `NormedSpace.exp ∘ f` has product `NormedSpace.exp a`. -/
lemma HasSum.exp {ι : Type*} {f : ι → 𝔸} {a : 𝔸} (h : HasSum f a) :
    HasProd (exp 𝕂 ∘ f) (exp 𝕂 a) :=
  Tendsto.congr (fun s ↦ exp_sum s f) <| Tendsto.exp h

end tsum_tprod
