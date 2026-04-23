/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!
# Complex and real exponential

In this file we prove that `Complex.exp` and `Real.exp` are analytic functions.

## Tags

exp, derivative
-/

public section

assert_not_exists IsConformalMap Conformal

noncomputable section

open Filter Asymptotics Set Function
open scoped Topology

/-! ## `Complex.exp` -/

section

open Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f g : E → ℂ} {z : ℂ} {x : E} {s : Set E}

/-- The function `Complex.exp` is complex analytic. -/
theorem analyticOnNhd_cexp : AnalyticOnNhd ℂ exp univ := by
  rw [Complex.exp_eq_exp_ℂ]
  exact fun x _ ↦ NormedSpace.exp_analytic x

/-- The function `Complex.exp` is complex analytic. -/
theorem analyticOn_cexp : AnalyticOn ℂ exp univ := analyticOnNhd_cexp.analyticOn

/-- The function `Complex.exp` is complex analytic. -/
@[fun_prop]
theorem analyticAt_cexp : AnalyticAt ℂ exp z :=
  analyticOnNhd_cexp z (mem_univ _)

/-- The function `Complex.exp` is complex analytic. -/
lemma analyticWithinAt_cexp {s : Set ℂ} {x : ℂ} :
    AnalyticWithinAt ℂ Complex.exp s x := by
  exact analyticAt_cexp.analyticWithinAt

/-- `exp ∘ f` is analytic -/
@[fun_prop]
theorem AnalyticAt.cexp (fa : AnalyticAt ℂ f x) : AnalyticAt ℂ (exp ∘ f) x :=
  analyticAt_cexp.comp fa

/-- `exp ∘ f` is analytic -/
@[fun_prop]
theorem AnalyticAt.cexp' (fa : AnalyticAt ℂ f x) : AnalyticAt ℂ (fun z ↦ exp (f z)) x :=
  fa.cexp

theorem AnalyticWithinAt.cexp (fa : AnalyticWithinAt ℂ f s x) :
    AnalyticWithinAt ℂ (fun z ↦ exp (f z)) s x :=
  analyticAt_cexp.comp_analyticWithinAt fa

/-- `exp ∘ f` is analytic -/
theorem AnalyticOnNhd.cexp (fs : AnalyticOnNhd ℂ f s) : AnalyticOnNhd ℂ (fun z ↦ exp (f z)) s :=
  fun z n ↦ analyticAt_cexp.comp (fs z n)

theorem AnalyticOn.cexp (fs : AnalyticOn ℂ f s) : AnalyticOn ℂ (fun z ↦ exp (f z)) s :=
  analyticOnNhd_cexp.comp_analyticOn fs (mapsTo_univ _ _)

end

namespace Complex

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]

/-- The complex exponential is everywhere differentiable, with the derivative `exp x`. -/
theorem hasDerivAt_exp (x : ℂ) : HasDerivAt exp (exp x) x := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have : (1 : ℕ) < 2 := by simp
  refine (IsBigO.of_bound ‖exp x‖ ?_).trans_isLittleO (isLittleO_pow_id this)
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one]
  simp only [Metric.mem_ball, dist_zero_right, norm_pow]
  exact fun z hz => exp_bound_sq x z hz.le

@[simp]
theorem differentiable_exp : Differentiable 𝕜 exp := fun x =>
  (hasDerivAt_exp x).differentiableAt.restrictScalars 𝕜

@[simp]
theorem differentiableAt_exp {x : ℂ} : DifferentiableAt 𝕜 exp x :=
  differentiable_exp x

@[simp]
theorem deriv_exp : deriv exp = exp :=
  funext fun x => (hasDerivAt_exp x).deriv

@[simp]
theorem iter_deriv_exp : ∀ n : ℕ, deriv^[n] exp = exp
  | 0 => rfl
  | n + 1 => by rw [iterate_succ_apply, deriv_exp, iter_deriv_exp n]

@[fun_prop]
theorem contDiff_exp {n : WithTop ℕ∞} : ContDiff 𝕜 n exp :=
  analyticOnNhd_cexp.restrictScalars.contDiff

theorem hasStrictDerivAt_exp (x : ℂ) : HasStrictDerivAt exp (exp x) x :=
  contDiff_exp.contDiffAt.hasStrictDerivAt' (hasDerivAt_exp x) one_ne_zero

theorem hasStrictFDerivAt_exp_real (x : ℂ) : HasStrictFDerivAt exp (exp x • (1 : ℂ →L[ℝ] ℂ)) x :=
  (hasStrictDerivAt_exp x).complexToReal_fderiv

end Complex

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] {f : 𝕜 → ℂ} {f' : ℂ} {x : 𝕜}
  {s : Set 𝕜}

theorem HasStrictDerivAt.cexp (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) * f') x :=
  (Complex.hasStrictDerivAt_exp (f x)).comp x hf

theorem HasDerivAt.cexp (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) * f') x :=
  (Complex.hasDerivAt_exp (f x)).comp x hf

theorem HasDerivWithinAt.cexp (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.exp (f x)) (Complex.exp (f x) * f') s x :=
  (Complex.hasDerivAt_exp (f x)).comp_hasDerivWithinAt x hf

theorem derivWithin_cexp (hf : DifferentiableWithinAt 𝕜 f s x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => Complex.exp (f x)) s x = Complex.exp (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.cexp.derivWithin hxs

@[simp]
theorem deriv_cexp (hc : DifferentiableAt 𝕜 f x) :
    deriv (fun x => Complex.exp (f x)) x = Complex.exp (f x) * deriv f x :=
  hc.hasDerivAt.cexp.deriv

end

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : E → ℂ} {f' : E →L[𝕜] ℂ} {x : E} {s : Set E}

theorem HasStrictFDerivAt.cexp (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) • f') x :=
  (Complex.hasStrictDerivAt_exp (f x)).comp_hasStrictFDerivAt x hf

theorem HasFDerivWithinAt.cexp (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Complex.exp (f x)) (Complex.exp (f x) • f') s x :=
  (Complex.hasDerivAt_exp (f x)).comp_hasFDerivWithinAt x hf

theorem HasFDerivAt.cexp (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) • f') x :=
  hasFDerivWithinAt_univ.1 <| hf.hasFDerivWithinAt.cexp

theorem DifferentiableWithinAt.cexp (hf : DifferentiableWithinAt 𝕜 f s x) :
    DifferentiableWithinAt 𝕜 (fun x => Complex.exp (f x)) s x :=
  hf.hasFDerivWithinAt.cexp.differentiableWithinAt

@[simp, fun_prop]
theorem DifferentiableAt.cexp (hc : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (fun x => Complex.exp (f x)) x :=
  hc.hasFDerivAt.cexp.differentiableAt

theorem DifferentiableOn.cexp (hc : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (fun x => Complex.exp (f x)) s := fun x h => (hc x h).cexp

@[simp, fun_prop]
theorem Differentiable.cexp (hc : Differentiable 𝕜 f) :
    Differentiable 𝕜 fun x => Complex.exp (f x) := fun x => (hc x).cexp

@[fun_prop]
theorem ContDiff.cexp {n} (h : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => Complex.exp (f x) :=
  Complex.contDiff_exp.comp h

@[fun_prop]
theorem ContDiffAt.cexp {n} (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x => Complex.exp (f x)) x :=
  Complex.contDiff_exp.contDiffAt.comp x hf

@[fun_prop]
theorem ContDiffOn.cexp {n} (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun x => Complex.exp (f x)) s :=
  Complex.contDiff_exp.comp_contDiffOn hf

@[fun_prop]
theorem ContDiffWithinAt.cexp {n} (hf : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n (fun x => Complex.exp (f x)) s x :=
  Complex.contDiff_exp.contDiffAt.comp_contDiffWithinAt x hf

end

open Complex in
@[simp]
theorem iteratedDeriv_cexp_const_mul (n : ℕ) (c : ℂ) :
    (iteratedDeriv n fun s : ℂ => exp (c * s)) = fun s => c ^ n * exp (c * s) := by
  rw [iteratedDeriv_comp_const_mul contDiff_exp, iteratedDeriv_eq_iterate, iter_deriv_exp]

/-! ## `Real.exp` -/

section

open Real

variable {x : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {s : Set E}

/-- The function `Real.exp` is real analytic. -/
theorem analyticOnNhd_rexp : AnalyticOnNhd ℝ exp univ := by
  rw [Real.exp_eq_exp_ℝ]
  exact fun x _ ↦ NormedSpace.exp_analytic x

/-- The function `Real.exp` is real analytic. -/
theorem analyticOn_rexp : AnalyticOn ℝ exp univ := analyticOnNhd_rexp.analyticOn

/-- The function `Real.exp` is real analytic. -/
@[fun_prop]
theorem analyticAt_rexp : AnalyticAt ℝ exp x :=
  analyticOnNhd_rexp x (mem_univ _)

/-- The function `Real.exp` is real analytic. -/
lemma analyticWithinAt_rexp {s : Set ℝ} : AnalyticWithinAt ℝ Real.exp s x :=
  analyticAt_rexp.analyticWithinAt

/-- `exp ∘ f` is analytic -/
@[fun_prop]
theorem AnalyticAt.rexp {x : E} (fa : AnalyticAt ℝ f x) : AnalyticAt ℝ (exp ∘ f) x :=
  analyticAt_rexp.comp fa

/-- `exp ∘ f` is analytic -/
@[fun_prop]
theorem AnalyticAt.rexp' {x : E} (fa : AnalyticAt ℝ f x) : AnalyticAt ℝ (fun z ↦ exp (f z)) x :=
  fa.rexp

theorem AnalyticWithinAt.rexp {x : E} (fa : AnalyticWithinAt ℝ f s x) :
    AnalyticWithinAt ℝ (fun z ↦ exp (f z)) s x :=
  analyticAt_rexp.comp_analyticWithinAt fa

/-- `exp ∘ f` is analytic -/
theorem AnalyticOnNhd.rexp {s : Set E} (fs : AnalyticOnNhd ℝ f s) :
    AnalyticOnNhd ℝ (fun z ↦ exp (f z)) s :=
  fun z n ↦ analyticAt_rexp.comp (fs z n)

theorem AnalyticOn.rexp (fs : AnalyticOn ℝ f s) : AnalyticOn ℝ (fun z ↦ exp (f z)) s :=
  analyticOnNhd_rexp.comp_analyticOn fs (mapsTo_univ _ _)

end

namespace Real

theorem hasStrictDerivAt_exp (x : ℝ) : HasStrictDerivAt exp (exp x) x :=
  (Complex.hasStrictDerivAt_exp x).real_of_complex

theorem hasDerivAt_exp (x : ℝ) : HasDerivAt exp (exp x) x :=
  (Complex.hasDerivAt_exp x).real_of_complex

@[fun_prop]
theorem contDiff_exp {n : WithTop ℕ∞} : ContDiff ℝ n exp :=
  Complex.contDiff_exp.real_of_complex

@[simp]
theorem differentiable_exp : Differentiable ℝ exp := fun x => (hasDerivAt_exp x).differentiableAt

@[simp]
theorem differentiableAt_exp {x : ℝ} : DifferentiableAt ℝ exp x :=
  differentiable_exp x

@[simp]
theorem deriv_exp : deriv exp = exp :=
  funext fun x => (hasDerivAt_exp x).deriv

@[simp]
theorem iter_deriv_exp : ∀ n : ℕ, deriv^[n] exp = exp
  | 0 => rfl
  | n + 1 => by rw [iterate_succ_apply, deriv_exp, iter_deriv_exp n]

end Real

section

/-! Register lemmas for the derivatives of the composition of `Real.exp` with a differentiable
function, for standalone use and use with `simp`. -/


variable {f : ℝ → ℝ} {f' x : ℝ} {s : Set ℝ}

theorem HasStrictDerivAt.exp (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') x :=
  (Real.hasStrictDerivAt_exp (f x)).comp x hf

theorem HasDerivAt.exp (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') x :=
  (Real.hasDerivAt_exp (f x)).comp x hf

theorem HasDerivWithinAt.exp (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') s x :=
  (Real.hasDerivAt_exp (f x)).comp_hasDerivWithinAt x hf

theorem derivWithin_exp (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => Real.exp (f x)) s x = Real.exp (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.exp.derivWithin hxs

@[simp]
theorem deriv_exp (hc : DifferentiableAt ℝ f x) :
    deriv (fun x => Real.exp (f x)) x = Real.exp (f x) * deriv f x :=
  hc.hasDerivAt.exp.deriv

end

section

/-! Register lemmas for the derivatives of the composition of `Real.exp` with a differentiable
function, for standalone use and use with `simp`. -/


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {f' : StrongDual ℝ E}
  {x : E} {s : Set E}

@[fun_prop]
theorem ContDiff.exp {n} (hf : ContDiff ℝ n f) : ContDiff ℝ n fun x => Real.exp (f x) :=
  Real.contDiff_exp.comp hf

@[fun_prop]
theorem ContDiffAt.exp {n} (hf : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun x => Real.exp (f x)) x :=
  Real.contDiff_exp.contDiffAt.comp x hf

@[fun_prop]
theorem ContDiffOn.exp {n} (hf : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun x => Real.exp (f x)) s :=
  Real.contDiff_exp.comp_contDiffOn hf

@[fun_prop]
theorem ContDiffWithinAt.exp {n} (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun x => Real.exp (f x)) s x :=
  Real.contDiff_exp.contDiffAt.comp_contDiffWithinAt x hf

theorem HasFDerivWithinAt.exp (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Real.exp (f x)) (Real.exp (f x) • f') s x :=
  (Real.hasDerivAt_exp (f x)).comp_hasFDerivWithinAt x hf

theorem HasFDerivAt.exp (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) • f') x :=
  (Real.hasDerivAt_exp (f x)).comp_hasFDerivAt x hf

theorem HasStrictFDerivAt.exp (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) • f') x :=
  (Real.hasStrictDerivAt_exp (f x)).comp_hasStrictFDerivAt x hf

theorem DifferentiableWithinAt.exp (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.exp (f x)) s x :=
  hf.hasFDerivWithinAt.exp.differentiableWithinAt

@[simp, fun_prop]
theorem DifferentiableAt.exp (hc : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun x => Real.exp (f x)) x :=
  hc.hasFDerivAt.exp.differentiableAt

@[fun_prop]
theorem DifferentiableOn.exp (hc : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun x => Real.exp (f x)) s := fun x h => (hc x h).exp

@[simp, fun_prop]
theorem Differentiable.exp (hc : Differentiable ℝ f) : Differentiable ℝ fun x => Real.exp (f x) :=
  fun x => (hc x).exp

theorem fderivWithin_exp (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => Real.exp (f x)) s x = Real.exp (f x) • fderivWithin ℝ f s x :=
  hf.hasFDerivWithinAt.exp.fderivWithin hxs

@[simp]
theorem fderiv_exp (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => Real.exp (f x)) x = Real.exp (f x) • fderiv ℝ f x :=
  hc.hasFDerivAt.exp.fderiv

end

open Real in
@[simp]
theorem iteratedDeriv_exp_const_mul (n : ℕ) (c : ℝ) :
    (iteratedDeriv n fun s => exp (c * s)) = fun s => c ^ n * exp (c * s) := by
  rw [iteratedDeriv_comp_const_mul contDiff_exp, iteratedDeriv_eq_iterate, iter_deriv_exp]
