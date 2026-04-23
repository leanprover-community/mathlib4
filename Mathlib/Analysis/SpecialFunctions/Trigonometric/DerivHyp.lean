/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Order.Monotone.Odd
import Mathlib.Tactic.Abel
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
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Differentiability of hyperbolic trigonometric functions

## Main statements

The differentiability of the hyperbolic trigonometric functions is proved, and their derivatives are
computed.

## Tags

sinh, cosh, tanh
-/

public section

noncomputable section

open scoped Asymptotics Topology Filter
open Set

namespace Complex

/-- The complex hyperbolic sine function is everywhere strictly differentiable, with the derivative
`cosh x`. -/
theorem hasStrictDerivAt_sinh (x : ℂ) : HasStrictDerivAt sinh (cosh x) x := by
  simp only [cosh, div_eq_mul_inv]
  convert ((hasStrictDerivAt_exp x).sub (hasStrictDerivAt_id x).fun_neg.cexp).mul_const (2 : ℂ)⁻¹
    using 1
  rw [id, mul_neg_one, sub_eq_add_neg, neg_neg]

/-- The complex hyperbolic sine function is everywhere differentiable, with the derivative
`cosh x`. -/
theorem hasDerivAt_sinh (x : ℂ) : HasDerivAt sinh (cosh x) x :=
  (hasStrictDerivAt_sinh x).hasDerivAt

theorem isEquivalent_sinh : sinh ~[𝓝 0] id := by simpa using (hasDerivAt_sinh 0).isLittleO

@[fun_prop]
theorem contDiff_sinh {n} : ContDiff ℂ n sinh :=
  (contDiff_exp.sub contDiff_neg.cexp).div_const _

@[simp]
theorem differentiable_sinh : Differentiable ℂ sinh := fun x => (hasDerivAt_sinh x).differentiableAt

@[simp]
theorem differentiableAt_sinh {x : ℂ} : DifferentiableAt ℂ sinh x :=
  differentiable_sinh x

/-- The function `Complex.sinh` is complex analytic. -/
@[fun_prop]
lemma analyticAt_sinh {x : ℂ} : AnalyticAt ℂ sinh x :=
  contDiff_sinh.contDiffAt.analyticAt

/-- The function `Complex.sinh` is complex analytic. -/
lemma analyticWithinAt_sinh {x : ℂ} {s : Set ℂ} : AnalyticWithinAt ℂ sinh s x :=
  contDiff_sinh.contDiffWithinAt.analyticWithinAt

/-- The function `Complex.sinh` is complex analytic. -/
theorem analyticOnNhd_sinh {s : Set ℂ} : AnalyticOnNhd ℂ sinh s :=
  fun _ _ ↦ analyticAt_sinh

/-- The function `Complex.sinh` is complex analytic. -/
lemma analyticOn_sinh {s : Set ℂ} : AnalyticOn ℂ sinh s :=
  contDiff_sinh.contDiffOn.analyticOn

@[simp]
theorem deriv_sinh : deriv sinh = cosh :=
  funext fun x => (hasDerivAt_sinh x).deriv

/-- The complex hyperbolic cosine function is everywhere strictly differentiable, with the
derivative `sinh x`. -/
theorem hasStrictDerivAt_cosh (x : ℂ) : HasStrictDerivAt cosh (sinh x) x := by
  simp only [sinh, div_eq_mul_inv]
  convert ((hasStrictDerivAt_exp x).add (hasStrictDerivAt_id x).fun_neg.cexp).mul_const (2 : ℂ)⁻¹
    using 1
  rw [id, mul_neg_one, sub_eq_add_neg]

/-- The complex hyperbolic cosine function is everywhere differentiable, with the derivative
`sinh x`. -/
theorem hasDerivAt_cosh (x : ℂ) : HasDerivAt cosh (sinh x) x :=
  (hasStrictDerivAt_cosh x).hasDerivAt

@[fun_prop]
theorem contDiff_cosh {n} : ContDiff ℂ n cosh :=
  (contDiff_exp.add contDiff_neg.cexp).div_const _

@[simp]
theorem differentiable_cosh : Differentiable ℂ cosh := fun x => (hasDerivAt_cosh x).differentiableAt

@[simp]
theorem differentiableAt_cosh {x : ℂ} : DifferentiableAt ℂ cosh x :=
  differentiable_cosh x

/-- The function `Complex.cosh` is complex analytic. -/
@[fun_prop]
lemma analyticAt_cosh {x : ℂ} : AnalyticAt ℂ cosh x :=
  contDiff_cosh.contDiffAt.analyticAt

/-- The function `Complex.cosh` is complex analytic. -/
lemma analyticWithinAt_cosh {x : ℂ} {s : Set ℂ} : AnalyticWithinAt ℂ cosh s x :=
  contDiff_cosh.contDiffWithinAt.analyticWithinAt

/-- The function `Complex.cosh` is complex analytic. -/
theorem analyticOnNhd_cosh {s : Set ℂ} : AnalyticOnNhd ℂ cosh s :=
  fun _ _ ↦ analyticAt_cosh

/-- The function `Complex.cosh` is complex analytic. -/
lemma analyticOn_cosh {s : Set ℂ} : AnalyticOn ℂ cosh s :=
  contDiff_cosh.contDiffOn.analyticOn

@[simp]
theorem deriv_cosh : deriv cosh = sinh :=
  funext fun x => (hasDerivAt_cosh x).deriv

end Complex

section

/-! ### Simp lemmas for derivatives of `fun x => Complex.cos (f x)` etc., `f : ℂ → ℂ` -/

variable {f : ℂ → ℂ} {f' x : ℂ} {s : Set ℂ}

/-! #### `Complex.cosh` -/

theorem HasStrictDerivAt.ccosh (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) * f') x :=
  (Complex.hasStrictDerivAt_cosh (f x)).comp x hf

theorem HasDerivAt.ccosh (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) * f') x :=
  (Complex.hasDerivAt_cosh (f x)).comp x hf

theorem HasDerivWithinAt.ccosh (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) * f') s x :=
  (Complex.hasDerivAt_cosh (f x)).comp_hasDerivWithinAt x hf

theorem derivWithin_ccosh (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    derivWithin (fun x => Complex.cosh (f x)) s x = Complex.sinh (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.ccosh.derivWithin hxs

@[simp]
theorem deriv_ccosh (hc : DifferentiableAt ℂ f x) :
    deriv (fun x => Complex.cosh (f x)) x = Complex.sinh (f x) * deriv f x :=
  hc.hasDerivAt.ccosh.deriv

/-! #### `Complex.sinh` -/

theorem HasStrictDerivAt.csinh (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) * f') x :=
  (Complex.hasStrictDerivAt_sinh (f x)).comp x hf

theorem HasDerivAt.csinh (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) * f') x :=
  (Complex.hasDerivAt_sinh (f x)).comp x hf

theorem HasDerivWithinAt.csinh (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) * f') s x :=
  (Complex.hasDerivAt_sinh (f x)).comp_hasDerivWithinAt x hf

theorem derivWithin_csinh (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    derivWithin (fun x => Complex.sinh (f x)) s x = Complex.cosh (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.csinh.derivWithin hxs

@[simp]
theorem deriv_csinh (hc : DifferentiableAt ℂ f x) :
    deriv (fun x => Complex.sinh (f x)) x = Complex.cosh (f x) * deriv f x :=
  hc.hasDerivAt.csinh.deriv

end

section

/-! ### Simp lemmas for derivatives of `fun x => Complex.cos (f x)` etc., `f : E → ℂ` -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ} {f' : StrongDual ℂ E}
  {x : E} {s : Set E}

/-! #### `Complex.cosh` -/

theorem HasStrictFDerivAt.ccosh (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) • f') x :=
  (Complex.hasStrictDerivAt_cosh (f x)).comp_hasStrictFDerivAt x hf

theorem HasFDerivAt.ccosh (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) • f') x :=
  (Complex.hasDerivAt_cosh (f x)).comp_hasFDerivAt x hf

theorem HasFDerivWithinAt.ccosh (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) • f') s x :=
  (Complex.hasDerivAt_cosh (f x)).comp_hasFDerivWithinAt x hf

theorem DifferentiableWithinAt.ccosh (hf : DifferentiableWithinAt ℂ f s x) :
    DifferentiableWithinAt ℂ (fun x => Complex.cosh (f x)) s x :=
  hf.hasFDerivWithinAt.ccosh.differentiableWithinAt

@[simp, fun_prop]
theorem DifferentiableAt.ccosh (hc : DifferentiableAt ℂ f x) :
    DifferentiableAt ℂ (fun x => Complex.cosh (f x)) x :=
  hc.hasFDerivAt.ccosh.differentiableAt

theorem DifferentiableOn.ccosh (hc : DifferentiableOn ℂ f s) :
    DifferentiableOn ℂ (fun x => Complex.cosh (f x)) s := fun x h => (hc x h).ccosh

@[simp, fun_prop]
theorem Differentiable.ccosh (hc : Differentiable ℂ f) :
    Differentiable ℂ fun x => Complex.cosh (f x) := fun x => (hc x).ccosh

theorem fderivWithin_ccosh (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    fderivWithin ℂ (fun x => Complex.cosh (f x)) s x = Complex.sinh (f x) • fderivWithin ℂ f s x :=
  hf.hasFDerivWithinAt.ccosh.fderivWithin hxs

@[simp]
theorem fderiv_ccosh (hc : DifferentiableAt ℂ f x) :
    fderiv ℂ (fun x => Complex.cosh (f x)) x = Complex.sinh (f x) • fderiv ℂ f x :=
  hc.hasFDerivAt.ccosh.fderiv

theorem ContDiff.ccosh {n} (h : ContDiff ℂ n f) : ContDiff ℂ n fun x => Complex.cosh (f x) :=
  Complex.contDiff_cosh.comp h

theorem ContDiffAt.ccosh {n} (hf : ContDiffAt ℂ n f x) :
    ContDiffAt ℂ n (fun x => Complex.cosh (f x)) x :=
  Complex.contDiff_cosh.contDiffAt.comp x hf

theorem ContDiffOn.ccosh {n} (hf : ContDiffOn ℂ n f s) :
    ContDiffOn ℂ n (fun x => Complex.cosh (f x)) s :=
  Complex.contDiff_cosh.comp_contDiffOn hf

theorem ContDiffWithinAt.ccosh {n} (hf : ContDiffWithinAt ℂ n f s x) :
    ContDiffWithinAt ℂ n (fun x => Complex.cosh (f x)) s x :=
  Complex.contDiff_cosh.contDiffAt.comp_contDiffWithinAt x hf

/-! #### `Complex.sinh` -/

theorem HasStrictFDerivAt.csinh (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) • f') x :=
  (Complex.hasStrictDerivAt_sinh (f x)).comp_hasStrictFDerivAt x hf

theorem HasFDerivAt.csinh (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) • f') x :=
  (Complex.hasDerivAt_sinh (f x)).comp_hasFDerivAt x hf

theorem HasFDerivWithinAt.csinh (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) • f') s x :=
  (Complex.hasDerivAt_sinh (f x)).comp_hasFDerivWithinAt x hf

theorem DifferentiableWithinAt.csinh (hf : DifferentiableWithinAt ℂ f s x) :
    DifferentiableWithinAt ℂ (fun x => Complex.sinh (f x)) s x :=
  hf.hasFDerivWithinAt.csinh.differentiableWithinAt

@[simp, fun_prop]
theorem DifferentiableAt.csinh (hc : DifferentiableAt ℂ f x) :
    DifferentiableAt ℂ (fun x => Complex.sinh (f x)) x :=
  hc.hasFDerivAt.csinh.differentiableAt

theorem DifferentiableOn.csinh (hc : DifferentiableOn ℂ f s) :
    DifferentiableOn ℂ (fun x => Complex.sinh (f x)) s := fun x h => (hc x h).csinh

@[simp, fun_prop]
theorem Differentiable.csinh (hc : Differentiable ℂ f) :
    Differentiable ℂ fun x => Complex.sinh (f x) := fun x => (hc x).csinh

theorem fderivWithin_csinh (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    fderivWithin ℂ (fun x => Complex.sinh (f x)) s x = Complex.cosh (f x) • fderivWithin ℂ f s x :=
  hf.hasFDerivWithinAt.csinh.fderivWithin hxs

@[simp]
theorem fderiv_csinh (hc : DifferentiableAt ℂ f x) :
    fderiv ℂ (fun x => Complex.sinh (f x)) x = Complex.cosh (f x) • fderiv ℂ f x :=
  hc.hasFDerivAt.csinh.fderiv

theorem ContDiff.csinh {n} (h : ContDiff ℂ n f) : ContDiff ℂ n fun x => Complex.sinh (f x) :=
  Complex.contDiff_sinh.comp h

theorem ContDiffAt.csinh {n} (hf : ContDiffAt ℂ n f x) :
    ContDiffAt ℂ n (fun x => Complex.sinh (f x)) x :=
  Complex.contDiff_sinh.contDiffAt.comp x hf

theorem ContDiffOn.csinh {n} (hf : ContDiffOn ℂ n f s) :
    ContDiffOn ℂ n (fun x => Complex.sinh (f x)) s :=
  Complex.contDiff_sinh.comp_contDiffOn hf

theorem ContDiffWithinAt.csinh {n} (hf : ContDiffWithinAt ℂ n f s x) :
    ContDiffWithinAt ℂ n (fun x => Complex.sinh (f x)) s x :=
  Complex.contDiff_sinh.contDiffAt.comp_contDiffWithinAt x hf

end

namespace Real

variable {x y z : ℝ}

theorem hasStrictDerivAt_sinh (x : ℝ) : HasStrictDerivAt sinh (cosh x) x :=
  (Complex.hasStrictDerivAt_sinh x).real_of_complex

theorem hasDerivAt_sinh (x : ℝ) : HasDerivAt sinh (cosh x) x :=
  (Complex.hasDerivAt_sinh x).real_of_complex

theorem isEquivalent_sinh : sinh ~[𝓝 0] id := by simpa using (hasDerivAt_sinh 0).isLittleO

@[fun_prop]
theorem contDiff_sinh {n} : ContDiff ℝ n sinh :=
  Complex.contDiff_sinh.real_of_complex

@[simp]
theorem differentiable_sinh : Differentiable ℝ sinh := fun x => (hasDerivAt_sinh x).differentiableAt

@[simp]
theorem differentiableAt_sinh : DifferentiableAt ℝ sinh x :=
  differentiable_sinh x

/-- The function `Real.sinh` is real analytic. -/
@[fun_prop]
lemma analyticAt_sinh : AnalyticAt ℝ sinh x :=
  contDiff_sinh.contDiffAt.analyticAt

/-- The function `Real.sinh` is real analytic. -/
lemma analyticWithinAt_sinh {s : Set ℝ} : AnalyticWithinAt ℝ sinh s x :=
  contDiff_sinh.contDiffWithinAt.analyticWithinAt

/-- The function `Real.sinh` is real analytic. -/
theorem analyticOnNhd_sinh {s : Set ℝ} : AnalyticOnNhd ℝ sinh s :=
  fun _ _ ↦ analyticAt_sinh

/-- The function `Real.sinh` is real analytic. -/
lemma analyticOn_sinh {s : Set ℝ} : AnalyticOn ℝ sinh s :=
  contDiff_sinh.contDiffOn.analyticOn

@[simp]
theorem deriv_sinh : deriv sinh = cosh :=
  funext fun x => (hasDerivAt_sinh x).deriv

theorem hasStrictDerivAt_cosh (x : ℝ) : HasStrictDerivAt cosh (sinh x) x :=
  (Complex.hasStrictDerivAt_cosh x).real_of_complex

theorem hasDerivAt_cosh (x : ℝ) : HasDerivAt cosh (sinh x) x :=
  (Complex.hasDerivAt_cosh x).real_of_complex

@[fun_prop]
theorem contDiff_cosh {n} : ContDiff ℝ n cosh :=
  Complex.contDiff_cosh.real_of_complex

@[simp]
theorem differentiable_cosh : Differentiable ℝ cosh := fun x => (hasDerivAt_cosh x).differentiableAt

@[simp]
theorem differentiableAt_cosh : DifferentiableAt ℝ cosh x :=
  differentiable_cosh x

/-- The function `Real.cosh` is real analytic. -/
@[fun_prop]
lemma analyticAt_cosh : AnalyticAt ℝ cosh x :=
  contDiff_cosh.contDiffAt.analyticAt

/-- The function `Real.cosh` is real analytic. -/
lemma analyticWithinAt_cosh {s : Set ℝ} : AnalyticWithinAt ℝ cosh s x :=
  contDiff_cosh.contDiffWithinAt.analyticWithinAt

/-- The function `Real.cosh` is real analytic. -/
theorem analyticOnNhd_cosh {s : Set ℝ} : AnalyticOnNhd ℝ cosh s :=
  fun _ _ ↦ analyticAt_cosh

/-- The function `Real.cosh` is real analytic. -/
lemma analyticOn_cosh {s : Set ℝ} : AnalyticOn ℝ cosh s :=
  contDiff_cosh.contDiffOn.analyticOn

@[simp]
theorem deriv_cosh : deriv cosh = sinh :=
  funext fun x => (hasDerivAt_cosh x).deriv

/-- `sinh` is strictly monotone. -/
theorem sinh_strictMono : StrictMono sinh :=
  strictMono_of_deriv_pos <| by rw [Real.deriv_sinh]; exact cosh_pos

/-- `sinh` is injective, `∀ a b, sinh a = sinh b → a = b`. -/
theorem sinh_injective : Function.Injective sinh :=
  sinh_strictMono.injective

@[simp]
theorem sinh_inj : sinh x = sinh y ↔ x = y :=
  sinh_injective.eq_iff

@[simp]
theorem sinh_le_sinh : sinh x ≤ sinh y ↔ x ≤ y :=
  sinh_strictMono.le_iff_le

@[simp]
theorem sinh_lt_sinh : sinh x < sinh y ↔ x < y :=
  sinh_strictMono.lt_iff_lt

@[simp] lemma sinh_eq_zero : sinh x = 0 ↔ x = 0 := by rw [← @sinh_inj x, sinh_zero]

lemma sinh_ne_zero : sinh x ≠ 0 ↔ x ≠ 0 := sinh_eq_zero.not

@[simp]
theorem sinh_pos_iff : 0 < sinh x ↔ 0 < x := by simpa only [sinh_zero] using @sinh_lt_sinh 0 x

@[simp]
theorem sinh_nonpos_iff : sinh x ≤ 0 ↔ x ≤ 0 := by simpa only [sinh_zero] using @sinh_le_sinh x 0

@[simp]
theorem sinh_neg_iff : sinh x < 0 ↔ x < 0 := by simpa only [sinh_zero] using @sinh_lt_sinh x 0

@[simp]
theorem sinh_nonneg_iff : 0 ≤ sinh x ↔ 0 ≤ x := by simpa only [sinh_zero] using @sinh_le_sinh 0 x

theorem abs_sinh (x : ℝ) : |sinh x| = sinh |x| := by
  cases le_total x 0 <;> simp [abs_of_nonneg, abs_of_nonpos, *]

theorem cosh_strictMonoOn : StrictMonoOn cosh (Ici 0) :=
  strictMonoOn_of_deriv_pos (convex_Ici _) continuous_cosh.continuousOn fun x hx => by
    rw [interior_Ici, mem_Ioi] at hx; rwa [deriv_cosh, sinh_pos_iff]

@[simp]
theorem cosh_le_cosh : cosh x ≤ cosh y ↔ |x| ≤ |y| :=
  cosh_abs x ▸ cosh_abs y ▸ cosh_strictMonoOn.le_iff_le (abs_nonneg x) (abs_nonneg y)

@[simp]
theorem cosh_lt_cosh : cosh x < cosh y ↔ |x| < |y| :=
  lt_iff_lt_of_le_iff_le cosh_le_cosh

@[simp]
theorem one_le_cosh (x : ℝ) : 1 ≤ cosh x :=
  cosh_zero ▸ cosh_le_cosh.2 (by simp only [_root_.abs_zero, _root_.abs_nonneg])

@[simp]
theorem one_lt_cosh : 1 < cosh x ↔ x ≠ 0 :=
  cosh_zero ▸ cosh_lt_cosh.trans (by simp only [_root_.abs_zero, abs_pos])

theorem sinh_sub_id_strictMono : StrictMono fun x => sinh x - x := by
  refine strictMono_of_odd_strictMonoOn_nonneg (fun x => by simp; abel) ?_
  refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ fun x hx => ?_
  · exact (continuous_sinh.sub continuous_id).continuousOn
  · rw [interior_Ici, mem_Ioi] at hx
    rw [deriv_fun_sub, deriv_sinh, deriv_id'', sub_pos, one_lt_cosh]
    exacts [hx.ne', differentiableAt_sinh, differentiableAt_id]

@[simp]
theorem self_le_sinh_iff : x ≤ sinh x ↔ 0 ≤ x :=
  calc
    x ≤ sinh x ↔ sinh 0 - 0 ≤ sinh x - x := by simp
    _ ↔ 0 ≤ x := sinh_sub_id_strictMono.le_iff_le

@[simp]
theorem sinh_le_self_iff : sinh x ≤ x ↔ x ≤ 0 :=
  calc
    sinh x ≤ x ↔ sinh x - x ≤ sinh 0 - 0 := by simp
    _ ↔ x ≤ 0 := sinh_sub_id_strictMono.le_iff_le

@[simp]
theorem self_lt_sinh_iff : x < sinh x ↔ 0 < x :=
  lt_iff_lt_of_le_iff_le sinh_le_self_iff

@[simp]
theorem sinh_lt_self_iff : sinh x < x ↔ x < 0 :=
  lt_iff_lt_of_le_iff_le self_le_sinh_iff

end Real

section iteratedDeriv

/-! ### Simp lemmas for iterated derivatives of `sinh` and `cosh`. -/

namespace Complex

@[simp]
theorem iteratedDeriv_add_one_sinh (n : ℕ) :
    iteratedDeriv (n + 1) sinh = iteratedDeriv n cosh := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]

@[simp]
theorem iteratedDeriv_add_one_cosh (n : ℕ) :
    iteratedDeriv (n + 1) cosh = iteratedDeriv n sinh := by
  induction n with
  | zero => ext; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]

@[simp]
theorem iteratedDeriv_even_sinh (n : ℕ) :
    iteratedDeriv (2 * n) sinh = sinh := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add]

@[simp]
theorem iteratedDeriv_even_cosh (n : ℕ) :
    iteratedDeriv (2 * n) cosh = cosh := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add]

theorem iteratedDeriv_odd_sinh (n : ℕ) :
    iteratedDeriv (2 * n + 1) sinh = cosh := by simp

theorem iteratedDeriv_odd_cosh (n : ℕ) :
    iteratedDeriv (2 * n + 1) cosh = sinh := by simp

theorem differentiable_iteratedDeriv_sinh (n : ℕ) :
    Differentiable ℂ (iteratedDeriv n sinh) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_sinh]

theorem differentiable_iteratedDeriv_cosh (n : ℕ) :
    Differentiable ℂ (iteratedDeriv n cosh) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_cosh]

end Complex

namespace Real

@[simp]
theorem iteratedDeriv_add_one_sinh (n : ℕ) :
    iteratedDeriv (n + 1) sinh = iteratedDeriv n cosh := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]

@[simp]
theorem iteratedDeriv_add_one_cosh (n : ℕ) :
    iteratedDeriv (n + 1) cosh = iteratedDeriv n sinh := by
  induction n with
  | zero => ext; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]

@[simp]
theorem iteratedDeriv_even_sinh (n : ℕ) :
    iteratedDeriv (2 * n) sinh = sinh := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add]

@[simp]
theorem iteratedDeriv_even_cosh (n : ℕ) :
    iteratedDeriv (2 * n) cosh = cosh := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add]

theorem iteratedDeriv_odd_sinh (n : ℕ) :
    iteratedDeriv (2 * n + 1) sinh = cosh := by simp

theorem iteratedDeriv_odd_cosh (n : ℕ) :
    iteratedDeriv (2 * n + 1) cosh = sinh := by simp

theorem differentiable_iteratedDeriv_sinh (n : ℕ) :
    Differentiable ℝ (iteratedDeriv n sinh) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_sinh]

theorem differentiable_iteratedDeriv_cosh (n : ℕ) :
    Differentiable ℝ (iteratedDeriv n cosh) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_cosh]

@[simp]
theorem iteratedDerivWithin_sinh_Icc (n : ℕ) {a b : ℝ} (h : a < b) {x : ℝ} (hx : x ∈ Icc a b) :
    iteratedDerivWithin n sinh (Icc a b) x = iteratedDeriv n sinh x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h) contDiff_sinh.contDiffAt hx

@[simp]
theorem iteratedDerivWithin_cosh_Icc (n : ℕ) {a b : ℝ} (h : a < b) {x : ℝ} (hx : x ∈ Icc a b) :
    iteratedDerivWithin n cosh (Icc a b) x = iteratedDeriv n cosh x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h) contDiff_cosh.contDiffAt hx

@[simp]
theorem iteratedDerivWithin_sinh_Ioo (n : ℕ) {a b x : ℝ} (hx : x ∈ Ioo a b) :
    iteratedDerivWithin n sinh (Ioo a b) x = iteratedDeriv n sinh x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo a b) contDiff_sinh.contDiffAt hx

@[simp]
theorem iteratedDerivWithin_cosh_Ioo (n : ℕ) {a b x : ℝ} (hx : x ∈ Ioo a b) :
    iteratedDerivWithin n cosh (Ioo a b) x = iteratedDeriv n cosh x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo a b) contDiff_cosh.contDiffAt hx

end Real

end iteratedDeriv

section

/-! ### Simp lemmas for derivatives of `fun x => Real.cos (f x)` etc., `f : ℝ → ℝ` -/

variable {f : ℝ → ℝ} {f' x : ℝ} {s : Set ℝ}

/-! #### `Real.cosh` -/

theorem HasStrictDerivAt.cosh (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.cosh (f x)) (Real.sinh (f x) * f') x :=
  (Real.hasStrictDerivAt_cosh (f x)).comp x hf

theorem HasDerivAt.cosh (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Real.cosh (f x)) (Real.sinh (f x) * f') x :=
  (Real.hasDerivAt_cosh (f x)).comp x hf

theorem HasDerivWithinAt.cosh (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.cosh (f x)) (Real.sinh (f x) * f') s x :=
  (Real.hasDerivAt_cosh (f x)).comp_hasDerivWithinAt x hf

theorem derivWithin_cosh (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => Real.cosh (f x)) s x = Real.sinh (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.cosh.derivWithin hxs

@[simp]
theorem deriv_cosh (hc : DifferentiableAt ℝ f x) :
    deriv (fun x => Real.cosh (f x)) x = Real.sinh (f x) * deriv f x :=
  hc.hasDerivAt.cosh.deriv

/-! #### `Real.sinh` -/

theorem HasStrictDerivAt.sinh (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.sinh (f x)) (Real.cosh (f x) * f') x :=
  (Real.hasStrictDerivAt_sinh (f x)).comp x hf

theorem HasDerivAt.sinh (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Real.sinh (f x)) (Real.cosh (f x) * f') x :=
  (Real.hasDerivAt_sinh (f x)).comp x hf

theorem HasDerivWithinAt.sinh (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.sinh (f x)) (Real.cosh (f x) * f') s x :=
  (Real.hasDerivAt_sinh (f x)).comp_hasDerivWithinAt x hf

theorem derivWithin_sinh (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => Real.sinh (f x)) s x = Real.cosh (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.sinh.derivWithin hxs

@[simp]
theorem deriv_sinh (hc : DifferentiableAt ℝ f x) :
    deriv (fun x => Real.sinh (f x)) x = Real.cosh (f x) * deriv f x :=
  hc.hasDerivAt.sinh.deriv

end

section

/-! ### Simp lemmas for derivatives of `fun x => Real.cos (f x)` etc., `f : E → ℝ` -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {f' : StrongDual ℝ E}
  {x : E} {s : Set E}

/-! #### `Real.cosh` -/

theorem HasStrictFDerivAt.cosh (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Real.cosh (f x)) (Real.sinh (f x) • f') x :=
  (Real.hasStrictDerivAt_cosh (f x)).comp_hasStrictFDerivAt x hf

theorem HasFDerivAt.cosh (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Real.cosh (f x)) (Real.sinh (f x) • f') x :=
  (Real.hasDerivAt_cosh (f x)).comp_hasFDerivAt x hf

theorem HasFDerivWithinAt.cosh (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Real.cosh (f x)) (Real.sinh (f x) • f') s x :=
  (Real.hasDerivAt_cosh (f x)).comp_hasFDerivWithinAt x hf

theorem DifferentiableWithinAt.cosh (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.cosh (f x)) s x :=
  hf.hasFDerivWithinAt.cosh.differentiableWithinAt

@[simp, fun_prop]
theorem DifferentiableAt.cosh (hc : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun x => Real.cosh (f x)) x :=
  hc.hasFDerivAt.cosh.differentiableAt

theorem DifferentiableOn.cosh (hc : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun x => Real.cosh (f x)) s := fun x h => (hc x h).cosh

@[simp, fun_prop]
theorem Differentiable.cosh (hc : Differentiable ℝ f) : Differentiable ℝ fun x => Real.cosh (f x) :=
  fun x => (hc x).cosh

theorem fderivWithin_cosh (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => Real.cosh (f x)) s x = Real.sinh (f x) • fderivWithin ℝ f s x :=
  hf.hasFDerivWithinAt.cosh.fderivWithin hxs

@[simp]
theorem fderiv_cosh (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => Real.cosh (f x)) x = Real.sinh (f x) • fderiv ℝ f x :=
  hc.hasFDerivAt.cosh.fderiv

theorem ContDiff.cosh {n} (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => Real.cosh (f x) :=
  Real.contDiff_cosh.comp h

theorem ContDiffAt.cosh {n} (hf : ContDiffAt ℝ n f x) :
    ContDiffAt ℝ n (fun x => Real.cosh (f x)) x :=
  Real.contDiff_cosh.contDiffAt.comp x hf

theorem ContDiffOn.cosh {n} (hf : ContDiffOn ℝ n f s) :
    ContDiffOn ℝ n (fun x => Real.cosh (f x)) s :=
  Real.contDiff_cosh.comp_contDiffOn hf

theorem ContDiffWithinAt.cosh {n} (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun x => Real.cosh (f x)) s x :=
  Real.contDiff_cosh.contDiffAt.comp_contDiffWithinAt x hf

/-! #### `Real.sinh` -/

theorem HasStrictFDerivAt.sinh (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Real.sinh (f x)) (Real.cosh (f x) • f') x :=
  (Real.hasStrictDerivAt_sinh (f x)).comp_hasStrictFDerivAt x hf

theorem HasFDerivAt.sinh (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Real.sinh (f x)) (Real.cosh (f x) • f') x :=
  (Real.hasDerivAt_sinh (f x)).comp_hasFDerivAt x hf

theorem HasFDerivWithinAt.sinh (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Real.sinh (f x)) (Real.cosh (f x) • f') s x :=
  (Real.hasDerivAt_sinh (f x)).comp_hasFDerivWithinAt x hf

theorem DifferentiableWithinAt.sinh (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.sinh (f x)) s x :=
  hf.hasFDerivWithinAt.sinh.differentiableWithinAt

@[simp, fun_prop]
theorem DifferentiableAt.sinh (hc : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun x => Real.sinh (f x)) x :=
  hc.hasFDerivAt.sinh.differentiableAt

theorem DifferentiableOn.sinh (hc : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun x => Real.sinh (f x)) s := fun x h => (hc x h).sinh

@[simp, fun_prop]
theorem Differentiable.sinh (hc : Differentiable ℝ f) : Differentiable ℝ fun x => Real.sinh (f x) :=
  fun x => (hc x).sinh

theorem fderivWithin_sinh (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => Real.sinh (f x)) s x = Real.cosh (f x) • fderivWithin ℝ f s x :=
  hf.hasFDerivWithinAt.sinh.fderivWithin hxs

@[simp]
theorem fderiv_sinh (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => Real.sinh (f x)) x = Real.cosh (f x) • fderiv ℝ f x :=
  hc.hasFDerivAt.sinh.fderiv

theorem ContDiff.sinh {n} (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => Real.sinh (f x) :=
  Real.contDiff_sinh.comp h

theorem ContDiffAt.sinh {n} (hf : ContDiffAt ℝ n f x) :
    ContDiffAt ℝ n (fun x => Real.sinh (f x)) x :=
  Real.contDiff_sinh.contDiffAt.comp x hf

theorem ContDiffOn.sinh {n} (hf : ContDiffOn ℝ n f s) :
    ContDiffOn ℝ n (fun x => Real.sinh (f x)) s :=
  Real.contDiff_sinh.comp_contDiffOn hf

theorem ContDiffWithinAt.sinh {n} (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun x => Real.sinh (f x)) s x :=
  Real.contDiff_sinh.contDiffAt.comp_contDiffWithinAt x hf

section LogDeriv

@[simp]
theorem Complex.logDeriv_cosh : logDeriv (Complex.cosh) = Complex.tanh := by
  ext
  rw [logDeriv, Complex.deriv_cosh, Pi.div_apply, Complex.tanh]

@[simp]
theorem Real.logDeriv_cosh : logDeriv (Real.cosh) = Real.tanh := by
  ext
  rw [logDeriv, Real.deriv_cosh, Pi.div_apply, Real.tanh_eq_sinh_div_cosh]

end LogDeriv

end

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

alias ⟨_, sinh_pos_of_pos⟩ := Real.sinh_pos_iff
alias ⟨_, sinh_nonneg_of_nonneg⟩ := Real.sinh_nonneg_iff
alias ⟨_, sinh_ne_zero_of_ne_zero⟩ := Real.sinh_ne_zero

/-- Extension for the `positivity` tactic: `Real.sinh` is positive/nonnegative/nonzero if its input
is. -/
@[positivity Real.sinh _]
meta def evalSinh : PositivityExt where eval {u α} _ _ e := do
  let zα : Q(Zero ℝ) := q(inferInstance)
  let pα : Q(PartialOrder ℝ) := q(inferInstance)
  match u, α, e with
  | 0, ~q(ℝ), ~q(Real.sinh $a) =>
    assumeInstancesCommute
    match ← core zα pα a with
    | .positive pa => return .positive q(sinh_pos_of_pos $pa)
    | .nonnegative pa => return .nonnegative q(sinh_nonneg_of_nonneg $pa)
    | .nonzero pa => return .nonzero q(sinh_ne_zero_of_ne_zero $pa)
    | _ => return .none
  | _, _, _ => throwError "not Real.sinh"

example (x : ℝ) (hx : 0 < x) : 0 < x.sinh := by positivity
example (x : ℝ) (hx : 0 ≤ x) : 0 ≤ x.sinh := by positivity
example (x : ℝ) (hx : x ≠ 0) : x.sinh ≠ 0 := by positivity

end Mathlib.Meta.Positivity
