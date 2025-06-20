/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import Mathlib.Order.Monotone.Odd
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Differentiability of trigonometric functions

## Main statements

The differentiability of the usual trigonometric functions is proved, and their derivatives are
computed.

## Tags

sin, cos, tan, angle
-/

noncomputable section

open scoped Topology Filter
open Set

namespace Complex

/-- The complex sine function is everywhere strictly differentiable, with the derivative `cos x`. -/
theorem hasStrictDerivAt_sin (x : ℂ) : HasStrictDerivAt sin (cos x) x := by
  simp only [cos, div_eq_mul_inv]
  convert ((((hasStrictDerivAt_id x).neg.mul_const I).cexp.sub
    ((hasStrictDerivAt_id x).mul_const I).cexp).mul_const I).mul_const (2 : ℂ)⁻¹ using 1
  simp only [Function.comp, id]
  rw [sub_mul, mul_assoc, mul_assoc, I_mul_I, neg_one_mul, neg_neg, mul_one, one_mul, mul_assoc,
    I_mul_I, mul_neg_one, sub_neg_eq_add, add_comm]

/-- The complex sine function is everywhere differentiable, with the derivative `cos x`. -/
theorem hasDerivAt_sin (x : ℂ) : HasDerivAt sin (cos x) x :=
  (hasStrictDerivAt_sin x).hasDerivAt

theorem contDiff_sin {n} : ContDiff ℂ n sin :=
  (((contDiff_neg.mul contDiff_const).cexp.sub (contDiff_id.mul contDiff_const).cexp).mul
    contDiff_const).div_const _

@[simp]
theorem differentiable_sin : Differentiable ℂ sin := fun x => (hasDerivAt_sin x).differentiableAt

@[simp]
theorem differentiableAt_sin {x : ℂ} : DifferentiableAt ℂ sin x :=
  differentiable_sin x

/-- The function `Complex.sin` is complex analytic. -/
@[fun_prop]
lemma analyticAt_sin {x : ℂ} : AnalyticAt ℂ sin x :=
  contDiff_sin.contDiffAt.analyticAt

/-- The function `Complex.sin` is complex analytic. -/
lemma analyticWithinAt_sin {x : ℂ} {s : Set ℂ} : AnalyticWithinAt ℂ sin s x :=
  contDiff_sin.contDiffWithinAt.analyticWithinAt

/-- The function `Complex.sin` is complex analytic. -/
theorem analyticOnNhd_sin {s : Set ℂ} : AnalyticOnNhd ℂ sin s :=
  fun _ _ ↦ analyticAt_sin

/-- The function `Complex.sin` is complex analytic. -/
lemma analyticOn_sin {s : Set ℂ} : AnalyticOn ℂ sin s :=
  contDiff_sin.contDiffOn.analyticOn

@[simp]
theorem deriv_sin : deriv sin = cos :=
  funext fun x => (hasDerivAt_sin x).deriv

/-- The complex cosine function is everywhere strictly differentiable, with the derivative
`-sin x`. -/
theorem hasStrictDerivAt_cos (x : ℂ) : HasStrictDerivAt cos (-sin x) x := by
  simp only [sin, div_eq_mul_inv, neg_mul_eq_neg_mul]
  convert (((hasStrictDerivAt_id x).mul_const I).cexp.add
    ((hasStrictDerivAt_id x).neg.mul_const I).cexp).mul_const (2 : ℂ)⁻¹ using 1
  simp only [Function.comp, id]
  ring

/-- The complex cosine function is everywhere differentiable, with the derivative `-sin x`. -/
theorem hasDerivAt_cos (x : ℂ) : HasDerivAt cos (-sin x) x :=
  (hasStrictDerivAt_cos x).hasDerivAt

theorem contDiff_cos {n} : ContDiff ℂ n cos :=
  ((contDiff_id.mul contDiff_const).cexp.add (contDiff_neg.mul contDiff_const).cexp).div_const _

@[simp]
theorem differentiable_cos : Differentiable ℂ cos := fun x => (hasDerivAt_cos x).differentiableAt

@[simp]
theorem differentiableAt_cos {x : ℂ} : DifferentiableAt ℂ cos x :=
  differentiable_cos x

/-- The function `Complex.cos` is complex analytic. -/
@[fun_prop]
lemma analyticAt_cos {x : ℂ} : AnalyticAt ℂ cos x :=
  contDiff_cos.contDiffAt.analyticAt

/-- The function `Complex.cos` is complex analytic. -/
lemma analyticWithinAt_cos {x : ℂ} {s : Set ℂ} : AnalyticWithinAt ℂ cos s x :=
  contDiff_cos.contDiffWithinAt.analyticWithinAt

/-- The function `Complex.cos` is complex analytic. -/
theorem analyticOnNhd_cos {s : Set ℂ} : AnalyticOnNhd ℂ cos s :=
  fun _ _ ↦ analyticAt_cos

/-- The function `Complex.cos` is complex analytic. -/
lemma analyticOn_cos {s : Set ℂ} : AnalyticOn ℂ cos s :=
  contDiff_cos.contDiffOn.analyticOn

theorem deriv_cos {x : ℂ} : deriv cos x = -sin x :=
  (hasDerivAt_cos x).deriv

@[simp]
theorem deriv_cos' : deriv cos = fun x => -sin x :=
  funext fun _ => deriv_cos

/-- The complex hyperbolic sine function is everywhere strictly differentiable, with the derivative
`cosh x`. -/
theorem hasStrictDerivAt_sinh (x : ℂ) : HasStrictDerivAt sinh (cosh x) x := by
  simp only [cosh, div_eq_mul_inv]
  convert ((hasStrictDerivAt_exp x).sub (hasStrictDerivAt_id x).neg.cexp).mul_const (2 : ℂ)⁻¹
    using 1
  rw [id, mul_neg_one, sub_eq_add_neg, neg_neg]

/-- The complex hyperbolic sine function is everywhere differentiable, with the derivative
`cosh x`. -/
theorem hasDerivAt_sinh (x : ℂ) : HasDerivAt sinh (cosh x) x :=
  (hasStrictDerivAt_sinh x).hasDerivAt

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
  convert ((hasStrictDerivAt_exp x).add (hasStrictDerivAt_id x).neg.cexp).mul_const (2 : ℂ)⁻¹
    using 1
  rw [id, mul_neg_one, sub_eq_add_neg]

/-- The complex hyperbolic cosine function is everywhere differentiable, with the derivative
`sinh x`. -/
theorem hasDerivAt_cosh (x : ℂ) : HasDerivAt cosh (sinh x) x :=
  (hasStrictDerivAt_cosh x).hasDerivAt

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

/-! #### `Complex.cos` -/


theorem HasStrictDerivAt.ccos (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) * f') x :=
  (Complex.hasStrictDerivAt_cos (f x)).comp x hf

theorem HasDerivAt.ccos (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) * f') x :=
  (Complex.hasDerivAt_cos (f x)).comp x hf

theorem HasDerivWithinAt.ccos (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) * f') s x :=
  (Complex.hasDerivAt_cos (f x)).comp_hasDerivWithinAt x hf

theorem derivWithin_ccos (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    derivWithin (fun x => Complex.cos (f x)) s x = -Complex.sin (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.ccos.derivWithin hxs

@[simp]
theorem deriv_ccos (hc : DifferentiableAt ℂ f x) :
    deriv (fun x => Complex.cos (f x)) x = -Complex.sin (f x) * deriv f x :=
  hc.hasDerivAt.ccos.deriv

/-! #### `Complex.sin` -/


theorem HasStrictDerivAt.csin (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.sin (f x)) (Complex.cos (f x) * f') x :=
  (Complex.hasStrictDerivAt_sin (f x)).comp x hf

theorem HasDerivAt.csin (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.sin (f x)) (Complex.cos (f x) * f') x :=
  (Complex.hasDerivAt_sin (f x)).comp x hf

theorem HasDerivWithinAt.csin (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.sin (f x)) (Complex.cos (f x) * f') s x :=
  (Complex.hasDerivAt_sin (f x)).comp_hasDerivWithinAt x hf

theorem derivWithin_csin (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    derivWithin (fun x => Complex.sin (f x)) s x = Complex.cos (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.csin.derivWithin hxs

@[simp]
theorem deriv_csin (hc : DifferentiableAt ℂ f x) :
    deriv (fun x => Complex.sin (f x)) x = Complex.cos (f x) * deriv f x :=
  hc.hasDerivAt.csin.deriv

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


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ} {f' : E →L[ℂ] ℂ} {x : E}
  {s : Set E}

/-! #### `Complex.cos` -/


theorem HasStrictFDerivAt.ccos (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) • f') x :=
  (Complex.hasStrictDerivAt_cos (f x)).comp_hasStrictFDerivAt x hf

theorem HasFDerivAt.ccos (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) • f') x :=
  (Complex.hasDerivAt_cos (f x)).comp_hasFDerivAt x hf

theorem HasFDerivWithinAt.ccos (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) • f') s x :=
  (Complex.hasDerivAt_cos (f x)).comp_hasFDerivWithinAt x hf

theorem DifferentiableWithinAt.ccos (hf : DifferentiableWithinAt ℂ f s x) :
    DifferentiableWithinAt ℂ (fun x => Complex.cos (f x)) s x :=
  hf.hasFDerivWithinAt.ccos.differentiableWithinAt

@[simp, fun_prop]
theorem DifferentiableAt.ccos (hc : DifferentiableAt ℂ f x) :
    DifferentiableAt ℂ (fun x => Complex.cos (f x)) x :=
  hc.hasFDerivAt.ccos.differentiableAt

theorem DifferentiableOn.ccos (hc : DifferentiableOn ℂ f s) :
    DifferentiableOn ℂ (fun x => Complex.cos (f x)) s := fun x h => (hc x h).ccos

@[simp, fun_prop]
theorem Differentiable.ccos (hc : Differentiable ℂ f) :
    Differentiable ℂ fun x => Complex.cos (f x) := fun x => (hc x).ccos

theorem fderivWithin_ccos (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    fderivWithin ℂ (fun x => Complex.cos (f x)) s x = -Complex.sin (f x) • fderivWithin ℂ f s x :=
  hf.hasFDerivWithinAt.ccos.fderivWithin hxs

@[simp]
theorem fderiv_ccos (hc : DifferentiableAt ℂ f x) :
    fderiv ℂ (fun x => Complex.cos (f x)) x = -Complex.sin (f x) • fderiv ℂ f x :=
  hc.hasFDerivAt.ccos.fderiv

theorem ContDiff.ccos {n} (h : ContDiff ℂ n f) : ContDiff ℂ n fun x => Complex.cos (f x) :=
  Complex.contDiff_cos.comp h

theorem ContDiffAt.ccos {n} (hf : ContDiffAt ℂ n f x) :
    ContDiffAt ℂ n (fun x => Complex.cos (f x)) x :=
  Complex.contDiff_cos.contDiffAt.comp x hf

theorem ContDiffOn.ccos {n} (hf : ContDiffOn ℂ n f s) :
    ContDiffOn ℂ n (fun x => Complex.cos (f x)) s :=
  Complex.contDiff_cos.comp_contDiffOn hf

theorem ContDiffWithinAt.ccos {n} (hf : ContDiffWithinAt ℂ n f s x) :
    ContDiffWithinAt ℂ n (fun x => Complex.cos (f x)) s x :=
  Complex.contDiff_cos.contDiffAt.comp_contDiffWithinAt x hf

/-! #### `Complex.sin` -/


theorem HasStrictFDerivAt.csin (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Complex.sin (f x)) (Complex.cos (f x) • f') x :=
  (Complex.hasStrictDerivAt_sin (f x)).comp_hasStrictFDerivAt x hf

theorem HasFDerivAt.csin (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Complex.sin (f x)) (Complex.cos (f x) • f') x :=
  (Complex.hasDerivAt_sin (f x)).comp_hasFDerivAt x hf

theorem HasFDerivWithinAt.csin (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Complex.sin (f x)) (Complex.cos (f x) • f') s x :=
  (Complex.hasDerivAt_sin (f x)).comp_hasFDerivWithinAt x hf

theorem DifferentiableWithinAt.csin (hf : DifferentiableWithinAt ℂ f s x) :
    DifferentiableWithinAt ℂ (fun x => Complex.sin (f x)) s x :=
  hf.hasFDerivWithinAt.csin.differentiableWithinAt

@[simp, fun_prop]
theorem DifferentiableAt.csin (hc : DifferentiableAt ℂ f x) :
    DifferentiableAt ℂ (fun x => Complex.sin (f x)) x :=
  hc.hasFDerivAt.csin.differentiableAt

theorem DifferentiableOn.csin (hc : DifferentiableOn ℂ f s) :
    DifferentiableOn ℂ (fun x => Complex.sin (f x)) s := fun x h => (hc x h).csin

@[simp, fun_prop]
theorem Differentiable.csin (hc : Differentiable ℂ f) :
    Differentiable ℂ fun x => Complex.sin (f x) := fun x => (hc x).csin

theorem fderivWithin_csin (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    fderivWithin ℂ (fun x => Complex.sin (f x)) s x = Complex.cos (f x) • fderivWithin ℂ f s x :=
  hf.hasFDerivWithinAt.csin.fderivWithin hxs

@[simp]
theorem fderiv_csin (hc : DifferentiableAt ℂ f x) :
    fderiv ℂ (fun x => Complex.sin (f x)) x = Complex.cos (f x) • fderiv ℂ f x :=
  hc.hasFDerivAt.csin.fderiv

theorem ContDiff.csin {n} (h : ContDiff ℂ n f) : ContDiff ℂ n fun x => Complex.sin (f x) :=
  Complex.contDiff_sin.comp h

theorem ContDiffAt.csin {n} (hf : ContDiffAt ℂ n f x) :
    ContDiffAt ℂ n (fun x => Complex.sin (f x)) x :=
  Complex.contDiff_sin.contDiffAt.comp x hf

theorem ContDiffOn.csin {n} (hf : ContDiffOn ℂ n f s) :
    ContDiffOn ℂ n (fun x => Complex.sin (f x)) s :=
  Complex.contDiff_sin.comp_contDiffOn hf

theorem ContDiffWithinAt.csin {n} (hf : ContDiffWithinAt ℂ n f s x) :
    ContDiffWithinAt ℂ n (fun x => Complex.sin (f x)) s x :=
  Complex.contDiff_sin.contDiffAt.comp_contDiffWithinAt x hf

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

theorem hasStrictDerivAt_sin (x : ℝ) : HasStrictDerivAt sin (cos x) x :=
  (Complex.hasStrictDerivAt_sin x).real_of_complex

theorem hasDerivAt_sin (x : ℝ) : HasDerivAt sin (cos x) x :=
  (hasStrictDerivAt_sin x).hasDerivAt

theorem contDiff_sin {n} : ContDiff ℝ n sin :=
  Complex.contDiff_sin.real_of_complex

@[simp]
theorem differentiable_sin : Differentiable ℝ sin := fun x => (hasDerivAt_sin x).differentiableAt

@[simp]
theorem differentiableAt_sin : DifferentiableAt ℝ sin x :=
  differentiable_sin x

/-- The function `Real.sin` is real analytic. -/
@[fun_prop]
lemma analyticAt_sin : AnalyticAt ℝ sin x :=
  contDiff_sin.contDiffAt.analyticAt

/-- The function `Real.sin` is real analytic. -/
lemma analyticWithinAt_sin {s : Set ℝ} : AnalyticWithinAt ℝ sin s x :=
  contDiff_sin.contDiffWithinAt.analyticWithinAt

/-- The function `Real.sin` is real analytic. -/
theorem analyticOnNhd_sin {s : Set ℝ} : AnalyticOnNhd ℝ sin s :=
  fun _ _ ↦ analyticAt_sin

/-- The function `Real.sin` is real analytic. -/
lemma analyticOn_sin {s : Set ℝ} : AnalyticOn ℝ sin s :=
  contDiff_sin.contDiffOn.analyticOn

@[simp]
theorem deriv_sin : deriv sin = cos :=
  funext fun x => (hasDerivAt_sin x).deriv

theorem hasStrictDerivAt_cos (x : ℝ) : HasStrictDerivAt cos (-sin x) x :=
  (Complex.hasStrictDerivAt_cos x).real_of_complex

theorem hasDerivAt_cos (x : ℝ) : HasDerivAt cos (-sin x) x :=
  (Complex.hasDerivAt_cos x).real_of_complex

theorem contDiff_cos {n} : ContDiff ℝ n cos :=
  Complex.contDiff_cos.real_of_complex

@[simp]
theorem differentiable_cos : Differentiable ℝ cos := fun x => (hasDerivAt_cos x).differentiableAt

@[simp]
theorem differentiableAt_cos : DifferentiableAt ℝ cos x :=
  differentiable_cos x

/-- The function `Real.cos` is real analytic. -/
@[fun_prop]
lemma analyticAt_cos : AnalyticAt ℝ cos x :=
  contDiff_cos.contDiffAt.analyticAt

/-- The function `Real.cos` is real analytic. -/
lemma analyticWithinAt_cos {s : Set ℝ} : AnalyticWithinAt ℝ cos s x :=
  contDiff_cos.contDiffWithinAt.analyticWithinAt

/-- The function `Real.cos` is real analytic. -/
theorem analyticOnNhd_cos {s : Set ℝ} : AnalyticOnNhd ℝ cos s :=
  fun _ _ ↦ analyticAt_cos

/-- The function `Real.cos` is real analytic. -/
lemma analyticOn_cos {s : Set ℝ} : AnalyticOn ℝ cos s :=
  contDiff_cos.contDiffOn.analyticOn

theorem deriv_cos : deriv cos x = -sin x :=
  (hasDerivAt_cos x).deriv

@[simp]
theorem deriv_cos' : deriv cos = fun x => -sin x :=
  funext fun _ => deriv_cos

theorem hasStrictDerivAt_sinh (x : ℝ) : HasStrictDerivAt sinh (cosh x) x :=
  (Complex.hasStrictDerivAt_sinh x).real_of_complex

theorem hasDerivAt_sinh (x : ℝ) : HasDerivAt sinh (cosh x) x :=
  (Complex.hasDerivAt_sinh x).real_of_complex

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
    rw [deriv_sub, deriv_sinh, deriv_id'', sub_pos, one_lt_cosh]
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

section

/-! ### Simp lemmas for derivatives of `fun x => Real.cos (f x)` etc., `f : ℝ → ℝ` -/


variable {f : ℝ → ℝ} {f' x : ℝ} {s : Set ℝ}

/-! #### `Real.cos` -/


theorem HasStrictDerivAt.cos (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.cos (f x)) (-Real.sin (f x) * f') x :=
  (Real.hasStrictDerivAt_cos (f x)).comp x hf

theorem HasDerivAt.cos (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Real.cos (f x)) (-Real.sin (f x) * f') x :=
  (Real.hasDerivAt_cos (f x)).comp x hf

theorem HasDerivWithinAt.cos (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.cos (f x)) (-Real.sin (f x) * f') s x :=
  (Real.hasDerivAt_cos (f x)).comp_hasDerivWithinAt x hf

theorem derivWithin_cos (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => Real.cos (f x)) s x = -Real.sin (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.cos.derivWithin hxs

@[simp]
theorem deriv_cos (hc : DifferentiableAt ℝ f x) :
    deriv (fun x => Real.cos (f x)) x = -Real.sin (f x) * deriv f x :=
  hc.hasDerivAt.cos.deriv

/-! #### `Real.sin` -/


theorem HasStrictDerivAt.sin (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.sin (f x)) (Real.cos (f x) * f') x :=
  (Real.hasStrictDerivAt_sin (f x)).comp x hf

theorem HasDerivAt.sin (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Real.sin (f x)) (Real.cos (f x) * f') x :=
  (Real.hasDerivAt_sin (f x)).comp x hf

theorem HasDerivWithinAt.sin (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.sin (f x)) (Real.cos (f x) * f') s x :=
  (Real.hasDerivAt_sin (f x)).comp_hasDerivWithinAt x hf

theorem derivWithin_sin (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => Real.sin (f x)) s x = Real.cos (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.sin.derivWithin hxs

@[simp]
theorem deriv_sin (hc : DifferentiableAt ℝ f x) :
    deriv (fun x => Real.sin (f x)) x = Real.cos (f x) * deriv f x :=
  hc.hasDerivAt.sin.deriv

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


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x : E}
  {s : Set E}

/-! #### `Real.cos` -/


theorem HasStrictFDerivAt.cos (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Real.cos (f x)) (-Real.sin (f x) • f') x :=
  (Real.hasStrictDerivAt_cos (f x)).comp_hasStrictFDerivAt x hf

theorem HasFDerivAt.cos (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Real.cos (f x)) (-Real.sin (f x) • f') x :=
  (Real.hasDerivAt_cos (f x)).comp_hasFDerivAt x hf

theorem HasFDerivWithinAt.cos (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Real.cos (f x)) (-Real.sin (f x) • f') s x :=
  (Real.hasDerivAt_cos (f x)).comp_hasFDerivWithinAt x hf

theorem DifferentiableWithinAt.cos (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.cos (f x)) s x :=
  hf.hasFDerivWithinAt.cos.differentiableWithinAt

@[simp, fun_prop]
theorem DifferentiableAt.cos (hc : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun x => Real.cos (f x)) x :=
  hc.hasFDerivAt.cos.differentiableAt

theorem DifferentiableOn.cos (hc : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun x => Real.cos (f x)) s := fun x h => (hc x h).cos

@[simp, fun_prop]
theorem Differentiable.cos (hc : Differentiable ℝ f) : Differentiable ℝ fun x => Real.cos (f x) :=
  fun x => (hc x).cos

theorem fderivWithin_cos (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => Real.cos (f x)) s x = -Real.sin (f x) • fderivWithin ℝ f s x :=
  hf.hasFDerivWithinAt.cos.fderivWithin hxs

@[simp]
theorem fderiv_cos (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => Real.cos (f x)) x = -Real.sin (f x) • fderiv ℝ f x :=
  hc.hasFDerivAt.cos.fderiv

theorem ContDiff.cos {n} (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => Real.cos (f x) :=
  Real.contDiff_cos.comp h

theorem ContDiffAt.cos {n} (hf : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun x => Real.cos (f x)) x :=
  Real.contDiff_cos.contDiffAt.comp x hf

theorem ContDiffOn.cos {n} (hf : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun x => Real.cos (f x)) s :=
  Real.contDiff_cos.comp_contDiffOn hf

theorem ContDiffWithinAt.cos {n} (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun x => Real.cos (f x)) s x :=
  Real.contDiff_cos.contDiffAt.comp_contDiffWithinAt x hf

/-! #### `Real.sin` -/


theorem HasStrictFDerivAt.sin (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Real.sin (f x)) (Real.cos (f x) • f') x :=
  (Real.hasStrictDerivAt_sin (f x)).comp_hasStrictFDerivAt x hf

theorem HasFDerivAt.sin (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Real.sin (f x)) (Real.cos (f x) • f') x :=
  (Real.hasDerivAt_sin (f x)).comp_hasFDerivAt x hf

theorem HasFDerivWithinAt.sin (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Real.sin (f x)) (Real.cos (f x) • f') s x :=
  (Real.hasDerivAt_sin (f x)).comp_hasFDerivWithinAt x hf

theorem DifferentiableWithinAt.sin (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.sin (f x)) s x :=
  hf.hasFDerivWithinAt.sin.differentiableWithinAt

@[simp, fun_prop]
theorem DifferentiableAt.sin (hc : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun x => Real.sin (f x)) x :=
  hc.hasFDerivAt.sin.differentiableAt

theorem DifferentiableOn.sin (hc : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun x => Real.sin (f x)) s := fun x h => (hc x h).sin

@[simp, fun_prop]
theorem Differentiable.sin (hc : Differentiable ℝ f) : Differentiable ℝ fun x => Real.sin (f x) :=
  fun x => (hc x).sin

theorem fderivWithin_sin (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => Real.sin (f x)) s x = Real.cos (f x) • fderivWithin ℝ f s x :=
  hf.hasFDerivWithinAt.sin.fderivWithin hxs

@[simp]
theorem fderiv_sin (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => Real.sin (f x)) x = Real.cos (f x) • fderiv ℝ f x :=
  hc.hasFDerivAt.sin.fderiv

theorem ContDiff.sin {n} (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => Real.sin (f x) :=
  Real.contDiff_sin.comp h

theorem ContDiffAt.sin {n} (hf : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun x => Real.sin (f x)) x :=
  Real.contDiff_sin.contDiffAt.comp x hf

theorem ContDiffOn.sin {n} (hf : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun x => Real.sin (f x)) s :=
  Real.contDiff_sin.comp_contDiffOn hf

theorem ContDiffWithinAt.sin {n} (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun x => Real.sin (f x)) s x :=
  Real.contDiff_sin.contDiffAt.comp_contDiffWithinAt x hf

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
theorem Complex.logDeriv_sin : logDeriv (Complex.sin) = Complex.cot := by
  ext
  rw [logDeriv, Complex.deriv_sin, Pi.div_apply, Complex.cot]

@[simp]
theorem Real.logDeriv_sin : logDeriv (Real.sin) = Real.cot := by
  ext
  rw [logDeriv, Real.deriv_sin, Pi.div_apply, Real.cot_eq_cos_div_sin]

@[simp]
theorem Complex.logDeriv_cos : logDeriv (Complex.cos) = -Complex.tan := by
  ext
  rw [logDeriv, Complex.deriv_cos', Pi.div_apply, Pi.neg_apply, Complex.tan, neg_div]

@[simp]
theorem Real.logDeriv_cos : logDeriv (Real.cos) = -Real.tan := by
  ext
  rw [logDeriv, Real.deriv_cos', Pi.div_apply, Pi.neg_apply, neg_div, Real.tan_eq_sin_div_cos ]

@[simp]
theorem Complex.logDeriv_cosh : logDeriv (Complex.cosh) = Complex.tanh := by
  ext
  rw [logDeriv, Complex.deriv_cosh, Pi.div_apply, Complex.tanh]

@[simp]
theorem Real.logDeriv_cosh : logDeriv (Real.cosh) = Real.tanh := by
  ext
  rw [logDeriv, Real.deriv_cosh, Pi.div_apply, Real.tanh_eq_sinh_div_cosh]

@[simp]
theorem Complex.LogDeriv_exp : logDeriv (Complex.exp) = 1 := by
  ext
  rw [logDeriv, Complex.deriv_exp, Pi.div_apply, ← exp_sub, sub_self, exp_zero, Pi.one_apply]

@[simp]
theorem Real.LogDeriv_exp : logDeriv (Real.exp) = 1 := by
  ext
  rw [logDeriv, Real.deriv_exp, Pi.div_apply, ← exp_sub, sub_self, exp_zero, Pi.one_apply]

end LogDeriv

end

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

private alias ⟨_, sinh_pos_of_pos⟩ := Real.sinh_pos_iff
private alias ⟨_, sinh_nonneg_of_nonneg⟩ := Real.sinh_nonneg_iff
private alias ⟨_, sinh_ne_zero_of_ne_zero⟩ := Real.sinh_ne_zero

/-- Extension for the `positivity` tactic: `Real.sinh` is positive/nonnegative/nonzero if its input
is. -/
@[positivity Real.sinh _]
def evalSinh : PositivityExt where eval {u α} _ _ e := do
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
