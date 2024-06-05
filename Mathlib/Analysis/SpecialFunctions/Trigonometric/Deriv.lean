/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import Mathlib.Order.Monotone.Odd
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

#align_import analysis.special_functions.trigonometric.deriv from "leanprover-community/mathlib"@"2c1d8ca2812b64f88992a5294ea3dba144755cd1"

/-!
# Differentiability of trigonometric functions

## Main statements

The differentiability of the usual trigonometric functions is proved, and their derivatives are
computed.

## Tags

sin, cos, tan, angle
-/


noncomputable section

open scoped Classical Topology Filter

open Set Filter

namespace Complex

/-- The complex sine function is everywhere strictly differentiable, with the derivative `cos x`. -/
theorem hasStrictDerivAt_sin (x : ℂ) : HasStrictDerivAt sin (cos x) x := by
  simp only [cos, div_eq_mul_inv]
  convert ((((hasStrictDerivAt_id x).neg.mul_const I).cexp.sub
    ((hasStrictDerivAt_id x).mul_const I).cexp).mul_const I).mul_const (2 : ℂ)⁻¹ using 1
  simp only [Function.comp, id]
  rw [sub_mul, mul_assoc, mul_assoc, I_mul_I, neg_one_mul, neg_neg, mul_one, one_mul, mul_assoc,
    I_mul_I, mul_neg_one, sub_neg_eq_add, add_comm]
#align complex.has_strict_deriv_at_sin Complex.hasStrictDerivAt_sin

/-- The complex sine function is everywhere differentiable, with the derivative `cos x`. -/
theorem hasDerivAt_sin (x : ℂ) : HasDerivAt sin (cos x) x :=
  (hasStrictDerivAt_sin x).hasDerivAt
#align complex.has_deriv_at_sin Complex.hasDerivAt_sin

theorem contDiff_sin {n} : ContDiff ℂ n sin :=
  (((contDiff_neg.mul contDiff_const).cexp.sub (contDiff_id.mul contDiff_const).cexp).mul
    contDiff_const).div_const _
#align complex.cont_diff_sin Complex.contDiff_sin

theorem differentiable_sin : Differentiable ℂ sin := fun x => (hasDerivAt_sin x).differentiableAt
#align complex.differentiable_sin Complex.differentiable_sin

theorem differentiableAt_sin {x : ℂ} : DifferentiableAt ℂ sin x :=
  differentiable_sin x
#align complex.differentiable_at_sin Complex.differentiableAt_sin

@[simp]
theorem deriv_sin : deriv sin = cos :=
  funext fun x => (hasDerivAt_sin x).deriv
#align complex.deriv_sin Complex.deriv_sin

/-- The complex cosine function is everywhere strictly differentiable, with the derivative
`-sin x`. -/
theorem hasStrictDerivAt_cos (x : ℂ) : HasStrictDerivAt cos (-sin x) x := by
  simp only [sin, div_eq_mul_inv, neg_mul_eq_neg_mul]
  convert (((hasStrictDerivAt_id x).mul_const I).cexp.add
    ((hasStrictDerivAt_id x).neg.mul_const I).cexp).mul_const (2 : ℂ)⁻¹ using 1
  simp only [Function.comp, id]
  ring
#align complex.has_strict_deriv_at_cos Complex.hasStrictDerivAt_cos

/-- The complex cosine function is everywhere differentiable, with the derivative `-sin x`. -/
theorem hasDerivAt_cos (x : ℂ) : HasDerivAt cos (-sin x) x :=
  (hasStrictDerivAt_cos x).hasDerivAt
#align complex.has_deriv_at_cos Complex.hasDerivAt_cos

theorem contDiff_cos {n} : ContDiff ℂ n cos :=
  ((contDiff_id.mul contDiff_const).cexp.add (contDiff_neg.mul contDiff_const).cexp).div_const _
#align complex.cont_diff_cos Complex.contDiff_cos

theorem differentiable_cos : Differentiable ℂ cos := fun x => (hasDerivAt_cos x).differentiableAt
#align complex.differentiable_cos Complex.differentiable_cos

theorem differentiableAt_cos {x : ℂ} : DifferentiableAt ℂ cos x :=
  differentiable_cos x
#align complex.differentiable_at_cos Complex.differentiableAt_cos

theorem deriv_cos {x : ℂ} : deriv cos x = -sin x :=
  (hasDerivAt_cos x).deriv
#align complex.deriv_cos Complex.deriv_cos

@[simp]
theorem deriv_cos' : deriv cos = fun x => -sin x :=
  funext fun _ => deriv_cos
#align complex.deriv_cos' Complex.deriv_cos'

/-- The complex hyperbolic sine function is everywhere strictly differentiable, with the derivative
`cosh x`. -/
theorem hasStrictDerivAt_sinh (x : ℂ) : HasStrictDerivAt sinh (cosh x) x := by
  simp only [cosh, div_eq_mul_inv]
  convert ((hasStrictDerivAt_exp x).sub (hasStrictDerivAt_id x).neg.cexp).mul_const (2 : ℂ)⁻¹
    using 1
  rw [id, mul_neg_one, sub_eq_add_neg, neg_neg]
#align complex.has_strict_deriv_at_sinh Complex.hasStrictDerivAt_sinh

/-- The complex hyperbolic sine function is everywhere differentiable, with the derivative
`cosh x`. -/
theorem hasDerivAt_sinh (x : ℂ) : HasDerivAt sinh (cosh x) x :=
  (hasStrictDerivAt_sinh x).hasDerivAt
#align complex.has_deriv_at_sinh Complex.hasDerivAt_sinh

theorem contDiff_sinh {n} : ContDiff ℂ n sinh :=
  (contDiff_exp.sub contDiff_neg.cexp).div_const _
#align complex.cont_diff_sinh Complex.contDiff_sinh

theorem differentiable_sinh : Differentiable ℂ sinh := fun x => (hasDerivAt_sinh x).differentiableAt
#align complex.differentiable_sinh Complex.differentiable_sinh

theorem differentiableAt_sinh {x : ℂ} : DifferentiableAt ℂ sinh x :=
  differentiable_sinh x
#align complex.differentiable_at_sinh Complex.differentiableAt_sinh

@[simp]
theorem deriv_sinh : deriv sinh = cosh :=
  funext fun x => (hasDerivAt_sinh x).deriv
#align complex.deriv_sinh Complex.deriv_sinh

/-- The complex hyperbolic cosine function is everywhere strictly differentiable, with the
derivative `sinh x`. -/
theorem hasStrictDerivAt_cosh (x : ℂ) : HasStrictDerivAt cosh (sinh x) x := by
  simp only [sinh, div_eq_mul_inv]
  convert ((hasStrictDerivAt_exp x).add (hasStrictDerivAt_id x).neg.cexp).mul_const (2 : ℂ)⁻¹
    using 1
  rw [id, mul_neg_one, sub_eq_add_neg]
#align complex.has_strict_deriv_at_cosh Complex.hasStrictDerivAt_cosh

/-- The complex hyperbolic cosine function is everywhere differentiable, with the derivative
`sinh x`. -/
theorem hasDerivAt_cosh (x : ℂ) : HasDerivAt cosh (sinh x) x :=
  (hasStrictDerivAt_cosh x).hasDerivAt
#align complex.has_deriv_at_cosh Complex.hasDerivAt_cosh

theorem contDiff_cosh {n} : ContDiff ℂ n cosh :=
  (contDiff_exp.add contDiff_neg.cexp).div_const _
#align complex.cont_diff_cosh Complex.contDiff_cosh

theorem differentiable_cosh : Differentiable ℂ cosh := fun x => (hasDerivAt_cosh x).differentiableAt
#align complex.differentiable_cosh Complex.differentiable_cosh

theorem differentiableAt_cosh {x : ℂ} : DifferentiableAt ℂ cosh x :=
  differentiable_cosh x
#align complex.differentiable_at_cosh Complex.differentiableAt_cosh

@[simp]
theorem deriv_cosh : deriv cosh = sinh :=
  funext fun x => (hasDerivAt_cosh x).deriv
#align complex.deriv_cosh Complex.deriv_cosh

end Complex

section

/-! ### Simp lemmas for derivatives of `fun x => Complex.cos (f x)` etc., `f : ℂ → ℂ` -/


variable {f : ℂ → ℂ} {f' x : ℂ} {s : Set ℂ}

/-! #### `Complex.cos` -/


theorem HasStrictDerivAt.ccos (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) * f') x :=
  (Complex.hasStrictDerivAt_cos (f x)).comp x hf
#align has_strict_deriv_at.ccos HasStrictDerivAt.ccos

theorem HasDerivAt.ccos (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) * f') x :=
  (Complex.hasDerivAt_cos (f x)).comp x hf
#align has_deriv_at.ccos HasDerivAt.ccos

theorem HasDerivWithinAt.ccos (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) * f') s x :=
  (Complex.hasDerivAt_cos (f x)).comp_hasDerivWithinAt x hf
#align has_deriv_within_at.ccos HasDerivWithinAt.ccos

theorem derivWithin_ccos (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    derivWithin (fun x => Complex.cos (f x)) s x = -Complex.sin (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.ccos.derivWithin hxs
#align deriv_within_ccos derivWithin_ccos

@[simp]
theorem deriv_ccos (hc : DifferentiableAt ℂ f x) :
    deriv (fun x => Complex.cos (f x)) x = -Complex.sin (f x) * deriv f x :=
  hc.hasDerivAt.ccos.deriv
#align deriv_ccos deriv_ccos

/-! #### `Complex.sin` -/


theorem HasStrictDerivAt.csin (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.sin (f x)) (Complex.cos (f x) * f') x :=
  (Complex.hasStrictDerivAt_sin (f x)).comp x hf
#align has_strict_deriv_at.csin HasStrictDerivAt.csin

theorem HasDerivAt.csin (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.sin (f x)) (Complex.cos (f x) * f') x :=
  (Complex.hasDerivAt_sin (f x)).comp x hf
#align has_deriv_at.csin HasDerivAt.csin

theorem HasDerivWithinAt.csin (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.sin (f x)) (Complex.cos (f x) * f') s x :=
  (Complex.hasDerivAt_sin (f x)).comp_hasDerivWithinAt x hf
#align has_deriv_within_at.csin HasDerivWithinAt.csin

theorem derivWithin_csin (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    derivWithin (fun x => Complex.sin (f x)) s x = Complex.cos (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.csin.derivWithin hxs
#align deriv_within_csin derivWithin_csin

@[simp]
theorem deriv_csin (hc : DifferentiableAt ℂ f x) :
    deriv (fun x => Complex.sin (f x)) x = Complex.cos (f x) * deriv f x :=
  hc.hasDerivAt.csin.deriv
#align deriv_csin deriv_csin

/-! #### `Complex.cosh` -/


theorem HasStrictDerivAt.ccosh (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) * f') x :=
  (Complex.hasStrictDerivAt_cosh (f x)).comp x hf
#align has_strict_deriv_at.ccosh HasStrictDerivAt.ccosh

theorem HasDerivAt.ccosh (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) * f') x :=
  (Complex.hasDerivAt_cosh (f x)).comp x hf
#align has_deriv_at.ccosh HasDerivAt.ccosh

theorem HasDerivWithinAt.ccosh (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) * f') s x :=
  (Complex.hasDerivAt_cosh (f x)).comp_hasDerivWithinAt x hf
#align has_deriv_within_at.ccosh HasDerivWithinAt.ccosh

theorem derivWithin_ccosh (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    derivWithin (fun x => Complex.cosh (f x)) s x = Complex.sinh (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.ccosh.derivWithin hxs
#align deriv_within_ccosh derivWithin_ccosh

@[simp]
theorem deriv_ccosh (hc : DifferentiableAt ℂ f x) :
    deriv (fun x => Complex.cosh (f x)) x = Complex.sinh (f x) * deriv f x :=
  hc.hasDerivAt.ccosh.deriv
#align deriv_ccosh deriv_ccosh

/-! #### `Complex.sinh` -/


theorem HasStrictDerivAt.csinh (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) * f') x :=
  (Complex.hasStrictDerivAt_sinh (f x)).comp x hf
#align has_strict_deriv_at.csinh HasStrictDerivAt.csinh

theorem HasDerivAt.csinh (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) * f') x :=
  (Complex.hasDerivAt_sinh (f x)).comp x hf
#align has_deriv_at.csinh HasDerivAt.csinh

theorem HasDerivWithinAt.csinh (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) * f') s x :=
  (Complex.hasDerivAt_sinh (f x)).comp_hasDerivWithinAt x hf
#align has_deriv_within_at.csinh HasDerivWithinAt.csinh

theorem derivWithin_csinh (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    derivWithin (fun x => Complex.sinh (f x)) s x = Complex.cosh (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.csinh.derivWithin hxs
#align deriv_within_csinh derivWithin_csinh

@[simp]
theorem deriv_csinh (hc : DifferentiableAt ℂ f x) :
    deriv (fun x => Complex.sinh (f x)) x = Complex.cosh (f x) * deriv f x :=
  hc.hasDerivAt.csinh.deriv
#align deriv_csinh deriv_csinh

end

section

/-! ### Simp lemmas for derivatives of `fun x => Complex.cos (f x)` etc., `f : E → ℂ` -/


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ} {f' : E →L[ℂ] ℂ} {x : E}
  {s : Set E}

/-! #### `Complex.cos` -/


theorem HasStrictFDerivAt.ccos (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) • f') x :=
  (Complex.hasStrictDerivAt_cos (f x)).comp_hasStrictFDerivAt x hf
#align has_strict_fderiv_at.ccos HasStrictFDerivAt.ccos

theorem HasFDerivAt.ccos (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) • f') x :=
  (Complex.hasDerivAt_cos (f x)).comp_hasFDerivAt x hf
#align has_fderiv_at.ccos HasFDerivAt.ccos

theorem HasFDerivWithinAt.ccos (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) • f') s x :=
  (Complex.hasDerivAt_cos (f x)).comp_hasFDerivWithinAt x hf
#align has_fderiv_within_at.ccos HasFDerivWithinAt.ccos

theorem DifferentiableWithinAt.ccos (hf : DifferentiableWithinAt ℂ f s x) :
    DifferentiableWithinAt ℂ (fun x => Complex.cos (f x)) s x :=
  hf.hasFDerivWithinAt.ccos.differentiableWithinAt
#align differentiable_within_at.ccos DifferentiableWithinAt.ccos

@[simp]
theorem DifferentiableAt.ccos (hc : DifferentiableAt ℂ f x) :
    DifferentiableAt ℂ (fun x => Complex.cos (f x)) x :=
  hc.hasFDerivAt.ccos.differentiableAt
#align differentiable_at.ccos DifferentiableAt.ccos

theorem DifferentiableOn.ccos (hc : DifferentiableOn ℂ f s) :
    DifferentiableOn ℂ (fun x => Complex.cos (f x)) s := fun x h => (hc x h).ccos
#align differentiable_on.ccos DifferentiableOn.ccos

@[simp]
theorem Differentiable.ccos (hc : Differentiable ℂ f) :
    Differentiable ℂ fun x => Complex.cos (f x) := fun x => (hc x).ccos
#align differentiable.ccos Differentiable.ccos

theorem fderivWithin_ccos (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    fderivWithin ℂ (fun x => Complex.cos (f x)) s x = -Complex.sin (f x) • fderivWithin ℂ f s x :=
  hf.hasFDerivWithinAt.ccos.fderivWithin hxs
#align fderiv_within_ccos fderivWithin_ccos

@[simp, nolint simpNF] -- `simp` times out trying to find `Module ℂ (E →L[ℂ] ℂ)`
-- with all of `Mathlib` opened -- no idea why
theorem fderiv_ccos (hc : DifferentiableAt ℂ f x) :
    fderiv ℂ (fun x => Complex.cos (f x)) x = -Complex.sin (f x) • fderiv ℂ f x :=
  hc.hasFDerivAt.ccos.fderiv
#align fderiv_ccos fderiv_ccos

theorem ContDiff.ccos {n} (h : ContDiff ℂ n f) : ContDiff ℂ n fun x => Complex.cos (f x) :=
  Complex.contDiff_cos.comp h
#align cont_diff.ccos ContDiff.ccos

theorem ContDiffAt.ccos {n} (hf : ContDiffAt ℂ n f x) :
    ContDiffAt ℂ n (fun x => Complex.cos (f x)) x :=
  Complex.contDiff_cos.contDiffAt.comp x hf
#align cont_diff_at.ccos ContDiffAt.ccos

theorem ContDiffOn.ccos {n} (hf : ContDiffOn ℂ n f s) :
    ContDiffOn ℂ n (fun x => Complex.cos (f x)) s :=
  Complex.contDiff_cos.comp_contDiffOn hf
#align cont_diff_on.ccos ContDiffOn.ccos

theorem ContDiffWithinAt.ccos {n} (hf : ContDiffWithinAt ℂ n f s x) :
    ContDiffWithinAt ℂ n (fun x => Complex.cos (f x)) s x :=
  Complex.contDiff_cos.contDiffAt.comp_contDiffWithinAt x hf
#align cont_diff_within_at.ccos ContDiffWithinAt.ccos

/-! #### `Complex.sin` -/


theorem HasStrictFDerivAt.csin (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Complex.sin (f x)) (Complex.cos (f x) • f') x :=
  (Complex.hasStrictDerivAt_sin (f x)).comp_hasStrictFDerivAt x hf
#align has_strict_fderiv_at.csin HasStrictFDerivAt.csin

theorem HasFDerivAt.csin (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Complex.sin (f x)) (Complex.cos (f x) • f') x :=
  (Complex.hasDerivAt_sin (f x)).comp_hasFDerivAt x hf
#align has_fderiv_at.csin HasFDerivAt.csin

theorem HasFDerivWithinAt.csin (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Complex.sin (f x)) (Complex.cos (f x) • f') s x :=
  (Complex.hasDerivAt_sin (f x)).comp_hasFDerivWithinAt x hf
#align has_fderiv_within_at.csin HasFDerivWithinAt.csin

theorem DifferentiableWithinAt.csin (hf : DifferentiableWithinAt ℂ f s x) :
    DifferentiableWithinAt ℂ (fun x => Complex.sin (f x)) s x :=
  hf.hasFDerivWithinAt.csin.differentiableWithinAt
#align differentiable_within_at.csin DifferentiableWithinAt.csin

@[simp]
theorem DifferentiableAt.csin (hc : DifferentiableAt ℂ f x) :
    DifferentiableAt ℂ (fun x => Complex.sin (f x)) x :=
  hc.hasFDerivAt.csin.differentiableAt
#align differentiable_at.csin DifferentiableAt.csin

theorem DifferentiableOn.csin (hc : DifferentiableOn ℂ f s) :
    DifferentiableOn ℂ (fun x => Complex.sin (f x)) s := fun x h => (hc x h).csin
#align differentiable_on.csin DifferentiableOn.csin

@[simp]
theorem Differentiable.csin (hc : Differentiable ℂ f) :
    Differentiable ℂ fun x => Complex.sin (f x) := fun x => (hc x).csin
#align differentiable.csin Differentiable.csin

theorem fderivWithin_csin (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    fderivWithin ℂ (fun x => Complex.sin (f x)) s x = Complex.cos (f x) • fderivWithin ℂ f s x :=
  hf.hasFDerivWithinAt.csin.fderivWithin hxs
#align fderiv_within_csin fderivWithin_csin

@[simp]
theorem fderiv_csin (hc : DifferentiableAt ℂ f x) :
    fderiv ℂ (fun x => Complex.sin (f x)) x = Complex.cos (f x) • fderiv ℂ f x :=
  hc.hasFDerivAt.csin.fderiv
#align fderiv_csin fderiv_csin

theorem ContDiff.csin {n} (h : ContDiff ℂ n f) : ContDiff ℂ n fun x => Complex.sin (f x) :=
  Complex.contDiff_sin.comp h
#align cont_diff.csin ContDiff.csin

theorem ContDiffAt.csin {n} (hf : ContDiffAt ℂ n f x) :
    ContDiffAt ℂ n (fun x => Complex.sin (f x)) x :=
  Complex.contDiff_sin.contDiffAt.comp x hf
#align cont_diff_at.csin ContDiffAt.csin

theorem ContDiffOn.csin {n} (hf : ContDiffOn ℂ n f s) :
    ContDiffOn ℂ n (fun x => Complex.sin (f x)) s :=
  Complex.contDiff_sin.comp_contDiffOn hf
#align cont_diff_on.csin ContDiffOn.csin

theorem ContDiffWithinAt.csin {n} (hf : ContDiffWithinAt ℂ n f s x) :
    ContDiffWithinAt ℂ n (fun x => Complex.sin (f x)) s x :=
  Complex.contDiff_sin.contDiffAt.comp_contDiffWithinAt x hf
#align cont_diff_within_at.csin ContDiffWithinAt.csin

/-! #### `Complex.cosh` -/


theorem HasStrictFDerivAt.ccosh (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) • f') x :=
  (Complex.hasStrictDerivAt_cosh (f x)).comp_hasStrictFDerivAt x hf
#align has_strict_fderiv_at.ccosh HasStrictFDerivAt.ccosh

theorem HasFDerivAt.ccosh (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) • f') x :=
  (Complex.hasDerivAt_cosh (f x)).comp_hasFDerivAt x hf
#align has_fderiv_at.ccosh HasFDerivAt.ccosh

theorem HasFDerivWithinAt.ccosh (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) • f') s x :=
  (Complex.hasDerivAt_cosh (f x)).comp_hasFDerivWithinAt x hf
#align has_fderiv_within_at.ccosh HasFDerivWithinAt.ccosh

theorem DifferentiableWithinAt.ccosh (hf : DifferentiableWithinAt ℂ f s x) :
    DifferentiableWithinAt ℂ (fun x => Complex.cosh (f x)) s x :=
  hf.hasFDerivWithinAt.ccosh.differentiableWithinAt
#align differentiable_within_at.ccosh DifferentiableWithinAt.ccosh

@[simp]
theorem DifferentiableAt.ccosh (hc : DifferentiableAt ℂ f x) :
    DifferentiableAt ℂ (fun x => Complex.cosh (f x)) x :=
  hc.hasFDerivAt.ccosh.differentiableAt
#align differentiable_at.ccosh DifferentiableAt.ccosh

theorem DifferentiableOn.ccosh (hc : DifferentiableOn ℂ f s) :
    DifferentiableOn ℂ (fun x => Complex.cosh (f x)) s := fun x h => (hc x h).ccosh
#align differentiable_on.ccosh DifferentiableOn.ccosh

@[simp]
theorem Differentiable.ccosh (hc : Differentiable ℂ f) :
    Differentiable ℂ fun x => Complex.cosh (f x) := fun x => (hc x).ccosh
#align differentiable.ccosh Differentiable.ccosh

theorem fderivWithin_ccosh (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    fderivWithin ℂ (fun x => Complex.cosh (f x)) s x = Complex.sinh (f x) • fderivWithin ℂ f s x :=
  hf.hasFDerivWithinAt.ccosh.fderivWithin hxs
#align fderiv_within_ccosh fderivWithin_ccosh

@[simp]
theorem fderiv_ccosh (hc : DifferentiableAt ℂ f x) :
    fderiv ℂ (fun x => Complex.cosh (f x)) x = Complex.sinh (f x) • fderiv ℂ f x :=
  hc.hasFDerivAt.ccosh.fderiv
#align fderiv_ccosh fderiv_ccosh

theorem ContDiff.ccosh {n} (h : ContDiff ℂ n f) : ContDiff ℂ n fun x => Complex.cosh (f x) :=
  Complex.contDiff_cosh.comp h
#align cont_diff.ccosh ContDiff.ccosh

theorem ContDiffAt.ccosh {n} (hf : ContDiffAt ℂ n f x) :
    ContDiffAt ℂ n (fun x => Complex.cosh (f x)) x :=
  Complex.contDiff_cosh.contDiffAt.comp x hf
#align cont_diff_at.ccosh ContDiffAt.ccosh

theorem ContDiffOn.ccosh {n} (hf : ContDiffOn ℂ n f s) :
    ContDiffOn ℂ n (fun x => Complex.cosh (f x)) s :=
  Complex.contDiff_cosh.comp_contDiffOn hf
#align cont_diff_on.ccosh ContDiffOn.ccosh

theorem ContDiffWithinAt.ccosh {n} (hf : ContDiffWithinAt ℂ n f s x) :
    ContDiffWithinAt ℂ n (fun x => Complex.cosh (f x)) s x :=
  Complex.contDiff_cosh.contDiffAt.comp_contDiffWithinAt x hf
#align cont_diff_within_at.ccosh ContDiffWithinAt.ccosh

/-! #### `Complex.sinh` -/


theorem HasStrictFDerivAt.csinh (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) • f') x :=
  (Complex.hasStrictDerivAt_sinh (f x)).comp_hasStrictFDerivAt x hf
#align has_strict_fderiv_at.csinh HasStrictFDerivAt.csinh

theorem HasFDerivAt.csinh (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) • f') x :=
  (Complex.hasDerivAt_sinh (f x)).comp_hasFDerivAt x hf
#align has_fderiv_at.csinh HasFDerivAt.csinh

theorem HasFDerivWithinAt.csinh (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) • f') s x :=
  (Complex.hasDerivAt_sinh (f x)).comp_hasFDerivWithinAt x hf
#align has_fderiv_within_at.csinh HasFDerivWithinAt.csinh

theorem DifferentiableWithinAt.csinh (hf : DifferentiableWithinAt ℂ f s x) :
    DifferentiableWithinAt ℂ (fun x => Complex.sinh (f x)) s x :=
  hf.hasFDerivWithinAt.csinh.differentiableWithinAt
#align differentiable_within_at.csinh DifferentiableWithinAt.csinh

@[simp]
theorem DifferentiableAt.csinh (hc : DifferentiableAt ℂ f x) :
    DifferentiableAt ℂ (fun x => Complex.sinh (f x)) x :=
  hc.hasFDerivAt.csinh.differentiableAt
#align differentiable_at.csinh DifferentiableAt.csinh

theorem DifferentiableOn.csinh (hc : DifferentiableOn ℂ f s) :
    DifferentiableOn ℂ (fun x => Complex.sinh (f x)) s := fun x h => (hc x h).csinh
#align differentiable_on.csinh DifferentiableOn.csinh

@[simp]
theorem Differentiable.csinh (hc : Differentiable ℂ f) :
    Differentiable ℂ fun x => Complex.sinh (f x) := fun x => (hc x).csinh
#align differentiable.csinh Differentiable.csinh

theorem fderivWithin_csinh (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    fderivWithin ℂ (fun x => Complex.sinh (f x)) s x = Complex.cosh (f x) • fderivWithin ℂ f s x :=
  hf.hasFDerivWithinAt.csinh.fderivWithin hxs
#align fderiv_within_csinh fderivWithin_csinh

@[simp]
theorem fderiv_csinh (hc : DifferentiableAt ℂ f x) :
    fderiv ℂ (fun x => Complex.sinh (f x)) x = Complex.cosh (f x) • fderiv ℂ f x :=
  hc.hasFDerivAt.csinh.fderiv
#align fderiv_csinh fderiv_csinh

theorem ContDiff.csinh {n} (h : ContDiff ℂ n f) : ContDiff ℂ n fun x => Complex.sinh (f x) :=
  Complex.contDiff_sinh.comp h
#align cont_diff.csinh ContDiff.csinh

theorem ContDiffAt.csinh {n} (hf : ContDiffAt ℂ n f x) :
    ContDiffAt ℂ n (fun x => Complex.sinh (f x)) x :=
  Complex.contDiff_sinh.contDiffAt.comp x hf
#align cont_diff_at.csinh ContDiffAt.csinh

theorem ContDiffOn.csinh {n} (hf : ContDiffOn ℂ n f s) :
    ContDiffOn ℂ n (fun x => Complex.sinh (f x)) s :=
  Complex.contDiff_sinh.comp_contDiffOn hf
#align cont_diff_on.csinh ContDiffOn.csinh

theorem ContDiffWithinAt.csinh {n} (hf : ContDiffWithinAt ℂ n f s x) :
    ContDiffWithinAt ℂ n (fun x => Complex.sinh (f x)) s x :=
  Complex.contDiff_sinh.contDiffAt.comp_contDiffWithinAt x hf
#align cont_diff_within_at.csinh ContDiffWithinAt.csinh

end

namespace Real

variable {x y z : ℝ}

theorem hasStrictDerivAt_sin (x : ℝ) : HasStrictDerivAt sin (cos x) x :=
  (Complex.hasStrictDerivAt_sin x).real_of_complex
#align real.has_strict_deriv_at_sin Real.hasStrictDerivAt_sin

theorem hasDerivAt_sin (x : ℝ) : HasDerivAt sin (cos x) x :=
  (hasStrictDerivAt_sin x).hasDerivAt
#align real.has_deriv_at_sin Real.hasDerivAt_sin

theorem contDiff_sin {n} : ContDiff ℝ n sin :=
  Complex.contDiff_sin.real_of_complex
#align real.cont_diff_sin Real.contDiff_sin

theorem differentiable_sin : Differentiable ℝ sin := fun x => (hasDerivAt_sin x).differentiableAt
#align real.differentiable_sin Real.differentiable_sin

theorem differentiableAt_sin : DifferentiableAt ℝ sin x :=
  differentiable_sin x
#align real.differentiable_at_sin Real.differentiableAt_sin

@[simp]
theorem deriv_sin : deriv sin = cos :=
  funext fun x => (hasDerivAt_sin x).deriv
#align real.deriv_sin Real.deriv_sin

theorem hasStrictDerivAt_cos (x : ℝ) : HasStrictDerivAt cos (-sin x) x :=
  (Complex.hasStrictDerivAt_cos x).real_of_complex
#align real.has_strict_deriv_at_cos Real.hasStrictDerivAt_cos

theorem hasDerivAt_cos (x : ℝ) : HasDerivAt cos (-sin x) x :=
  (Complex.hasDerivAt_cos x).real_of_complex
#align real.has_deriv_at_cos Real.hasDerivAt_cos

theorem contDiff_cos {n} : ContDiff ℝ n cos :=
  Complex.contDiff_cos.real_of_complex
#align real.cont_diff_cos Real.contDiff_cos

theorem differentiable_cos : Differentiable ℝ cos := fun x => (hasDerivAt_cos x).differentiableAt
#align real.differentiable_cos Real.differentiable_cos

theorem differentiableAt_cos : DifferentiableAt ℝ cos x :=
  differentiable_cos x
#align real.differentiable_at_cos Real.differentiableAt_cos

theorem deriv_cos : deriv cos x = -sin x :=
  (hasDerivAt_cos x).deriv
#align real.deriv_cos Real.deriv_cos

@[simp]
theorem deriv_cos' : deriv cos = fun x => -sin x :=
  funext fun _ => deriv_cos
#align real.deriv_cos' Real.deriv_cos'

theorem hasStrictDerivAt_sinh (x : ℝ) : HasStrictDerivAt sinh (cosh x) x :=
  (Complex.hasStrictDerivAt_sinh x).real_of_complex
#align real.has_strict_deriv_at_sinh Real.hasStrictDerivAt_sinh

theorem hasDerivAt_sinh (x : ℝ) : HasDerivAt sinh (cosh x) x :=
  (Complex.hasDerivAt_sinh x).real_of_complex
#align real.has_deriv_at_sinh Real.hasDerivAt_sinh

theorem contDiff_sinh {n} : ContDiff ℝ n sinh :=
  Complex.contDiff_sinh.real_of_complex
#align real.cont_diff_sinh Real.contDiff_sinh

theorem differentiable_sinh : Differentiable ℝ sinh := fun x => (hasDerivAt_sinh x).differentiableAt
#align real.differentiable_sinh Real.differentiable_sinh

theorem differentiableAt_sinh : DifferentiableAt ℝ sinh x :=
  differentiable_sinh x
#align real.differentiable_at_sinh Real.differentiableAt_sinh

@[simp]
theorem deriv_sinh : deriv sinh = cosh :=
  funext fun x => (hasDerivAt_sinh x).deriv
#align real.deriv_sinh Real.deriv_sinh

theorem hasStrictDerivAt_cosh (x : ℝ) : HasStrictDerivAt cosh (sinh x) x :=
  (Complex.hasStrictDerivAt_cosh x).real_of_complex
#align real.has_strict_deriv_at_cosh Real.hasStrictDerivAt_cosh

theorem hasDerivAt_cosh (x : ℝ) : HasDerivAt cosh (sinh x) x :=
  (Complex.hasDerivAt_cosh x).real_of_complex
#align real.has_deriv_at_cosh Real.hasDerivAt_cosh

theorem contDiff_cosh {n} : ContDiff ℝ n cosh :=
  Complex.contDiff_cosh.real_of_complex
#align real.cont_diff_cosh Real.contDiff_cosh

theorem differentiable_cosh : Differentiable ℝ cosh := fun x => (hasDerivAt_cosh x).differentiableAt
#align real.differentiable_cosh Real.differentiable_cosh

theorem differentiableAt_cosh : DifferentiableAt ℝ cosh x :=
  differentiable_cosh x
#align real.differentiable_at_cosh Real.differentiableAt_cosh

@[simp]
theorem deriv_cosh : deriv cosh = sinh :=
  funext fun x => (hasDerivAt_cosh x).deriv
#align real.deriv_cosh Real.deriv_cosh

/-- `sinh` is strictly monotone. -/
theorem sinh_strictMono : StrictMono sinh :=
  strictMono_of_deriv_pos <| by rw [Real.deriv_sinh]; exact cosh_pos
#align real.sinh_strict_mono Real.sinh_strictMono

/-- `sinh` is injective, `∀ a b, sinh a = sinh b → a = b`. -/
theorem sinh_injective : Function.Injective sinh :=
  sinh_strictMono.injective
#align real.sinh_injective Real.sinh_injective

@[simp]
theorem sinh_inj : sinh x = sinh y ↔ x = y :=
  sinh_injective.eq_iff
#align real.sinh_inj Real.sinh_inj

@[simp]
theorem sinh_le_sinh : sinh x ≤ sinh y ↔ x ≤ y :=
  sinh_strictMono.le_iff_le
#align real.sinh_le_sinh Real.sinh_le_sinh

@[simp]
theorem sinh_lt_sinh : sinh x < sinh y ↔ x < y :=
  sinh_strictMono.lt_iff_lt
#align real.sinh_lt_sinh Real.sinh_lt_sinh

@[simp] lemma sinh_eq_zero : sinh x = 0 ↔ x = 0 := by rw [← @sinh_inj x, sinh_zero]

lemma sinh_ne_zero : sinh x ≠ 0 ↔ x ≠ 0 := sinh_eq_zero.not

@[simp]
theorem sinh_pos_iff : 0 < sinh x ↔ 0 < x := by simpa only [sinh_zero] using @sinh_lt_sinh 0 x
#align real.sinh_pos_iff Real.sinh_pos_iff

@[simp]
theorem sinh_nonpos_iff : sinh x ≤ 0 ↔ x ≤ 0 := by simpa only [sinh_zero] using @sinh_le_sinh x 0
#align real.sinh_nonpos_iff Real.sinh_nonpos_iff

@[simp]
theorem sinh_neg_iff : sinh x < 0 ↔ x < 0 := by simpa only [sinh_zero] using @sinh_lt_sinh x 0
#align real.sinh_neg_iff Real.sinh_neg_iff

@[simp]
theorem sinh_nonneg_iff : 0 ≤ sinh x ↔ 0 ≤ x := by simpa only [sinh_zero] using @sinh_le_sinh 0 x
#align real.sinh_nonneg_iff Real.sinh_nonneg_iff

theorem abs_sinh (x : ℝ) : |sinh x| = sinh |x| := by
  cases le_total x 0 <;> simp [abs_of_nonneg, abs_of_nonpos, *]
#align real.abs_sinh Real.abs_sinh

theorem cosh_strictMonoOn : StrictMonoOn cosh (Ici 0) :=
  strictMonoOn_of_deriv_pos (convex_Ici _) continuous_cosh.continuousOn fun x hx => by
    rw [interior_Ici, mem_Ioi] at hx; rwa [deriv_cosh, sinh_pos_iff]
#align real.cosh_strict_mono_on Real.cosh_strictMonoOn

@[simp]
theorem cosh_le_cosh : cosh x ≤ cosh y ↔ |x| ≤ |y| :=
  cosh_abs x ▸ cosh_abs y ▸ cosh_strictMonoOn.le_iff_le (abs_nonneg x) (abs_nonneg y)
#align real.cosh_le_cosh Real.cosh_le_cosh

@[simp]
theorem cosh_lt_cosh : cosh x < cosh y ↔ |x| < |y| :=
  lt_iff_lt_of_le_iff_le cosh_le_cosh
#align real.cosh_lt_cosh Real.cosh_lt_cosh

@[simp]
theorem one_le_cosh (x : ℝ) : 1 ≤ cosh x :=
  cosh_zero ▸ cosh_le_cosh.2 (by simp only [_root_.abs_zero, _root_.abs_nonneg])
#align real.one_le_cosh Real.one_le_cosh

@[simp]
theorem one_lt_cosh : 1 < cosh x ↔ x ≠ 0 :=
  cosh_zero ▸ cosh_lt_cosh.trans (by simp only [_root_.abs_zero, abs_pos])
#align real.one_lt_cosh Real.one_lt_cosh

theorem sinh_sub_id_strictMono : StrictMono fun x => sinh x - x := by
  -- Porting note: `by simp; abel` was just `by simp` in mathlib3.
  refine strictMono_of_odd_strictMonoOn_nonneg (fun x => by simp; abel) ?_
  refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ fun x hx => ?_
  · exact (continuous_sinh.sub continuous_id).continuousOn
  · rw [interior_Ici, mem_Ioi] at hx
    rw [deriv_sub, deriv_sinh, deriv_id'', sub_pos, one_lt_cosh]
    exacts [hx.ne', differentiableAt_sinh, differentiableAt_id]
#align real.sinh_sub_id_strict_mono Real.sinh_sub_id_strictMono

@[simp]
theorem self_le_sinh_iff : x ≤ sinh x ↔ 0 ≤ x :=
  calc
    x ≤ sinh x ↔ sinh 0 - 0 ≤ sinh x - x := by simp
    _ ↔ 0 ≤ x := sinh_sub_id_strictMono.le_iff_le

#align real.self_le_sinh_iff Real.self_le_sinh_iff

@[simp]
theorem sinh_le_self_iff : sinh x ≤ x ↔ x ≤ 0 :=
  calc
    sinh x ≤ x ↔ sinh x - x ≤ sinh 0 - 0 := by simp
    _ ↔ x ≤ 0 := sinh_sub_id_strictMono.le_iff_le

#align real.sinh_le_self_iff Real.sinh_le_self_iff

@[simp]
theorem self_lt_sinh_iff : x < sinh x ↔ 0 < x :=
  lt_iff_lt_of_le_iff_le sinh_le_self_iff
#align real.self_lt_sinh_iff Real.self_lt_sinh_iff

@[simp]
theorem sinh_lt_self_iff : sinh x < x ↔ x < 0 :=
  lt_iff_lt_of_le_iff_le self_le_sinh_iff
#align real.sinh_lt_self_iff Real.sinh_lt_self_iff

end Real

section

/-! ### Simp lemmas for derivatives of `fun x => Real.cos (f x)` etc., `f : ℝ → ℝ` -/


variable {f : ℝ → ℝ} {f' x : ℝ} {s : Set ℝ}

/-! #### `Real.cos` -/


theorem HasStrictDerivAt.cos (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.cos (f x)) (-Real.sin (f x) * f') x :=
  (Real.hasStrictDerivAt_cos (f x)).comp x hf
#align has_strict_deriv_at.cos HasStrictDerivAt.cos

theorem HasDerivAt.cos (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Real.cos (f x)) (-Real.sin (f x) * f') x :=
  (Real.hasDerivAt_cos (f x)).comp x hf
#align has_deriv_at.cos HasDerivAt.cos

theorem HasDerivWithinAt.cos (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.cos (f x)) (-Real.sin (f x) * f') s x :=
  (Real.hasDerivAt_cos (f x)).comp_hasDerivWithinAt x hf
#align has_deriv_within_at.cos HasDerivWithinAt.cos

theorem derivWithin_cos (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => Real.cos (f x)) s x = -Real.sin (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.cos.derivWithin hxs
#align deriv_within_cos derivWithin_cos

@[simp]
theorem deriv_cos (hc : DifferentiableAt ℝ f x) :
    deriv (fun x => Real.cos (f x)) x = -Real.sin (f x) * deriv f x :=
  hc.hasDerivAt.cos.deriv
#align deriv_cos deriv_cos

/-! #### `Real.sin` -/


theorem HasStrictDerivAt.sin (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.sin (f x)) (Real.cos (f x) * f') x :=
  (Real.hasStrictDerivAt_sin (f x)).comp x hf
#align has_strict_deriv_at.sin HasStrictDerivAt.sin

theorem HasDerivAt.sin (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Real.sin (f x)) (Real.cos (f x) * f') x :=
  (Real.hasDerivAt_sin (f x)).comp x hf
#align has_deriv_at.sin HasDerivAt.sin

theorem HasDerivWithinAt.sin (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.sin (f x)) (Real.cos (f x) * f') s x :=
  (Real.hasDerivAt_sin (f x)).comp_hasDerivWithinAt x hf
#align has_deriv_within_at.sin HasDerivWithinAt.sin

theorem derivWithin_sin (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => Real.sin (f x)) s x = Real.cos (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.sin.derivWithin hxs
#align deriv_within_sin derivWithin_sin

@[simp]
theorem deriv_sin (hc : DifferentiableAt ℝ f x) :
    deriv (fun x => Real.sin (f x)) x = Real.cos (f x) * deriv f x :=
  hc.hasDerivAt.sin.deriv
#align deriv_sin deriv_sin

/-! #### `Real.cosh` -/


theorem HasStrictDerivAt.cosh (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.cosh (f x)) (Real.sinh (f x) * f') x :=
  (Real.hasStrictDerivAt_cosh (f x)).comp x hf
#align has_strict_deriv_at.cosh HasStrictDerivAt.cosh

theorem HasDerivAt.cosh (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Real.cosh (f x)) (Real.sinh (f x) * f') x :=
  (Real.hasDerivAt_cosh (f x)).comp x hf
#align has_deriv_at.cosh HasDerivAt.cosh

theorem HasDerivWithinAt.cosh (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.cosh (f x)) (Real.sinh (f x) * f') s x :=
  (Real.hasDerivAt_cosh (f x)).comp_hasDerivWithinAt x hf
#align has_deriv_within_at.cosh HasDerivWithinAt.cosh

theorem derivWithin_cosh (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => Real.cosh (f x)) s x = Real.sinh (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.cosh.derivWithin hxs
#align deriv_within_cosh derivWithin_cosh

@[simp]
theorem deriv_cosh (hc : DifferentiableAt ℝ f x) :
    deriv (fun x => Real.cosh (f x)) x = Real.sinh (f x) * deriv f x :=
  hc.hasDerivAt.cosh.deriv
#align deriv_cosh deriv_cosh

/-! #### `Real.sinh` -/


theorem HasStrictDerivAt.sinh (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.sinh (f x)) (Real.cosh (f x) * f') x :=
  (Real.hasStrictDerivAt_sinh (f x)).comp x hf
#align has_strict_deriv_at.sinh HasStrictDerivAt.sinh

theorem HasDerivAt.sinh (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Real.sinh (f x)) (Real.cosh (f x) * f') x :=
  (Real.hasDerivAt_sinh (f x)).comp x hf
#align has_deriv_at.sinh HasDerivAt.sinh

theorem HasDerivWithinAt.sinh (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.sinh (f x)) (Real.cosh (f x) * f') s x :=
  (Real.hasDerivAt_sinh (f x)).comp_hasDerivWithinAt x hf
#align has_deriv_within_at.sinh HasDerivWithinAt.sinh

theorem derivWithin_sinh (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => Real.sinh (f x)) s x = Real.cosh (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.sinh.derivWithin hxs
#align deriv_within_sinh derivWithin_sinh

@[simp]
theorem deriv_sinh (hc : DifferentiableAt ℝ f x) :
    deriv (fun x => Real.sinh (f x)) x = Real.cosh (f x) * deriv f x :=
  hc.hasDerivAt.sinh.deriv
#align deriv_sinh deriv_sinh

end

section

/-! ### Simp lemmas for derivatives of `fun x => Real.cos (f x)` etc., `f : E → ℝ` -/


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x : E}
  {s : Set E}

/-! #### `Real.cos` -/


theorem HasStrictFDerivAt.cos (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Real.cos (f x)) (-Real.sin (f x) • f') x :=
  (Real.hasStrictDerivAt_cos (f x)).comp_hasStrictFDerivAt x hf
#align has_strict_fderiv_at.cos HasStrictFDerivAt.cos

theorem HasFDerivAt.cos (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Real.cos (f x)) (-Real.sin (f x) • f') x :=
  (Real.hasDerivAt_cos (f x)).comp_hasFDerivAt x hf
#align has_fderiv_at.cos HasFDerivAt.cos

theorem HasFDerivWithinAt.cos (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Real.cos (f x)) (-Real.sin (f x) • f') s x :=
  (Real.hasDerivAt_cos (f x)).comp_hasFDerivWithinAt x hf
#align has_fderiv_within_at.cos HasFDerivWithinAt.cos

theorem DifferentiableWithinAt.cos (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.cos (f x)) s x :=
  hf.hasFDerivWithinAt.cos.differentiableWithinAt
#align differentiable_within_at.cos DifferentiableWithinAt.cos

@[simp]
theorem DifferentiableAt.cos (hc : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun x => Real.cos (f x)) x :=
  hc.hasFDerivAt.cos.differentiableAt
#align differentiable_at.cos DifferentiableAt.cos

theorem DifferentiableOn.cos (hc : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun x => Real.cos (f x)) s := fun x h => (hc x h).cos
#align differentiable_on.cos DifferentiableOn.cos

@[simp]
theorem Differentiable.cos (hc : Differentiable ℝ f) : Differentiable ℝ fun x => Real.cos (f x) :=
  fun x => (hc x).cos
#align differentiable.cos Differentiable.cos

theorem fderivWithin_cos (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => Real.cos (f x)) s x = -Real.sin (f x) • fderivWithin ℝ f s x :=
  hf.hasFDerivWithinAt.cos.fderivWithin hxs
#align fderiv_within_cos fderivWithin_cos

@[simp]
theorem fderiv_cos (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => Real.cos (f x)) x = -Real.sin (f x) • fderiv ℝ f x :=
  hc.hasFDerivAt.cos.fderiv
#align fderiv_cos fderiv_cos

theorem ContDiff.cos {n} (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => Real.cos (f x) :=
  Real.contDiff_cos.comp h
#align cont_diff.cos ContDiff.cos

theorem ContDiffAt.cos {n} (hf : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun x => Real.cos (f x)) x :=
  Real.contDiff_cos.contDiffAt.comp x hf
#align cont_diff_at.cos ContDiffAt.cos

theorem ContDiffOn.cos {n} (hf : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun x => Real.cos (f x)) s :=
  Real.contDiff_cos.comp_contDiffOn hf
#align cont_diff_on.cos ContDiffOn.cos

theorem ContDiffWithinAt.cos {n} (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun x => Real.cos (f x)) s x :=
  Real.contDiff_cos.contDiffAt.comp_contDiffWithinAt x hf
#align cont_diff_within_at.cos ContDiffWithinAt.cos

/-! #### `Real.sin` -/


theorem HasStrictFDerivAt.sin (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Real.sin (f x)) (Real.cos (f x) • f') x :=
  (Real.hasStrictDerivAt_sin (f x)).comp_hasStrictFDerivAt x hf
#align has_strict_fderiv_at.sin HasStrictFDerivAt.sin

theorem HasFDerivAt.sin (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Real.sin (f x)) (Real.cos (f x) • f') x :=
  (Real.hasDerivAt_sin (f x)).comp_hasFDerivAt x hf
#align has_fderiv_at.sin HasFDerivAt.sin

theorem HasFDerivWithinAt.sin (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Real.sin (f x)) (Real.cos (f x) • f') s x :=
  (Real.hasDerivAt_sin (f x)).comp_hasFDerivWithinAt x hf
#align has_fderiv_within_at.sin HasFDerivWithinAt.sin

theorem DifferentiableWithinAt.sin (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.sin (f x)) s x :=
  hf.hasFDerivWithinAt.sin.differentiableWithinAt
#align differentiable_within_at.sin DifferentiableWithinAt.sin

@[simp]
theorem DifferentiableAt.sin (hc : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun x => Real.sin (f x)) x :=
  hc.hasFDerivAt.sin.differentiableAt
#align differentiable_at.sin DifferentiableAt.sin

theorem DifferentiableOn.sin (hc : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun x => Real.sin (f x)) s := fun x h => (hc x h).sin
#align differentiable_on.sin DifferentiableOn.sin

@[simp]
theorem Differentiable.sin (hc : Differentiable ℝ f) : Differentiable ℝ fun x => Real.sin (f x) :=
  fun x => (hc x).sin
#align differentiable.sin Differentiable.sin

theorem fderivWithin_sin (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => Real.sin (f x)) s x = Real.cos (f x) • fderivWithin ℝ f s x :=
  hf.hasFDerivWithinAt.sin.fderivWithin hxs
#align fderiv_within_sin fderivWithin_sin

@[simp]
theorem fderiv_sin (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => Real.sin (f x)) x = Real.cos (f x) • fderiv ℝ f x :=
  hc.hasFDerivAt.sin.fderiv
#align fderiv_sin fderiv_sin

theorem ContDiff.sin {n} (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => Real.sin (f x) :=
  Real.contDiff_sin.comp h
#align cont_diff.sin ContDiff.sin

theorem ContDiffAt.sin {n} (hf : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun x => Real.sin (f x)) x :=
  Real.contDiff_sin.contDiffAt.comp x hf
#align cont_diff_at.sin ContDiffAt.sin

theorem ContDiffOn.sin {n} (hf : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun x => Real.sin (f x)) s :=
  Real.contDiff_sin.comp_contDiffOn hf
#align cont_diff_on.sin ContDiffOn.sin

theorem ContDiffWithinAt.sin {n} (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun x => Real.sin (f x)) s x :=
  Real.contDiff_sin.contDiffAt.comp_contDiffWithinAt x hf
#align cont_diff_within_at.sin ContDiffWithinAt.sin

/-! #### `Real.cosh` -/


theorem HasStrictFDerivAt.cosh (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Real.cosh (f x)) (Real.sinh (f x) • f') x :=
  (Real.hasStrictDerivAt_cosh (f x)).comp_hasStrictFDerivAt x hf
#align has_strict_fderiv_at.cosh HasStrictFDerivAt.cosh

theorem HasFDerivAt.cosh (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Real.cosh (f x)) (Real.sinh (f x) • f') x :=
  (Real.hasDerivAt_cosh (f x)).comp_hasFDerivAt x hf
#align has_fderiv_at.cosh HasFDerivAt.cosh

theorem HasFDerivWithinAt.cosh (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Real.cosh (f x)) (Real.sinh (f x) • f') s x :=
  (Real.hasDerivAt_cosh (f x)).comp_hasFDerivWithinAt x hf
#align has_fderiv_within_at.cosh HasFDerivWithinAt.cosh

theorem DifferentiableWithinAt.cosh (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.cosh (f x)) s x :=
  hf.hasFDerivWithinAt.cosh.differentiableWithinAt
#align differentiable_within_at.cosh DifferentiableWithinAt.cosh

@[simp]
theorem DifferentiableAt.cosh (hc : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun x => Real.cosh (f x)) x :=
  hc.hasFDerivAt.cosh.differentiableAt
#align differentiable_at.cosh DifferentiableAt.cosh

theorem DifferentiableOn.cosh (hc : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun x => Real.cosh (f x)) s := fun x h => (hc x h).cosh
#align differentiable_on.cosh DifferentiableOn.cosh

@[simp]
theorem Differentiable.cosh (hc : Differentiable ℝ f) : Differentiable ℝ fun x => Real.cosh (f x) :=
  fun x => (hc x).cosh
#align differentiable.cosh Differentiable.cosh

theorem fderivWithin_cosh (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => Real.cosh (f x)) s x = Real.sinh (f x) • fderivWithin ℝ f s x :=
  hf.hasFDerivWithinAt.cosh.fderivWithin hxs
#align fderiv_within_cosh fderivWithin_cosh

@[simp]
theorem fderiv_cosh (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => Real.cosh (f x)) x = Real.sinh (f x) • fderiv ℝ f x :=
  hc.hasFDerivAt.cosh.fderiv
#align fderiv_cosh fderiv_cosh

theorem ContDiff.cosh {n} (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => Real.cosh (f x) :=
  Real.contDiff_cosh.comp h
#align cont_diff.cosh ContDiff.cosh

theorem ContDiffAt.cosh {n} (hf : ContDiffAt ℝ n f x) :
    ContDiffAt ℝ n (fun x => Real.cosh (f x)) x :=
  Real.contDiff_cosh.contDiffAt.comp x hf
#align cont_diff_at.cosh ContDiffAt.cosh

theorem ContDiffOn.cosh {n} (hf : ContDiffOn ℝ n f s) :
    ContDiffOn ℝ n (fun x => Real.cosh (f x)) s :=
  Real.contDiff_cosh.comp_contDiffOn hf
#align cont_diff_on.cosh ContDiffOn.cosh

theorem ContDiffWithinAt.cosh {n} (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun x => Real.cosh (f x)) s x :=
  Real.contDiff_cosh.contDiffAt.comp_contDiffWithinAt x hf
#align cont_diff_within_at.cosh ContDiffWithinAt.cosh

/-! #### `Real.sinh` -/


theorem HasStrictFDerivAt.sinh (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Real.sinh (f x)) (Real.cosh (f x) • f') x :=
  (Real.hasStrictDerivAt_sinh (f x)).comp_hasStrictFDerivAt x hf
#align has_strict_fderiv_at.sinh HasStrictFDerivAt.sinh

theorem HasFDerivAt.sinh (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Real.sinh (f x)) (Real.cosh (f x) • f') x :=
  (Real.hasDerivAt_sinh (f x)).comp_hasFDerivAt x hf
#align has_fderiv_at.sinh HasFDerivAt.sinh

theorem HasFDerivWithinAt.sinh (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Real.sinh (f x)) (Real.cosh (f x) • f') s x :=
  (Real.hasDerivAt_sinh (f x)).comp_hasFDerivWithinAt x hf
#align has_fderiv_within_at.sinh HasFDerivWithinAt.sinh

theorem DifferentiableWithinAt.sinh (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.sinh (f x)) s x :=
  hf.hasFDerivWithinAt.sinh.differentiableWithinAt
#align differentiable_within_at.sinh DifferentiableWithinAt.sinh

@[simp]
theorem DifferentiableAt.sinh (hc : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun x => Real.sinh (f x)) x :=
  hc.hasFDerivAt.sinh.differentiableAt
#align differentiable_at.sinh DifferentiableAt.sinh

theorem DifferentiableOn.sinh (hc : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun x => Real.sinh (f x)) s := fun x h => (hc x h).sinh
#align differentiable_on.sinh DifferentiableOn.sinh

@[simp]
theorem Differentiable.sinh (hc : Differentiable ℝ f) : Differentiable ℝ fun x => Real.sinh (f x) :=
  fun x => (hc x).sinh
#align differentiable.sinh Differentiable.sinh

theorem fderivWithin_sinh (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => Real.sinh (f x)) s x = Real.cosh (f x) • fderivWithin ℝ f s x :=
  hf.hasFDerivWithinAt.sinh.fderivWithin hxs
#align fderiv_within_sinh fderivWithin_sinh

@[simp]
theorem fderiv_sinh (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => Real.sinh (f x)) x = Real.cosh (f x) • fderiv ℝ f x :=
  hc.hasFDerivAt.sinh.fderiv
#align fderiv_sinh fderiv_sinh

theorem ContDiff.sinh {n} (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => Real.sinh (f x) :=
  Real.contDiff_sinh.comp h
#align cont_diff.sinh ContDiff.sinh

theorem ContDiffAt.sinh {n} (hf : ContDiffAt ℝ n f x) :
    ContDiffAt ℝ n (fun x => Real.sinh (f x)) x :=
  Real.contDiff_sinh.contDiffAt.comp x hf
#align cont_diff_at.sinh ContDiffAt.sinh

theorem ContDiffOn.sinh {n} (hf : ContDiffOn ℝ n f s) :
    ContDiffOn ℝ n (fun x => Real.sinh (f x)) s :=
  Real.contDiff_sinh.comp_contDiffOn hf
#align cont_diff_on.sinh ContDiffOn.sinh

theorem ContDiffWithinAt.sinh {n} (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun x => Real.sinh (f x)) s x :=
  Real.contDiff_sinh.contDiffAt.comp_contDiffWithinAt x hf
#align cont_diff_within_at.sinh ContDiffWithinAt.sinh

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
