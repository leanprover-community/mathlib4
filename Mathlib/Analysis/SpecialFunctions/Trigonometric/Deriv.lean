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
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
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
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Metrizable.Uniformity

/-!
# Differentiability of trigonometric functions

## Main statements

The differentiability of the usual trigonometric functions is proved, and their derivatives are
computed.

## Tags

sin, cos, tan, angle
-/

public section

noncomputable section

open scoped Asymptotics Topology Filter
open Set

namespace Complex

/-- The complex sine function is everywhere strictly differentiable, with the derivative `cos x`. -/
theorem hasStrictDerivAt_sin (x : ℂ) : HasStrictDerivAt sin (cos x) x := by
  simp only [cos, div_eq_mul_inv]
  convert ((((hasStrictDerivAt_id x).fun_neg.mul_const I).cexp.sub
    ((hasStrictDerivAt_id x).mul_const I).cexp).mul_const I).mul_const (2 : ℂ)⁻¹ using 1
  simp only [id]
  rw [sub_mul, mul_assoc, mul_assoc, I_mul_I, neg_one_mul, neg_neg, mul_one, one_mul, mul_assoc,
    I_mul_I, mul_neg_one, sub_neg_eq_add, add_comm]

/-- The complex sine function is everywhere differentiable, with the derivative `cos x`. -/
theorem hasDerivAt_sin (x : ℂ) : HasDerivAt sin (cos x) x :=
  (hasStrictDerivAt_sin x).hasDerivAt

theorem isEquivalent_sin : sin ~[𝓝 0] id := by simpa using (hasDerivAt_sin 0).isLittleO

@[fun_prop]
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
    ((hasStrictDerivAt_id x).fun_neg.mul_const I).cexp).mul_const (2 : ℂ)⁻¹ using 1
  simp only [id]
  ring

/-- The complex cosine function is everywhere differentiable, with the derivative `-sin x`. -/
theorem hasDerivAt_cos (x : ℂ) : HasDerivAt cos (-sin x) x :=
  (hasStrictDerivAt_cos x).hasDerivAt

@[fun_prop]
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

end

section

/-! ### Simp lemmas for derivatives of `fun x => Complex.cos (f x)` etc., `f : E → ℂ` -/


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ} {f' : StrongDual ℂ E}
  {x : E} {s : Set E}

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

end

namespace Real

variable {x y z : ℝ}

theorem hasStrictDerivAt_sin (x : ℝ) : HasStrictDerivAt sin (cos x) x :=
  (Complex.hasStrictDerivAt_sin x).real_of_complex

theorem hasDerivAt_sin (x : ℝ) : HasDerivAt sin (cos x) x :=
  (hasStrictDerivAt_sin x).hasDerivAt

theorem isEquivalent_sin : sin ~[𝓝 0] id := by simpa using (hasDerivAt_sin 0).isLittleO

@[fun_prop]
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

@[fun_prop]
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

end Real

section iteratedDeriv

/-! ### Simp lemmas for iterated derivatives of `sin` and `cos`. -/

namespace Complex

@[simp]
theorem iteratedDeriv_add_one_sin (n : ℕ) :
    iteratedDeriv (n + 1) sin = iteratedDeriv n cos := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]

@[simp]
theorem iteratedDeriv_add_one_cos (n : ℕ) :
    iteratedDeriv (n + 1) cos = - iteratedDeriv n sin := by
  induction n with
  | zero => ext; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ, deriv.neg']
    ext x
    simp

@[simp]
theorem iteratedDeriv_even_sin (n : ℕ) :
    iteratedDeriv (2 * n) sin = (-1) ^ n * sin := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add, pow_succ]

@[simp]
theorem iteratedDeriv_even_cos (n : ℕ) :
    iteratedDeriv (2 * n) cos = (-1) ^ n * cos := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add, pow_succ]

theorem iteratedDeriv_odd_sin (n : ℕ) :
    iteratedDeriv (2 * n + 1) sin = (-1) ^ n * cos := by simp

theorem iteratedDeriv_odd_cos (n : ℕ) :
    iteratedDeriv (2 * n + 1) cos = (-1) ^ (n + 1) * sin := by simp [pow_succ]

theorem differentiable_iteratedDeriv_sin (n : ℕ) :
    Differentiable ℂ (iteratedDeriv n sin) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_sin]

theorem differentiable_iteratedDeriv_cos (n : ℕ) :
    Differentiable ℂ (iteratedDeriv n cos) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_cos]

end Complex

namespace Real

@[simp]
theorem iteratedDeriv_add_one_sin (n : ℕ) :
    iteratedDeriv (n + 1) sin = iteratedDeriv n cos := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]

@[simp]
theorem iteratedDeriv_add_one_cos (n : ℕ) :
    iteratedDeriv (n + 1) cos = - iteratedDeriv n sin := by
  induction n with
  | zero => ext; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ, deriv.neg']
    ext x
    simp

@[simp]
theorem iteratedDeriv_even_sin (n : ℕ) :
    iteratedDeriv (2 * n) sin = (-1) ^ n * sin := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add, pow_succ]

@[simp]
theorem iteratedDeriv_even_cos (n : ℕ) :
    iteratedDeriv (2 * n) cos = (-1) ^ n * cos := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add, pow_succ]

theorem iteratedDeriv_odd_sin (n : ℕ) :
    iteratedDeriv (2 * n + 1) sin = (-1) ^ n * cos := by simp

theorem iteratedDeriv_odd_cos (n : ℕ) :
    iteratedDeriv (2 * n + 1) cos = (-1) ^ (n + 1) * sin := by simp [pow_succ]

theorem differentiable_iteratedDeriv_sin (n : ℕ) :
    Differentiable ℝ (iteratedDeriv n sin) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_sin]

theorem differentiable_iteratedDeriv_cos (n : ℕ) :
    Differentiable ℝ (iteratedDeriv n cos) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_cos]

theorem abs_iteratedDeriv_sin_le_one (n : ℕ) (x : ℝ) :
    |iteratedDeriv n sin x| ≤ 1 :=
  match n with
  | 0 => by simpa using Real.abs_sin_le_one x
  | 1 => by simpa using Real.abs_cos_le_one x
  | n + 2 => by simpa using abs_iteratedDeriv_sin_le_one n x

theorem abs_iteratedDeriv_cos_le_one (n : ℕ) (x : ℝ) :
    |iteratedDeriv n cos x| ≤ 1 :=
  match n with
  | 0 => by simpa using Real.abs_cos_le_one x
  | 1 => by simpa using Real.abs_sin_le_one x
  | n + 2 => by simpa using abs_iteratedDeriv_cos_le_one n x

@[simp]
theorem iteratedDerivWithin_sin_Icc (n : ℕ) {a b : ℝ} (h : a < b) {x : ℝ} (hx : x ∈ Icc a b) :
    iteratedDerivWithin n sin (Icc a b) x = iteratedDeriv n sin x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h) contDiff_sin.contDiffAt hx

@[simp]
theorem iteratedDerivWithin_cos_Icc (n : ℕ) {a b : ℝ} (h : a < b) {x : ℝ} (hx : x ∈ Icc a b) :
    iteratedDerivWithin n cos (Icc a b) x = iteratedDeriv n cos x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h) contDiff_cos.contDiffAt hx

@[simp]
theorem iteratedDerivWithin_sin_Ioo (n : ℕ) {a b x : ℝ} (hx : x ∈ Ioo a b) :
    iteratedDerivWithin n sin (Ioo a b) x = iteratedDeriv n sin x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo a b) contDiff_sin.contDiffAt hx

@[simp]
theorem iteratedDerivWithin_cos_Ioo (n : ℕ) {a b x : ℝ} (hx : x ∈ Ioo a b) :
    iteratedDerivWithin n cos (Ioo a b) x = iteratedDeriv n cos x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo a b) contDiff_cos.contDiffAt hx

end Real

end iteratedDeriv

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

end

section

/-! ### Simp lemmas for derivatives of `fun x => Real.cos (f x)` etc., `f : E → ℝ` -/


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {f' : StrongDual ℝ E}
  {x : E} {s : Set E}

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
  rw [logDeriv, Real.deriv_cos', Pi.div_apply, Pi.neg_apply, neg_div, Real.tan_eq_sin_div_cos]

@[simp]
theorem Complex.logDeriv_exp : logDeriv (Complex.exp) = 1 := by
  ext
  rw [logDeriv, Complex.deriv_exp, Pi.div_apply, ← exp_sub, sub_self, exp_zero, Pi.one_apply]

@[deprecated (since := "2026-02-05")] alias Complex.LogDeriv_exp := Complex.logDeriv_exp

@[simp]
theorem Real.logDeriv_exp : logDeriv (Real.exp) = 1 := by
  ext
  rw [logDeriv, Real.deriv_exp, Pi.div_apply, ← exp_sub, sub_self, exp_zero, Pi.one_apply]

@[deprecated (since := "2026-02-05")] alias Real.LogDeriv_exp := Real.logDeriv_exp

end LogDeriv

end
