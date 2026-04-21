/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Eric Wieser
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Derivatives of polynomials

In this file we prove that derivatives of polynomials in the analysis sense agree with their
derivatives in the algebraic sense.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Mathlib/Analysis/Calculus/Deriv/Basic.lean`.

## TODO

* Add results about multivariable polynomials.
* Generalize some (most?) results to an algebra over the base field.

## Keywords

derivative, polynomial
-/
set_option backward.defeqAttrib.useBackward true

public section


universe u

open scoped Polynomial

open ContinuousLinearMap (smulRight)

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {x : 𝕜} {s : Set 𝕜}

namespace Polynomial

/-! ### Derivative of a polynomial -/


variable {R : Type*} [CommSemiring R] [Algebra R 𝕜]
variable (p : 𝕜[X]) (q : R[X])

/-- The derivative (in the analysis sense) of a polynomial `p` is given by `p.derivative`. -/
protected theorem hasStrictDerivAt (x : 𝕜) :
    HasStrictDerivAt (fun x => p.eval x) (p.derivative.eval x) x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using hp.add hq
  | monomial n a => simpa [mul_assoc, derivative_monomial]
                      using (hasStrictDerivAt_pow n x).const_mul a

protected theorem hasStrictDerivAt_aeval (x : 𝕜) :
    HasStrictDerivAt (fun x => aeval x q) (aeval x (derivative q)) x := by
  simpa only [aeval_def, eval₂_eq_eval_map, derivative_map] using
    (q.map (algebraMap R 𝕜)).hasStrictDerivAt x

/-- The derivative (in the analysis sense) of a polynomial `p` is given by `p.derivative`. -/
protected theorem hasDerivAt (x : 𝕜) : HasDerivAt (fun x => p.eval x) (p.derivative.eval x) x :=
  (p.hasStrictDerivAt x).hasDerivAt

protected theorem hasDerivAt_aeval (x : 𝕜) :
    HasDerivAt (fun x => aeval x q) (aeval x (derivative q)) x :=
  (q.hasStrictDerivAt_aeval x).hasDerivAt

protected theorem hasDerivWithinAt (x : 𝕜) (s : Set 𝕜) :
    HasDerivWithinAt (fun x => p.eval x) (p.derivative.eval x) s x :=
  (p.hasDerivAt x).hasDerivWithinAt

protected theorem hasDerivWithinAt_aeval (x : 𝕜) (s : Set 𝕜) :
    HasDerivWithinAt (fun x => aeval x q) (aeval x (derivative q)) s x :=
  (q.hasDerivAt_aeval x).hasDerivWithinAt

protected theorem differentiableAt : DifferentiableAt 𝕜 (fun x => p.eval x) x :=
  (p.hasDerivAt x).differentiableAt

protected theorem differentiableAt_aeval : DifferentiableAt 𝕜 (fun x => aeval x q) x :=
  (q.hasDerivAt_aeval x).differentiableAt

protected theorem differentiableWithinAt : DifferentiableWithinAt 𝕜 (fun x => p.eval x) s x :=
  p.differentiableAt.differentiableWithinAt

protected theorem differentiableWithinAt_aeval :
    DifferentiableWithinAt 𝕜 (fun x => aeval x q) s x :=
  q.differentiableAt_aeval.differentiableWithinAt

@[fun_prop]
protected theorem differentiable : Differentiable 𝕜 fun x => p.eval x := fun _ => p.differentiableAt

protected theorem differentiable_aeval : Differentiable 𝕜 fun x : 𝕜 => aeval x q := fun _ =>
  q.differentiableAt_aeval

protected theorem differentiableOn : DifferentiableOn 𝕜 (fun x => p.eval x) s :=
  p.differentiable.differentiableOn

protected theorem differentiableOn_aeval : DifferentiableOn 𝕜 (fun x => aeval x q) s :=
  q.differentiable_aeval.differentiableOn

@[simp]
protected theorem deriv : deriv (fun x => p.eval x) x = p.derivative.eval x :=
  (p.hasDerivAt x).deriv

@[simp]
protected theorem deriv_aeval : deriv (fun x => aeval x q) x = aeval x (derivative q) :=
  (q.hasDerivAt_aeval x).deriv

protected theorem derivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => p.eval x) s x = p.derivative.eval x := by
  rw [DifferentiableAt.derivWithin p.differentiableAt hxs]
  exact p.deriv

protected theorem derivWithin_aeval (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => aeval x q) s x = aeval x (derivative q) := by
  simpa only [aeval_def, eval₂_eq_eval_map, derivative_map] using
    (q.map (algebraMap R 𝕜)).derivWithin hxs

protected theorem hasFDerivAt (x : 𝕜) :
    HasFDerivAt (fun x => p.eval x) (smulRight (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x)) x :=
  p.hasDerivAt x

protected theorem hasFDerivAt_aeval (x : 𝕜) :
    HasFDerivAt (fun x => aeval x q) (smulRight (1 : 𝕜 →L[𝕜] 𝕜) (aeval x (derivative q))) x :=
  q.hasDerivAt_aeval x

protected theorem hasFDerivWithinAt (x : 𝕜) :
    HasFDerivWithinAt (fun x => p.eval x) (smulRight (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x)) s x :=
  (p.hasFDerivAt x).hasFDerivWithinAt

protected theorem hasFDerivWithinAt_aeval (x : 𝕜) :
    HasFDerivWithinAt (fun x => aeval x q) (smulRight (1 : 𝕜 →L[𝕜] 𝕜)
      (aeval x (derivative q))) s x :=
  (q.hasFDerivAt_aeval x).hasFDerivWithinAt

@[simp]
protected theorem fderiv :
    fderiv 𝕜 (fun x => p.eval x) x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x) :=
  (p.hasFDerivAt x).fderiv

@[simp]
protected theorem fderiv_aeval :
    fderiv 𝕜 (fun x => aeval x q) x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (aeval x (derivative q)) :=
  (q.hasFDerivAt_aeval x).fderiv

protected theorem fderivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x => p.eval x) s x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x) :=
  (p.hasFDerivWithinAt x).fderivWithin hxs

protected theorem fderivWithin_aeval (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x => aeval x q) s x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (aeval x (derivative q)) :=
  (q.hasFDerivWithinAt_aeval x).fderivWithin hxs

end Polynomial
