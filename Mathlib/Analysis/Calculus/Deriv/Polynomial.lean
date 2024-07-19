/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Eric Wieser
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add

#align_import analysis.calculus.deriv.polynomial from "leanprover-community/mathlib"@"3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe"

/-!
# Derivatives of polynomials

In this file we prove that derivatives of polynomials in the analysis sense agree with their
derivatives in the algebraic sense.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`analysis/calculus/deriv/basic`.

## TODO

* Add results about multivariable polynomials.
* Generalize some (most?) results to an algebra over the base field.

## Keywords

derivative, polynomial
-/


universe u v w

open scoped Classical Topology Filter ENNReal Polynomial

open Filter Asymptotics Set

open ContinuousLinearMap (smulRight smulRight_one_eq_iff)

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f f₀ f₁ g : 𝕜 → F}
variable {f' f₀' f₁' g' : F}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L L₁ L₂ : Filter 𝕜}

namespace Polynomial

/-! ### Derivative of a polynomial -/


variable {R : Type*} [CommSemiring R] [Algebra R 𝕜]
variable (p : 𝕜[X]) (q : R[X])

/-- The derivative (in the analysis sense) of a polynomial `p` is given by `p.derivative`. -/
protected theorem hasStrictDerivAt (x : 𝕜) :
    HasStrictDerivAt (fun x => p.eval x) (p.derivative.eval x) x := by
  induction p using Polynomial.induction_on' with
  | h_add p q hp hq => simpa using hp.add hq
  | h_monomial n a => simpa [mul_assoc, derivative_monomial]
                        using (hasStrictDerivAt_pow n x).const_mul a
#align polynomial.has_strict_deriv_at Polynomial.hasStrictDerivAt

protected theorem hasStrictDerivAt_aeval (x : 𝕜) :
    HasStrictDerivAt (fun x => aeval x q) (aeval x (derivative q)) x := by
  simpa only [aeval_def, eval₂_eq_eval_map, derivative_map] using
    (q.map (algebraMap R 𝕜)).hasStrictDerivAt x
#align polynomial.has_strict_deriv_at_aeval Polynomial.hasStrictDerivAt_aeval

/-- The derivative (in the analysis sense) of a polynomial `p` is given by `p.derivative`. -/
protected theorem hasDerivAt (x : 𝕜) : HasDerivAt (fun x => p.eval x) (p.derivative.eval x) x :=
  (p.hasStrictDerivAt x).hasDerivAt
#align polynomial.has_deriv_at Polynomial.hasDerivAt

protected theorem hasDerivAt_aeval (x : 𝕜) :
    HasDerivAt (fun x => aeval x q) (aeval x (derivative q)) x :=
  (q.hasStrictDerivAt_aeval x).hasDerivAt
#align polynomial.has_deriv_at_aeval Polynomial.hasDerivAt_aeval

protected theorem hasDerivWithinAt (x : 𝕜) (s : Set 𝕜) :
    HasDerivWithinAt (fun x => p.eval x) (p.derivative.eval x) s x :=
  (p.hasDerivAt x).hasDerivWithinAt
#align polynomial.has_deriv_within_at Polynomial.hasDerivWithinAt

protected theorem hasDerivWithinAt_aeval (x : 𝕜) (s : Set 𝕜) :
    HasDerivWithinAt (fun x => aeval x q) (aeval x (derivative q)) s x :=
  (q.hasDerivAt_aeval x).hasDerivWithinAt
#align polynomial.has_deriv_within_at_aeval Polynomial.hasDerivWithinAt_aeval

protected theorem differentiableAt : DifferentiableAt 𝕜 (fun x => p.eval x) x :=
  (p.hasDerivAt x).differentiableAt
#align polynomial.differentiable_at Polynomial.differentiableAt

protected theorem differentiableAt_aeval : DifferentiableAt 𝕜 (fun x => aeval x q) x :=
  (q.hasDerivAt_aeval x).differentiableAt
#align polynomial.differentiable_at_aeval Polynomial.differentiableAt_aeval

protected theorem differentiableWithinAt : DifferentiableWithinAt 𝕜 (fun x => p.eval x) s x :=
  p.differentiableAt.differentiableWithinAt
#align polynomial.differentiable_within_at Polynomial.differentiableWithinAt

protected theorem differentiableWithinAt_aeval :
    DifferentiableWithinAt 𝕜 (fun x => aeval x q) s x :=
  q.differentiableAt_aeval.differentiableWithinAt
#align polynomial.differentiable_within_at_aeval Polynomial.differentiableWithinAt_aeval

protected theorem differentiable : Differentiable 𝕜 fun x => p.eval x := fun _ => p.differentiableAt
#align polynomial.differentiable Polynomial.differentiable

protected theorem differentiable_aeval : Differentiable 𝕜 fun x : 𝕜 => aeval x q := fun _ =>
  q.differentiableAt_aeval
#align polynomial.differentiable_aeval Polynomial.differentiable_aeval

protected theorem differentiableOn : DifferentiableOn 𝕜 (fun x => p.eval x) s :=
  p.differentiable.differentiableOn
#align polynomial.differentiable_on Polynomial.differentiableOn

protected theorem differentiableOn_aeval : DifferentiableOn 𝕜 (fun x => aeval x q) s :=
  q.differentiable_aeval.differentiableOn
#align polynomial.differentiable_on_aeval Polynomial.differentiableOn_aeval

@[simp]
protected theorem deriv : deriv (fun x => p.eval x) x = p.derivative.eval x :=
  (p.hasDerivAt x).deriv
#align polynomial.deriv Polynomial.deriv

@[simp]
protected theorem deriv_aeval : deriv (fun x => aeval x q) x = aeval x (derivative q) :=
  (q.hasDerivAt_aeval x).deriv
#align polynomial.deriv_aeval Polynomial.deriv_aeval

protected theorem derivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => p.eval x) s x = p.derivative.eval x := by
  rw [DifferentiableAt.derivWithin p.differentiableAt hxs]
  exact p.deriv
#align polynomial.deriv_within Polynomial.derivWithin

protected theorem derivWithin_aeval (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => aeval x q) s x = aeval x (derivative q) := by
  simpa only [aeval_def, eval₂_eq_eval_map, derivative_map] using
    (q.map (algebraMap R 𝕜)).derivWithin hxs
#align polynomial.deriv_within_aeval Polynomial.derivWithin_aeval

protected theorem hasFDerivAt (x : 𝕜) :
    HasFDerivAt (fun x => p.eval x) (smulRight (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x)) x :=
  p.hasDerivAt x
#align polynomial.has_fderiv_at Polynomial.hasFDerivAt

protected theorem hasFDerivAt_aeval (x : 𝕜) :
    HasFDerivAt (fun x => aeval x q) (smulRight (1 : 𝕜 →L[𝕜] 𝕜) (aeval x (derivative q))) x :=
  q.hasDerivAt_aeval x
#align polynomial.has_fderiv_at_aeval Polynomial.hasFDerivAt_aeval

protected theorem hasFDerivWithinAt (x : 𝕜) :
    HasFDerivWithinAt (fun x => p.eval x) (smulRight (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x)) s x :=
  (p.hasFDerivAt x).hasFDerivWithinAt
#align polynomial.has_fderiv_within_at Polynomial.hasFDerivWithinAt

protected theorem hasFDerivWithinAt_aeval (x : 𝕜) :
    HasFDerivWithinAt (fun x => aeval x q) (smulRight (1 : 𝕜 →L[𝕜] 𝕜)
      (aeval x (derivative q))) s x :=
  (q.hasFDerivAt_aeval x).hasFDerivWithinAt
#align polynomial.has_fderiv_within_at_aeval Polynomial.hasFDerivWithinAt_aeval

@[simp]
protected theorem fderiv :
    fderiv 𝕜 (fun x => p.eval x) x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x) :=
  (p.hasFDerivAt x).fderiv
#align polynomial.fderiv Polynomial.fderiv

@[simp]
protected theorem fderiv_aeval :
    fderiv 𝕜 (fun x => aeval x q) x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (aeval x (derivative q)) :=
  (q.hasFDerivAt_aeval x).fderiv
#align polynomial.fderiv_aeval Polynomial.fderiv_aeval

protected theorem fderivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x => p.eval x) s x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x) :=
  (p.hasFDerivWithinAt x).fderivWithin hxs
#align polynomial.fderiv_within Polynomial.fderivWithin

protected theorem fderivWithin_aeval (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x => aeval x q) s x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (aeval x (derivative q)) :=
  (q.hasFDerivWithinAt_aeval x).fderivWithin hxs
#align polynomial.fderiv_within_aeval Polynomial.fderivWithin_aeval

end Polynomial
