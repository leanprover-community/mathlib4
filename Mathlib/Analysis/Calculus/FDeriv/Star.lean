/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Topology.Algebra.Module.Star

#align_import analysis.calculus.fderiv.star from "leanprover-community/mathlib"@"ad84a13c884fd19e286fb7abb36f4b9ba7e2f615"

/-!
# Star operations on derivatives

For detailed documentation of the Fréchet derivative,
see the module docstring of `Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of the star
operation. Note that these only apply when the field that the derivative is respect to has a trivial
star operation; which as should be expected rules out `𝕜 = ℂ`.
-/


open scoped Classical

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [StarRing 𝕜] [TrivialStar 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [StarAddMonoid F] [NormedSpace 𝕜 F] [StarModule 𝕜 F]
  [ContinuousStar F]

variable {f : E → F} {f' : E →L[𝕜] F} (e : E →L[𝕜] F) {x : E} {s : Set E} {L : Filter E}

@[fun_prop]
theorem HasStrictFDerivAt.star (h : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => star (f x)) (((starL' 𝕜 : F ≃L[𝕜] F) : F →L[𝕜] F) ∘L f') x :=
  (starL' 𝕜 : F ≃L[𝕜] F).toContinuousLinearMap.hasStrictFDerivAt.comp x h
#align has_strict_fderiv_at.star HasStrictFDerivAt.star

theorem HasFDerivAtFilter.star (h : HasFDerivAtFilter f f' x L) :
    HasFDerivAtFilter (fun x => star (f x)) (((starL' 𝕜 : F ≃L[𝕜] F) : F →L[𝕜] F) ∘L f') x L :=
  (starL' 𝕜 : F ≃L[𝕜] F).toContinuousLinearMap.hasFDerivAtFilter.comp x h Filter.tendsto_map
#align has_fderiv_at_filter.star HasFDerivAtFilter.star

@[fun_prop]
nonrec theorem HasFDerivWithinAt.star (h : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => star (f x)) (((starL' 𝕜 : F ≃L[𝕜] F) : F →L[𝕜] F) ∘L f') s x :=
  h.star
#align has_fderiv_within_at.star HasFDerivWithinAt.star

@[fun_prop]
nonrec theorem HasFDerivAt.star (h : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => star (f x)) (((starL' 𝕜 : F ≃L[𝕜] F) : F →L[𝕜] F) ∘L f') x :=
  h.star
#align has_fderiv_at.star HasFDerivAt.star

@[fun_prop]
theorem DifferentiableWithinAt.star (h : DifferentiableWithinAt 𝕜 f s x) :
    DifferentiableWithinAt 𝕜 (fun y => star (f y)) s x :=
  h.hasFDerivWithinAt.star.differentiableWithinAt
#align differentiable_within_at.star DifferentiableWithinAt.star

@[simp]
theorem differentiableWithinAt_star_iff :
    DifferentiableWithinAt 𝕜 (fun y => star (f y)) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  (starL' 𝕜 : F ≃L[𝕜] F).comp_differentiableWithinAt_iff
#align differentiable_within_at_star_iff differentiableWithinAt_star_iff

@[fun_prop]
theorem DifferentiableAt.star (h : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (fun y => star (f y)) x :=
  h.hasFDerivAt.star.differentiableAt
#align differentiable_at.star DifferentiableAt.star

@[simp]
theorem differentiableAt_star_iff :
    DifferentiableAt 𝕜 (fun y => star (f y)) x ↔ DifferentiableAt 𝕜 f x :=
  (starL' 𝕜 : F ≃L[𝕜] F).comp_differentiableAt_iff
#align differentiable_at_star_iff differentiableAt_star_iff

@[fun_prop]
theorem DifferentiableOn.star (h : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (fun y => star (f y)) s := fun x hx => (h x hx).star
#align differentiable_on.star DifferentiableOn.star

@[simp]
theorem differentiableOn_star_iff :
    DifferentiableOn 𝕜 (fun y => star (f y)) s ↔ DifferentiableOn 𝕜 f s :=
  (starL' 𝕜 : F ≃L[𝕜] F).comp_differentiableOn_iff
#align differentiable_on_star_iff differentiableOn_star_iff

@[fun_prop]
theorem Differentiable.star (h : Differentiable 𝕜 f) : Differentiable 𝕜 fun y => star (f y) :=
  fun x => (h x).star
#align differentiable.star Differentiable.star

@[simp]
theorem differentiable_star_iff : (Differentiable 𝕜 fun y => star (f y)) ↔ Differentiable 𝕜 f :=
  (starL' 𝕜 : F ≃L[𝕜] F).comp_differentiable_iff
#align differentiable_star_iff differentiable_star_iff

theorem fderivWithin_star (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun y => star (f y)) s x =
      ((starL' 𝕜 : F ≃L[𝕜] F) : F →L[𝕜] F) ∘L fderivWithin 𝕜 f s x :=
  (starL' 𝕜 : F ≃L[𝕜] F).comp_fderivWithin hxs
#align fderiv_within_star fderivWithin_star

@[simp]
theorem fderiv_star :
    fderiv 𝕜 (fun y => star (f y)) x = ((starL' 𝕜 : F ≃L[𝕜] F) : F →L[𝕜] F) ∘L fderiv 𝕜 f x :=
  (starL' 𝕜 : F ≃L[𝕜] F).comp_fderiv
#align fderiv_star fderiv_star
