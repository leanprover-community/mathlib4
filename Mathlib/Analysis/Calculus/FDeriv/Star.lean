/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Topology.Algebra.Module.Star

/-!
# Star operations on derivatives

This file contains the usual formulas (and existence assertions) for the Fréchet derivative of the
star operation. For detailed documentation of the Fréchet derivative, see the module docstring of
`Analysis/Calculus/FDeriv/Basic.lean`.

Most of the results in this file only apply when the field that the derivative is respect to has a
trivial star operation; which as should be expected rules out `𝕜 = ℂ`. The exceptions are
`HasFDerivAt.star_star` and `DifferentiableAt.star_star`, showing that `star ∘ f ∘ star` is
differentiable when `f` is (and giving a formula for its derivative).
-/


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [StarRing 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [StarAddMonoid F] [NormedSpace 𝕜 F] [StarModule 𝕜 F]
  [ContinuousStar F]

variable {f : E → F} {f' : E →L[𝕜] F} {x : E} {s : Set E} {L : Filter E}

section TrivialStar

variable [TrivialStar 𝕜]

@[fun_prop]
protected theorem HasStrictFDerivAt.star (h : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => star (f x)) (((starL' 𝕜 : F ≃L[𝕜] F) : F →L[𝕜] F) ∘L f') x :=
  (starL' 𝕜 : F ≃L[𝕜] F).toContinuousLinearMap.hasStrictFDerivAt.comp x h

protected theorem HasFDerivAtFilter.star (h : HasFDerivAtFilter f f' x L) :
    HasFDerivAtFilter (fun x => star (f x)) (((starL' 𝕜 : F ≃L[𝕜] F) : F →L[𝕜] F) ∘L f') x L :=
  (starL' 𝕜 : F ≃L[𝕜] F).toContinuousLinearMap.hasFDerivAtFilter.comp x h Filter.tendsto_map

@[fun_prop]
protected nonrec theorem HasFDerivWithinAt.star (h : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => star (f x)) (((starL' 𝕜 : F ≃L[𝕜] F) : F →L[𝕜] F) ∘L f') s x :=
  h.star

@[fun_prop]
protected nonrec theorem HasFDerivAt.star (h : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => star (f x)) (((starL' 𝕜 : F ≃L[𝕜] F) : F →L[𝕜] F) ∘L f') x :=
  h.star

@[fun_prop]
protected theorem DifferentiableWithinAt.star (h : DifferentiableWithinAt 𝕜 f s x) :
    DifferentiableWithinAt 𝕜 (fun y => star (f y)) s x :=
  h.hasFDerivWithinAt.star.differentiableWithinAt

@[simp]
theorem differentiableWithinAt_star_iff :
    DifferentiableWithinAt 𝕜 (fun y => star (f y)) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  (starL' 𝕜 : F ≃L[𝕜] F).comp_differentiableWithinAt_iff

@[fun_prop]
protected theorem DifferentiableAt.star (h : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (fun y => star (f y)) x :=
  h.hasFDerivAt.star.differentiableAt

@[simp]
theorem differentiableAt_star_iff :
    DifferentiableAt 𝕜 (fun y => star (f y)) x ↔ DifferentiableAt 𝕜 f x :=
  (starL' 𝕜 : F ≃L[𝕜] F).comp_differentiableAt_iff

@[fun_prop]
protected theorem DifferentiableOn.star (h : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (fun y => star (f y)) s := fun x hx => (h x hx).star

@[simp]
theorem differentiableOn_star_iff :
    DifferentiableOn 𝕜 (fun y => star (f y)) s ↔ DifferentiableOn 𝕜 f s :=
  (starL' 𝕜 : F ≃L[𝕜] F).comp_differentiableOn_iff

@[fun_prop]
protected theorem Differentiable.star (h : Differentiable 𝕜 f) :
    Differentiable 𝕜 fun y => star (f y) :=
  fun x => (h x).star

@[simp]
theorem differentiable_star_iff : (Differentiable 𝕜 fun y => star (f y)) ↔ Differentiable 𝕜 f :=
  (starL' 𝕜 : F ≃L[𝕜] F).comp_differentiable_iff

theorem fderivWithin_star (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun y => star (f y)) s x =
      ((starL' 𝕜 : F ≃L[𝕜] F) : F →L[𝕜] F) ∘L fderivWithin 𝕜 f s x :=
  (starL' 𝕜 : F ≃L[𝕜] F).comp_fderivWithin hxs

@[simp]
theorem fderiv_star :
    fderiv 𝕜 (fun y => star (f y)) x = ((starL' 𝕜 : F ≃L[𝕜] F) : F →L[𝕜] F) ∘L fderiv 𝕜 f x :=
  (starL' 𝕜 : F ≃L[𝕜] F).comp_fderiv

end TrivialStar

section NontrivialStar

/-!
## Composing on the left and right with `star`
-/

variable [StarAddMonoid E] [StarModule 𝕜 E] [ContinuousStar E] [NormedStarGroup 𝕜]

/-- If `f` has derivative `f'` at `z`, then `star ∘ f ∘ star` has derivative `starL ∘ f' ∘ starL`
at `star z`. -/
@[fun_prop]
lemma HasFDerivAt.star_star {f : E → F} {z : E} {f' : E →L[𝕜] F} (hf : HasFDerivAt f f' z) :
    HasFDerivAt (star ∘ f ∘ star)
      ((starL 𝕜).toContinuousLinearMap.comp <| f'.comp (starL 𝕜).toContinuousLinearMap) (star z) :=
  .comp_semilinear (starL 𝕜).toContinuousLinearMap (starL 𝕜).toContinuousLinearMap
    (by simpa using hf)

/-- If `f` is differentiable at `z`, then `star ∘ f ∘ star` is differentiable at `star z`. -/
@[fun_prop]
lemma DifferentiableAt.star_star {f : E → F} {z : E} (hf : DifferentiableAt 𝕜 f z) :
    DifferentiableAt 𝕜 (star ∘ f ∘ star) (star z) :=
  hf.hasFDerivAt.star_star.differentiableAt

end NontrivialStar
