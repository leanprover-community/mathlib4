/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module analysis.calculus.deriv.star
! leanprover-community/mathlib commit 3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Fderiv.Star

/-!
# Star operations on derivatives

This file contains the usual formulas (and existence assertions) for the derivative of the star
operation. Note that these only apply when the field that the derivative is respect to has a trivial
star operation; which as should be expected rules out `𝕜 = ℂ`.
-/


universe u v w

noncomputable section

open Classical Topology BigOperators Filter ENNReal

open Filter Asymptotics Set

open ContinuousLinearMap (smul_right smulRight_one_eq_iff)

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {f f₀ f₁ g : 𝕜 → F}

variable {f' f₀' f₁' g' : F}

variable {x : 𝕜}

variable {s t : Set 𝕜}

variable {L L₁ L₂ : Filter 𝕜}

section Star

/-! ### Derivative of `x ↦ star x` -/


variable [StarRing 𝕜] [TrivialStar 𝕜] [StarAddMonoid F] [ContinuousStar F]

variable [StarModule 𝕜 F]

protected theorem HasDerivAtFilter.star (h : HasDerivAtFilter f f' x L) :
    HasDerivAtFilter (fun x => star (f x)) (star f') x L := by
  simpa using h.star.has_deriv_at_filter
#align has_deriv_at_filter.star HasDerivAtFilter.star

protected theorem HasDerivWithinAt.star (h : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => star (f x)) (star f') s x :=
  h.unit
#align has_deriv_within_at.star HasDerivWithinAt.star

protected theorem HasDerivAt.star (h : HasDerivAt f f' x) :
    HasDerivAt (fun x => star (f x)) (star f') x :=
  h.unit
#align has_deriv_at.star HasDerivAt.star

protected theorem HasStrictDerivAt.star (h : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => star (f x)) (star f') x := by simpa using h.star.has_strict_deriv_at
#align has_strict_deriv_at.star HasStrictDerivAt.star

protected theorem derivWithin.star (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun y => star (f y)) s x = star (derivWithin f s x) :=
  FunLike.congr_fun (fderivWithin_star hxs) _
#align deriv_within.star derivWithin.star

protected theorem deriv.star : deriv (fun y => star (f y)) x = star (deriv f x) :=
  FunLike.congr_fun fderiv_star _
#align deriv.star deriv.star

@[simp]
protected theorem deriv.star' : (deriv fun y => star (f y)) = fun x => star (deriv f x) :=
  funext fun x => deriv.star
#align deriv.star' deriv.star'

end Star

