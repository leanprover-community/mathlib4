/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

-- public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
-- public import Mathlib.Analysis.Normed.Group.RadialFunction
public import Mathlib

/-!
# Radial functions

A function on a space equipped with a norm is *radial* if its value at a point depends only on the
norm of that point, that is, if it factors through the norm. This file introduces the predicate
`Function.IsRadial` and develops basic API.

## Main definitions

* `Function.IsRadial`: the predicate stating that `f : E → F` factors through `‖·‖ : E → ℝ`.
* `Function.radialPart`: a choice of function `ℝ → F` through which `f : E → F` factors; it
  satisfies `f = f.radialPart ∘ (‖·‖)` precisely when `f` is radial.

## Main statements

* `Function.IsRadial.even`: a radial function on a seminormed additive group is even.
* `Function.IsRadial.comp_isometry`: a radial function is invariant under precomposition with an
  isometry fixing the origin.
* `Function.isRadial_iff_comp_linearIsometryEquiv`: on a real inner product space, a function is
  radial if and only if it is invariant under precomposition with every linear isometry
  equivalence.

## Tags

radial function, radially symmetric, norm
-/

@[expose] public section

variable {D E F : Type*}

namespace Function
section Isometries

lemma isRadial_iff_comp_linearIsometryEquiv [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → F) : f.IsRadial ↔ ∀ g : E ≃ₗᵢ[ℝ] E, f ∘ g = f := by
  refine ⟨fun hf g ↦ hf.comp_isometry g.isometry (by simp), fun h x y hxy ↦ ?_⟩
  specialize h (ℝ ∙ (x - y))ᗮ.reflection
  rw [← Submodule.reflection_sub hxy, ← f.comp_apply (g := (ℝ ∙ (x - y))ᗮ.reflection), h]

#find_home isRadial_iff_comp_linearIsometryEquiv

end Isometries

end Function

section Norm

open Function

lemma RCLike.isRadial_normSq {K : Type*} [RCLike K] : IsRadial (RCLike.normSq (K := K)) := by
  simp [isRadial_def, RCLike.normSq_eq_def']

#find_home RCLike.isRadial_normSq

variable [Norm E]

variable (E) in
lemma Norm.isRadial : (‖·‖ : E → ℝ).IsRadial := by grind [isRadial_def]

lemma Function.IsRadial.comp_norm (g : ℝ → F) : (g ∘ (‖·‖ : E → ℝ)).IsRadial := by
  simp [IsRadial.comp_right, Norm.isRadial]

variable (E) in
lemma Function.isRadial_norm_sq : IsRadial (‖·‖ ^ 2 : E → ℝ) := by grind [isRadial_def]

end Norm

#min_imports
