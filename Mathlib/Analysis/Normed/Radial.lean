/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

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

/-- A function on a space with a norm is *radial* if it factors through the norm. -/
def IsRadial [Norm E] (f : E → F) : Prop := f.FactorsThrough (‖·‖ : E → ℝ)

lemma isRadial_def [Norm E] (f : E → F) :
    f.IsRadial ↔ ∀ {x y : E}, ‖x‖ = ‖y‖ → f x = f y := by
  simp [IsRadial, Function.FactorsThrough]

/-- The radial part of a function. If `f` is radial, then `f = f.radialPart ∘ (‖·‖)`. -/
noncomputable def radialPart [Norm E] [hF : Nonempty F] (f : E → F) : ℝ → F :=
  Function.extend (‖·‖ : E → ℝ) f <| fun _ ↦ Classical.choice hF

namespace IsRadial

lemma eq_radialPart_comp_norm [Norm E] [Nonempty F] {f : E → F} (hf : f.IsRadial) :
    f = f.radialPart ∘ (‖·‖ : E → ℝ) := by
  ext x
  rw [radialPart]
  exact (hf.extend_apply _ _).symm

lemma even [SeminormedAddGroup E] {f : E → F} (hf : f.IsRadial) : f.Even := fun x ↦ hf (norm_neg x)

lemma comp_right [Norm D] {f : D → E} {g : E → F} (hf : f.IsRadial) :
    (g ∘ f).IsRadial := by grind [isRadial_def]

end IsRadial

section Isometries

lemma IsRadial.comp_isometry [SeminormedAddGroup E] {f : E → F} (hf : f.IsRadial) {g : E → E}
    (hg : Isometry g) (hg₀ : g 0 = 0) : f ∘ g = f :=
  funext fun x ↦ hf <| hg.norm_map_of_map_zero hg₀ x

lemma isRadial_iff_comp_linearIsometryEquiv [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → F) : f.IsRadial ↔ ∀ g : E ≃ₗᵢ[ℝ] E, f ∘ g = f := by
  refine ⟨fun hf g ↦ hf.comp_isometry g.isometry (by simp), fun h x y hxy ↦ ?_⟩
  specialize h (ℝ ∙ (x - y))ᗮ.reflection
  rw [← Submodule.reflection_sub hxy, ← f.comp_apply (g := (ℝ ∙ (x - y))ᗮ.reflection), h]

end Isometries

end Function

section Norm

open Function

lemma RCLike.normSq_radial {K : Type*} [RCLike K] : IsRadial (RCLike.normSq (K := K)) := by
  intro _ _ _
  simpa [RCLike.normSq_eq_def']

lemma Complex.normSq_radial : IsRadial (Complex.normSq) := RCLike.normSq_radial

variable [Norm E]

variable (E) in
lemma Norm.isRadial : (‖·‖ : E → ℝ).IsRadial := by grind [isRadial_def]

lemma comp_norm (g : ℝ → F) : (g ∘ (‖·‖ : E → ℝ)).IsRadial := by
  simp [IsRadial.comp_right, Norm.isRadial]

variable (E) in
lemma isRadial_norm_sq : IsRadial (‖·‖ ^ 2 : E → ℝ) := by grind [isRadial_def]

end Norm
