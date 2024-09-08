/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! # Properties of C⋆-algebra homomorphisms

Here we collect properties of C⋆-algebra homomorphisms.

## Main declarations

+ `NonUnitalStarAlgHom.norm_map`: A non-unital star algebra monomorphism of complex C⋆-algebras
  is isometric.
-/

namespace NonUnitalStarAlgHom

variable {F A B : Type*}
variable [NonUnitalNormedRing A] [CompleteSpace A] [StarRing A] [CStarRing A]
variable [NormedSpace ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]
variable [NonUnitalNormedRing B] [CompleteSpace B] [StarRing B] [CStarRing B]
variable [NormedSpace ℂ B] [IsScalarTower ℂ B B] [SMulCommClass ℂ B B] [StarModule ℂ B]
variable [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [NonUnitalStarAlgHomClass F ℂ A B]

open CStarAlgebra Unitization in
/-- A non-unital star algebra monomorphism of complex C⋆-algebras is isometric. -/
lemma norm_map (φ : F) (hφ : Function.Injective φ) (a : A) : ‖φ a‖ = ‖a‖ := by
  /- by passing to the unitization is functorial, and it is an isometric embedding, we may assume
  that `φ` is a unital star algebra monomorphism and that `A` and `B` are unital C⋆-algebras. -/
  suffices ∀ {ψ : Unitization ℂ A →⋆ₐ[ℂ] Unitization ℂ B} (_ : Function.Injective ψ)
      (a : Unitization ℂ A), ‖ψ a‖ = ‖a‖ by
    simpa [norm_inr] using this (starLift_injective (φ := (φ : A →⋆ₙₐ[ℂ] B)) hφ) a
  intro ψ hψ a
  -- to show `‖ψ a‖ = ‖a‖`, by the C⋆-property it suffices to show `‖ψ (star a * a‖ = ‖star a * a‖`.
  rw [← sq_eq_sq (by positivity) (by positivity)]
  simp only [sq, ← CStarRing.norm_star_mul_self, ← map_star, ← map_mul]
  /- since `star a * a` is selfadjoint, it suffices to show that it has the same `ℝ`-spectrum as
  `ψ (star a * a)`, since the spectral radius coincides with the norm. -/
  suffices ∀ a, IsSelfAdjoint a → spectrum ℝ (ψ a) = spectrum ℝ a from
    have ha : IsSelfAdjoint (star a * a) := .star_mul_self a
    calc ‖ψ (star a * a)‖ = (spectralRadius ℝ (ψ (star a * a))).toReal :=
        ha.map ψ |>.toReal_spectralRadius_eq_norm.symm
      _ = (spectralRadius ℝ (star a * a)).toReal := by simp only [spectralRadius, this _ ha]
      _ = ‖star a * a‖ := ha.toReal_spectralRadius_eq_norm
  /- so suppose that `a` is selfadjoint. The inclusion `specturm ℝ (ψ a) ⊆ spectrum ℝ a` is
  immediate because `ψ` is a homomorphism. -/
  intro a ha
  have h_spec := AlgHom.spectrum_apply_subset (ψ.restrictScalars ℝ) a
  refine Set.eq_of_subset_of_subset h_spec fun x hx ↦ ?_
  /- we prove the reverse inclusion by contradiction, so assume that `x ∈ spectrum ℝ a`, but
  `x ∉ spectrum ℝ (ψ a)`. Then by Urysohn's lemma we can get a function for which `f x = 1`, but
  `f = 0` on `spectrum ℝ a`. -/
  by_contra hx'
  obtain ⟨f, h_eqOn, h_eqOn_x, -⟩ := exists_continuous_zero_one_of_isClosed
    (spectrum.isClosed (𝕜 := ℝ) (ψ a)) (isClosed_singleton (x := x)) <| by simpa
  /- it suffices to show that `ψ (f a) = 0`, for if so, then `f a = 0` by injectivity of `ψ`, and
  hence `f = 0` on `spectrum ℝ a`, contradicting the fact that `f x = 1`. -/
  suffices ψ (cfc f a) = 0 by
    rw [map_eq_zero_iff ψ hψ, ← cfc_zero ℝ a, cfc_eq_cfc_iff_eqOn] at this
    exact zero_ne_one <| calc
      0 = f x := (this hx).symm
      _ = 1 := h_eqOn_x <| Set.mem_singleton x
  /- Finally, `ψ (f a) = f (ψ a) = 0`, where the last equality follows since `f = 0` on
  `spectrum ℝ (ψ a)`. -/
  calc ψ (cfc f a) = cfc f (ψ a) := ψ.map_cfc f a
    _ = cfc (0 : ℝ → ℝ) (ψ a) := cfc_congr h_eqOn
    _ = 0 := by simp

/-- A non-unital star algebra monomorphism of complex C⋆-algebras is isometric. -/
lemma nnnorm_map (φ : F) (hφ : Function.Injective φ) (a : A) : ‖φ a‖₊ = ‖a‖₊ :=
  Subtype.ext <| norm_map φ hφ a

lemma isometry (φ : F) (hφ : Function.Injective φ) : Isometry φ :=
  AddMonoidHomClass.isometry_of_norm φ (norm_map φ hφ)

end NonUnitalStarAlgHom
