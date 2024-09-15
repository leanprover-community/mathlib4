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

open CStarAlgebra in
lemma IsSelfAdjoint.map_spectrum_real {F A B : Type*}
    [NormedRing A] [CompleteSpace A] [StarRing A] [CStarRing A]
    [NormedAlgebra ℂ A] [StarModule ℂ A]
    [NormedRing B] [CompleteSpace B] [StarRing B] [CStarRing B]
    [NormedAlgebra ℂ B] [StarModule ℂ B]
    [FunLike F A B] [AlgHomClass F ℂ A B] [StarHomClass F A B]
    {a : A} (ha : IsSelfAdjoint a) (φ : F) (hφ : Function.Injective φ) :
    spectrum ℝ (φ a) = spectrum ℝ a := by
  have h_spec := AlgHom.spectrum_apply_subset ((φ : A →⋆ₐ[ℂ] B).restrictScalars ℝ) a
  refine Set.eq_of_subset_of_subset h_spec fun x hx ↦ ?_
  /- we prove the reverse inclusion by contradiction, so assume that `x ∈ spectrum ℝ a`, but
  `x ∉ spectrum ℝ (φ a)`. Then by Urysohn's lemma we can get a function for which `f x = 1`, but
  `f = 0` on `spectrum ℝ a`. -/
  by_contra hx'
  obtain ⟨f, h_eqOn, h_eqOn_x, -⟩ := exists_continuous_zero_one_of_isClosed
    (spectrum.isClosed (𝕜 := ℝ) (φ a)) (isClosed_singleton (x := x)) <| by simpa
  /- it suffices to show that `φ (f a) = 0`, for if so, then `f a = 0` by injectivity of `φ`, and
  hence `f = 0` on `spectrum ℝ a`, contradicting the fact that `f x = 1`. -/
  suffices φ (cfc f a) = 0 by
    rw [map_eq_zero_iff φ hφ, ← cfc_zero ℝ a, cfc_eq_cfc_iff_eqOn] at this
    exact zero_ne_one <| calc
      0 = f x := (this hx).symm
      _ = 1 := h_eqOn_x <| Set.mem_singleton x
  /- Finally, `φ (f a) = f (φ a) = 0`, where the last equality follows since `f = 0` on
  `spectrum ℝ (φ a)`. -/
  calc φ (cfc f a) = cfc f (φ a) := StarAlgHomClass.map_cfc φ f a
    _ = cfc (0 : ℝ → ℝ) (φ a) := cfc_congr h_eqOn
    _ = 0 := by simp

namespace NonUnitalStarAlgHom

variable {F A B : Type*}
variable [NonUnitalNormedRing A] [CompleteSpace A] [StarRing A] [CStarRing A]
variable [NormedSpace ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]
variable [NonUnitalNormedRing B] [CompleteSpace B] [StarRing B] [CStarRing B]
variable [NormedSpace ℂ B] [IsScalarTower ℂ B B] [SMulCommClass ℂ B B] [StarModule ℂ B]
variable [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

open CStarAlgebra Unitization in
/-- A non-unital star algebra monomorphism of complex C⋆-algebras is isometric. -/
lemma norm_map (φ : F) (hφ : Function.Injective φ) (a : A) : ‖φ a‖ = ‖a‖ := by
  /- Since passing to the unitization is functorial, and it is an isometric embedding, we may assume
  that `φ` is a unital star algebra monomorphism and that `A` and `B` are unital C⋆-algebras. -/
  suffices ∀ {ψ : Unitization ℂ A →⋆ₐ[ℂ] Unitization ℂ B} (_ : Function.Injective ψ)
      (a : Unitization ℂ A), ‖ψ a‖ = ‖a‖ by
    simpa [norm_inr] using this (starMap_injective (φ := (φ : A →⋆ₙₐ[ℂ] B)) hφ) a
  intro ψ hψ a
  -- to show `‖ψ a‖ = ‖a‖`, by the C⋆-property it suffices to show `‖ψ (star a * a)‖ = ‖star a * a‖`
  rw [← sq_eq_sq (by positivity) (by positivity)]
  simp only [sq, ← CStarRing.norm_star_mul_self, ← map_star, ← map_mul]
  /- since `star a * a` is selfadjoint, it has the same `ℝ`-spectrum as `ψ (star a * a)`.
  Since the spectral radius over `ℝ` coincides with the norm, `‖ψ (star a * a)‖ = ‖star a * a‖`. -/
  have ha : IsSelfAdjoint (star a * a) := .star_mul_self a
  calc ‖ψ (star a * a)‖ = (spectralRadius ℝ (ψ (star a * a))).toReal :=
      ha.map ψ |>.toReal_spectralRadius_eq_norm.symm
    _ = (spectralRadius ℝ (star a * a)).toReal := by
      simp only [spectralRadius, ha.map_spectrum_real ψ hψ]
    _ = ‖star a * a‖ := ha.toReal_spectralRadius_eq_norm

/-- A non-unital star algebra monomorphism of complex C⋆-algebras is isometric. -/
lemma nnnorm_map (φ : F) (hφ : Function.Injective φ) (a : A) : ‖φ a‖₊ = ‖a‖₊ :=
  Subtype.ext <| norm_map φ hφ a

lemma isometry (φ : F) (hφ : Function.Injective φ) : Isometry φ :=
  AddMonoidHomClass.isometry_of_norm φ (norm_map φ hφ)

end NonUnitalStarAlgHom
