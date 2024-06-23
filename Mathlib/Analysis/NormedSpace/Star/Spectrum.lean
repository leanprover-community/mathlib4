/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.NormedSpace.Star.Basic
import Mathlib.Analysis.NormedSpace.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Algebra.Star.StarAlgHom

#align_import analysis.normed_space.star.spectrum from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-! # Spectral properties in C⋆-algebras
In this file, we establish various properties related to the spectrum of elements in C⋆-algebras.
-/


local postfix:max "⋆" => star

section

open scoped Topology ENNReal

open Filter ENNReal spectrum CstarRing NormedSpace

section UnitarySpectrum

variable {𝕜 : Type*} [NormedField 𝕜] {E : Type*} [NormedRing E] [StarRing E] [CstarRing E]
  [NormedAlgebra 𝕜 E] [CompleteSpace E]

theorem unitary.spectrum_subset_circle (u : unitary E) :
    spectrum 𝕜 (u : E) ⊆ Metric.sphere 0 1 := by
  nontriviality E
  refine fun k hk => mem_sphere_zero_iff_norm.mpr (le_antisymm ?_ ?_)
  · simpa only [CstarRing.norm_coe_unitary u] using norm_le_norm_of_mem hk
  · rw [← unitary.val_toUnits_apply u] at hk
    have hnk := ne_zero_of_mem_of_unit hk
    rw [← inv_inv (unitary.toUnits u), ← spectrum.map_inv, Set.mem_inv] at hk
    have : ‖k‖⁻¹ ≤ ‖(↑(unitary.toUnits u)⁻¹ : E)‖ := by
      simpa only [norm_inv] using norm_le_norm_of_mem hk
    simpa using inv_le_of_inv_le (norm_pos_iff.mpr hnk) this
#align unitary.spectrum_subset_circle unitary.spectrum_subset_circle

theorem spectrum.subset_circle_of_unitary {u : E} (h : u ∈ unitary E) :
    spectrum 𝕜 u ⊆ Metric.sphere 0 1 :=
  unitary.spectrum_subset_circle ⟨u, h⟩
#align spectrum.subset_circle_of_unitary spectrum.subset_circle_of_unitary

end UnitarySpectrum

section ComplexScalars

open Complex

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [StarRing A]
  [CstarRing A]

local notation "↑ₐ" => algebraMap ℂ A

theorem IsSelfAdjoint.spectralRadius_eq_nnnorm {a : A} (ha : IsSelfAdjoint a) :
    spectralRadius ℂ a = ‖a‖₊ := by
  have hconst : Tendsto (fun _n : ℕ => (‖a‖₊ : ℝ≥0∞)) atTop _ := tendsto_const_nhds
  refine tendsto_nhds_unique ?_ hconst
  convert
    (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (a : A)).comp
      (Nat.tendsto_pow_atTop_atTop_of_one_lt one_lt_two) using 1
  refine funext fun n => ?_
  rw [Function.comp_apply, ha.nnnorm_pow_two_pow, ENNReal.coe_pow, ← rpow_natCast, ← rpow_mul]
  simp
#align is_self_adjoint.spectral_radius_eq_nnnorm IsSelfAdjoint.spectralRadius_eq_nnnorm

theorem IsStarNormal.spectralRadius_eq_nnnorm (a : A) [IsStarNormal a] :
    spectralRadius ℂ a = ‖a‖₊ := by
  refine (ENNReal.pow_strictMono two_ne_zero).injective ?_
  have heq :
    (fun n : ℕ => (‖(a⋆ * a) ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ)) =
      (fun x => x ^ 2) ∘ fun n : ℕ => (‖a ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ) := by
    funext n
    rw [Function.comp_apply, ← rpow_natCast, ← rpow_mul, mul_comm, rpow_mul, rpow_natCast, ←
      coe_pow, sq, ← nnnorm_star_mul_self, Commute.mul_pow (star_comm_self' a), star_pow]
  have h₂ :=
    ((ENNReal.continuous_pow 2).tendsto (spectralRadius ℂ a)).comp
      (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a)
  rw [← heq] at h₂
  convert tendsto_nhds_unique h₂ (pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (a⋆ * a))
  rw [(IsSelfAdjoint.star_mul_self a).spectralRadius_eq_nnnorm, sq, nnnorm_star_mul_self, coe_mul]
#align is_star_normal.spectral_radius_eq_nnnorm IsStarNormal.spectralRadius_eq_nnnorm

/-- Any element of the spectrum of a selfadjoint is real. -/
theorem IsSelfAdjoint.mem_spectrum_eq_re [StarModule ℂ A] {a : A} (ha : IsSelfAdjoint a) {z : ℂ}
    (hz : z ∈ spectrum ℂ a) : z = z.re := by
  have hu := exp_mem_unitary_of_mem_skewAdjoint ℂ (ha.smul_mem_skewAdjoint conj_I)
  let Iu := Units.mk0 I I_ne_zero
  have : NormedSpace.exp ℂ (I • z) ∈ spectrum ℂ (NormedSpace.exp ℂ (I • a)) := by
    simpa only [Units.smul_def, Units.val_mk0] using
      spectrum.exp_mem_exp (Iu • a) (smul_mem_smul_iff.mpr hz)
  exact Complex.ext (ofReal_re _) <| by
    simpa only [← Complex.exp_eq_exp_ℂ, mem_sphere_zero_iff_norm, norm_eq_abs, abs_exp,
      Real.exp_eq_one_iff, smul_eq_mul, I_mul, neg_eq_zero] using
      spectrum.subset_circle_of_unitary hu this
#align is_self_adjoint.mem_spectrum_eq_re IsSelfAdjoint.mem_spectrum_eq_re

/-- Any element of the spectrum of a selfadjoint is real. -/
theorem selfAdjoint.mem_spectrum_eq_re [StarModule ℂ A] (a : selfAdjoint A) {z : ℂ}
    (hz : z ∈ spectrum ℂ (a : A)) : z = z.re :=
  a.prop.mem_spectrum_eq_re hz
#align self_adjoint.mem_spectrum_eq_re selfAdjoint.mem_spectrum_eq_re

/-- The spectrum of a selfadjoint is real -/
theorem IsSelfAdjoint.val_re_map_spectrum [StarModule ℂ A] {a : A} (ha : IsSelfAdjoint a) :
    spectrum ℂ a = ((↑) ∘ re '' spectrum ℂ a : Set ℂ) :=
  le_antisymm (fun z hz => ⟨z, hz, (ha.mem_spectrum_eq_re hz).symm⟩) fun z => by
    rintro ⟨z, hz, rfl⟩
    simpa only [(ha.mem_spectrum_eq_re hz).symm, Function.comp_apply] using hz
#align is_self_adjoint.coe_re_map_spectrum IsSelfAdjoint.val_re_map_spectrum

/-- The spectrum of a selfadjoint is real -/
theorem selfAdjoint.val_re_map_spectrum [StarModule ℂ A] (a : selfAdjoint A) :
    spectrum ℂ (a : A) = ((↑) ∘ re '' spectrum ℂ (a : A) : Set ℂ) :=
  a.property.val_re_map_spectrum
#align self_adjoint.coe_re_map_spectrum selfAdjoint.val_re_map_spectrum

end ComplexScalars

namespace StarAlgHom

variable {F A B : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [StarRing A]
  [CstarRing A] [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B] [StarRing B] [CstarRing B]
  [FunLike F A B] [AlgHomClass F ℂ A B] [StarAlgHomClass F ℂ A B] (φ : F)

/-- A star algebra homomorphism of complex C⋆-algebras is norm contractive. -/
theorem nnnorm_apply_le (a : A) : ‖(φ a : B)‖₊ ≤ ‖a‖₊ := by
  suffices ∀ s : A, IsSelfAdjoint s → ‖φ s‖₊ ≤ ‖s‖₊ by
    exact nonneg_le_nonneg_of_sq_le_sq zero_le' <| by
      simpa only [nnnorm_star_mul_self, map_star, map_mul]
      using this _ (IsSelfAdjoint.star_mul_self a)
  intro s hs
  simpa only [hs.spectralRadius_eq_nnnorm, (hs.starHom_apply φ).spectralRadius_eq_nnnorm,
    coe_le_coe] using
    show spectralRadius ℂ (φ s) ≤ spectralRadius ℂ s from
      iSup_le_iSup_of_subset (AlgHom.spectrum_apply_subset φ s)
#align star_alg_hom.nnnorm_apply_le StarAlgHom.nnnorm_apply_le

/-- A star algebra homomorphism of complex C⋆-algebras is norm contractive. -/
theorem norm_apply_le (a : A) : ‖(φ a : B)‖ ≤ ‖a‖ :=
  nnnorm_apply_le φ a
#align star_alg_hom.norm_apply_le StarAlgHom.norm_apply_le

/-- Star algebra homomorphisms between C⋆-algebras are continuous linear maps.
See note [lower instance priority] -/
noncomputable instance (priority := 100) : ContinuousLinearMapClass F ℂ A B :=
  { AlgHomClass.linearMapClass with
    map_continuous := fun φ =>
      AddMonoidHomClass.continuous_of_bound φ 1 (by simpa only [one_mul] using nnnorm_apply_le φ) }

end StarAlgHom

namespace StarAlgEquiv

variable {F A B : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [StarRing A]
  [CstarRing A] [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B] [StarRing B] [CstarRing B]
  [EquivLike F A B] [NonUnitalAlgEquivClass F ℂ A B] [StarAlgEquivClass F ℂ A B]

lemma nnnorm_map (φ : F) (a : A) : ‖φ a‖₊ = ‖a‖₊ :=
  le_antisymm (StarAlgHom.nnnorm_apply_le φ a) <| by
    simpa using StarAlgHom.nnnorm_apply_le (symm (φ : A ≃⋆ₐ[ℂ] B)) ((φ : A ≃⋆ₐ[ℂ] B) a)

lemma norm_map (φ : F) (a : A) : ‖φ a‖ = ‖a‖ :=
  congr_arg NNReal.toReal (nnnorm_map φ a)

lemma isometry (φ : F) : Isometry φ :=
  AddMonoidHomClass.isometry_of_norm φ (norm_map φ)

end StarAlgEquiv

end

namespace WeakDual

open ContinuousMap Complex

open scoped ComplexStarModule

variable {F A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [StarRing A]
  [CstarRing A] [StarModule ℂ A] [FunLike F A ℂ] [hF : AlgHomClass F ℂ A ℂ]

/-- This instance is provided instead of `StarAlgHomClass` to avoid type class inference loops.
See note [lower instance priority] -/
noncomputable instance (priority := 100) Complex.instStarHomClass : StarHomClass F A ℂ where
  map_star φ a := by
    suffices hsa : ∀ s : selfAdjoint A, (φ s)⋆ = φ s by
      rw [← realPart_add_I_smul_imaginaryPart a]
      simp only [map_add, map_smul, star_add, star_smul, hsa, selfAdjoint.star_val_eq]
    intro s
    have := AlgHom.apply_mem_spectrum φ (s : A)
    rw [selfAdjoint.val_re_map_spectrum s] at this
    rcases this with ⟨⟨_, _⟩, _, heq⟩
    simp only [Function.comp_apply] at heq
    rw [← heq, RCLike.star_def]
    exact RCLike.conj_ofReal _

/-- This is not an instance to avoid type class inference loops. See
`WeakDual.Complex.instStarHomClass`. -/
lemma _root_.AlgHomClass.instStarAlgHomClass : StarAlgHomClass F ℂ A ℂ :=
  { WeakDual.Complex.instStarHomClass, hF with }
#align alg_hom_class.star_alg_hom_class AlgHomClass.instStarAlgHomClass

namespace CharacterSpace

noncomputable instance instStarAlgHomClass : StarAlgHomClass (characterSpace ℂ A) ℂ A ℂ :=
  { AlgHomClass.instStarAlgHomClass with }

end CharacterSpace

end WeakDual
