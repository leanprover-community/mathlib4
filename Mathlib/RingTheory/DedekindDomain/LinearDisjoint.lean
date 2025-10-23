/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.RingTheory.DedekindDomain.Different

/-!
# Disjoint extensions with coprime different ideals

Let `A ⊆ B` be a finite extension of Dedekind domains and assume that `A ⊆ R₁, R₂ ⊆ B` are two
subrings such that `Frac R₁ ⊔ Frac R₂ = Frac B`, `Frac R₁` and `Frac R₂` are linearly disjoint
over `Frac A`, and that `𝓓(R₁/A)` and `𝓓(R₂/A)` are coprime where `𝓓` denotes the different ideal
and `Frac R` denotes the fraction field of a domain `R`.

# Main results

* `FractionalIdeal.differentIdeal_eq_map_differentIdeal`: `𝓓(B/R₁) = 𝓓(R₂/A)`
* `FractionalIdeal.differentIdeal_eq_differentIdeal_mul_differentIdeal_of_isCoprime`:
  `𝓓(B/A) = 𝓓(R₁/A) * 𝓓(R₂/A)`.

-/

open FractionalIdeal nonZeroDivisors IntermediateField Algebra Module Submodule

variable (A B : Type*) {K L : Type*} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
  [CommRing B] [Field L] [Algebra B L] [Algebra A L] [Algebra K L] [FiniteDimensional K L]
  [IsScalarTower A K L]
variable (R₁ R₂ : Type*) [CommRing R₁] [CommRing R₂] [Algebra A R₁] [Algebra A R₂] [Algebra R₁ B]
  [Algebra R₂ B] [Algebra R₁ L] [Algebra R₂ L] [IsScalarTower A R₁ L] [IsScalarTower R₁ B L]
  [IsScalarTower R₂ B L] [Module.Finite A R₂]
variable {F₁ F₂ : IntermediateField K L} [Algebra R₁ F₁] [Algebra R₂ F₂] [NoZeroSMulDivisors R₁ F₁]
  [IsScalarTower A F₂ L] [IsScalarTower A R₂ F₂] [IsScalarTower R₁ F₁ L] [IsScalarTower R₂ F₂ L]
  [Algebra.IsSeparable K F₂] [Algebra.IsSeparable F₁ L]

theorem Submodule.traceDual_le_span_map_traceDual [Module.Free A R₂]
    [IsLocalization (Algebra.algebraMapSubmonoid R₂ A⁰) F₂] (h₁ : F₁.LinearDisjoint F₂)
    (h₂ : F₁ ⊔ F₂ = ⊤) :
    (traceDual R₁ F₁ (1 : Submodule B L)).restrictScalars R₁ ≤
      span R₁ (algebraMap F₂ L '' (traceDual A K (1 : Submodule R₂ F₂))) := by
  intro x hx
  have h₂' : F₁.toSubalgebra ⊔ F₂.toSubalgebra = ⊤ := by
    simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg IntermediateField.toSubalgebra h₂
  let b₂ := (Free.chooseBasis A R₂).localizationLocalization K A⁰ F₂
  let B₁ := h₁.basisOfBasisRight h₂' b₂
  have h_main : x ∈ span R₁ (Set.range B₁.traceDual) := by
    rw [B₁.traceDual.mem_span_iff_repr_mem R₁ x]
    intro i
    rw [B₁.traceDual_repr_apply]
    refine mem_traceDual.mp hx _ ?_
    rw [LinearDisjoint.basisOfBasisRight_apply, Basis.localizationLocalization_apply,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R₂ B L, mem_one]
    exact ⟨_, rfl⟩
  have h : Set.range B₁.traceDual =
      Set.range (IsScalarTower.toAlgHom A F₂ L ∘ b₂.traceDual) := by
    refine congr_arg Set.range <| B₁.traceDual_eq_iff.mpr fun i j ↦ ?_
    rw [LinearDisjoint.basisOfBasisRight_apply, traceForm_apply, Function.comp_apply,
      IsScalarTower.coe_toAlgHom', ← map_mul, h₁.trace_algebraMap h₂, b₂.trace_traceDual_mul,
      MonoidWithZeroHom.map_ite_one_zero]
  rwa [← span_span_of_tower A R₁, h, Set.range_comp, ← map_span,
    ← traceDual_span_of_basis A (1 : Submodule R₂ F₂) b₂
      (by rw [Basis.localizationLocalization_span K A⁰ F₂]; ext; simp)] at h_main

attribute [local instance] FractionRing.liftAlgebra

variable [IsDomain A] [IsDedekindDomain B] [IsDedekindDomain R₁] [IsDedekindDomain R₂]
    [IsFractionRing B L] [IsFractionRing R₁ F₁] [IsFractionRing R₂ F₂] [IsIntegrallyClosed A]
    [IsIntegralClosure B R₁ L] [NoZeroSMulDivisors R₁ B] [NoZeroSMulDivisors R₂ B]

namespace FractionalIdeal

theorem differentIdeal_dvd_map_differentIdeal [Algebra.IsIntegral R₂ B]
    [Module.Free A R₂] [IsLocalization (Algebra.algebraMapSubmonoid R₂ A⁰) F₂]
    (h₁ : F₁.LinearDisjoint F₂) (h₂ : F₁ ⊔ F₂ = ⊤) :
    differentIdeal R₁ B ∣ Ideal.map (algebraMap R₂ B) (differentIdeal A R₂) := by
  have : Algebra.IsSeparable (FractionRing A) (FractionRing R₂) := by
    refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv A K).symm.toRingEquiv
          (FractionRing.algEquiv R₂ F₂).symm.toRingEquiv ?_
    ext x
    obtain ⟨r, s, -, rfl⟩ := IsFractionRing.div_surjective (A := A) x
    simp_rw [AlgEquiv.toRingEquiv_eq_coe, map_div₀, RingHom.coe_comp,
      RingHom.coe_coe, Function.comp_apply, AlgEquiv.coe_ringEquiv,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A R₂ F₂,
      AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  rw [Ideal.dvd_iff_le, ← coeIdeal_le_coeIdeal L, coeIdeal_differentIdeal R₁ F₁ L B,
    ← extendedHomₐ_coeIdeal_eq_map L B (K := F₂), le_inv_comm _ (by simp), ← map_inv₀,
    coeIdeal_differentIdeal A K, inv_inv, ← coe_le_coe, coe_dual_one, coe_extendedHomₐ_eq_span,
    ← coeToSet_coeToSubmodule, coe_dual_one]
  · have := Submodule.span_mono (R := B) <| traceDual_le_span_map_traceDual A B R₁ R₂ h₁ h₂
    rwa [← span_coe_eq_restrictScalars, span_span_of_tower, span_span_of_tower, span_eq] at this
  · exact (_root_.map_ne_zero _).mpr <| coeIdeal_eq_zero.not.mpr differentIdeal_ne_bot

variable [Algebra A B] [Module.Finite A B] [NoZeroSMulDivisors A B] [NoZeroSMulDivisors A R₁]
  [NoZeroSMulDivisors A R₂] [Module.Finite A R₁] [Module.Finite R₂ B] [IsScalarTower A R₂ B]
  [Module.Finite R₁ B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
  [IsScalarTower A R₁ B]

theorem map_differentIdeal_dvd_differentIdeal
    (h : IsCoprime ((differentIdeal A R₁).map (algebraMap R₁ B))
      ((differentIdeal A R₂).map (algebraMap R₂ B))) :
    Ideal.map (algebraMap R₂ B) (differentIdeal A R₂) ∣ differentIdeal R₁ B :=
  have := (differentIdeal_eq_differentIdeal_mul_differentIdeal A R₂ B).symm.trans
    (differentIdeal_eq_differentIdeal_mul_differentIdeal A R₁ B)
  h.symm.dvd_of_dvd_mul_right (dvd_of_mul_left_eq _ this)

theorem differentIdeal_eq_map_differentIdeal [Module.Free A R₂] (h₁ : F₁.LinearDisjoint F₂)
    (h₂ : F₁ ⊔ F₂ = ⊤) (h₃ : IsCoprime ((differentIdeal A R₁).map (algebraMap R₁ B))
      ((differentIdeal A R₂).map (algebraMap R₂ B))) :
    differentIdeal R₁ B = Ideal.map (algebraMap R₂ B) (differentIdeal A R₂) := by
  apply dvd_antisymm
  · exact differentIdeal_dvd_map_differentIdeal A B R₁ R₂ h₁ h₂
  · exact map_differentIdeal_dvd_differentIdeal A B R₁ R₂ h₃

theorem differentIdeal_eq_differentIdeal_mul_differentIdeal_of_isCoprime
    [Module.Free A R₂] (h₁ : F₁.LinearDisjoint F₂) (h₂ : F₁ ⊔ F₂ = ⊤)
    (h₃ : IsCoprime ((differentIdeal A R₁).map (algebraMap R₁ B))
      ((differentIdeal A R₂).map (algebraMap R₂ B))) :
    differentIdeal A B = differentIdeal R₁ B * differentIdeal R₂ B := by
  have := differentIdeal_eq_differentIdeal_mul_differentIdeal A R₂ B
  rwa [← differentIdeal_eq_map_differentIdeal A B R₁ R₂ h₁ h₂ h₃,
    mul_comm] at this

end FractionalIdeal
