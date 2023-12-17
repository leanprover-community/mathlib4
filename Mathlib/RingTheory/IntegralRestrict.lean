/-
Copyright (c) 2023 Andrew Yang, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.IntegrallyClosed
import Mathlib.RingTheory.Norm
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
/-!
# Restriction of various maps between fields to integrally closed subrings.

In this file, we assume `A` is an integrally closed domain; `K` is the fraction ring of `A`;
`L` is a finite (separable) extension of `K`; `B` is the integral closure of `A` in `L`.
We call this the AKLB setup.

## Main definition
- `galRestrict`: The restriction `Aut(L/K) → Aut(B/A)` as an `MulEquiv` in an AKLB setup.

## TODO
Define the restriction of norms and traces.

-/
open BigOperators nonZeroDivisors

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [FiniteDimensional K L]

/-- The lift `End(B/A) → End(L/K)` in an ALKB setup.
This is inverse to the restriction. See `galRestrictHom`. -/
noncomputable
def galLift (σ : B →ₐ[A] B) : L →ₐ[K] L :=
  haveI := (IsFractionRing.injective A K).isDomain
  haveI := NoZeroSMulDivisors.trans A K L
  haveI := IsIntegralClosure.isLocalization A K L B (Algebra.IsIntegral.of_finite _ _).isAlgebraic
  haveI H : ∀ (y :  Algebra.algebraMapSubmonoid B A⁰),
      IsUnit (((algebraMap B L).comp σ) (y : B)) := by
    rintro ⟨_, x, hx, rfl⟩
    simpa only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, AlgHom.commutes,
      isUnit_iff_ne_zero, ne_eq, map_eq_zero_iff _ (NoZeroSMulDivisors.algebraMap_injective _ _),
      ← IsScalarTower.algebraMap_apply] using nonZeroDivisors.ne_zero hx
  haveI H_eq : (IsLocalization.lift (S := L) H).comp (algebraMap K L) = (algebraMap K L) := by
    apply IsLocalization.ringHom_ext A⁰
    ext
    simp only [RingHom.coe_comp, Function.comp_apply, ← IsScalarTower.algebraMap_apply A K L,
      IsScalarTower.algebraMap_apply A B L, IsLocalization.lift_eq,
      RingHom.coe_coe, AlgHom.commutes]
  { IsLocalization.lift (S := L) H with commutes' := FunLike.congr_fun H_eq }

/-- The restriction `End(L/K) → End(B/A)` in an AKLB setup.
Also see `galRestrict` for the `AlgEquiv` version. -/
noncomputable
def galRestrictHom : (L →ₐ[K] L) ≃* (B →ₐ[A] B) where
  toFun := fun f ↦ (IsIntegralClosure.equiv A (integralClosure A L) L B).toAlgHom.comp
      (((f.restrictScalars A).comp (IsScalarTower.toAlgHom A B L)).codRestrict
        (integralClosure A L) (fun x ↦ IsIntegral.map _ (IsIntegralClosure.isIntegral A L x)))
  map_mul' := by
    intros σ₁ σ₂
    ext x
    apply (IsIntegralClosure.equiv A (integralClosure A L) L B).symm.injective
    ext
    dsimp
    simp only [AlgEquiv.symm_apply_apply, AlgHom.coe_codRestrict, AlgHom.coe_comp,
      AlgHom.coe_restrictScalars', IsScalarTower.coe_toAlgHom', Function.comp_apply,
      AlgHom.mul_apply, IsIntegralClosure.algebraMap_equiv, Subalgebra.algebraMap_eq]
    rfl
  invFun := galLift A K L B
  left_inv σ :=
    have := (IsFractionRing.injective A K).isDomain
    have := IsIntegralClosure.isLocalization A K L B (Algebra.IsIntegral.of_finite _ _).isAlgebraic
    AlgHom.coe_ringHom_injective <| IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid B A⁰)
      <| RingHom.ext fun x ↦ by simp [Subalgebra.algebraMap_eq, galLift]
  right_inv σ :=
    have := (IsFractionRing.injective A K).isDomain
    have := IsIntegralClosure.isLocalization A K L B (Algebra.IsIntegral.of_finite _ _).isAlgebraic
    AlgHom.ext fun x ↦
      IsIntegralClosure.algebraMap_injective B A L (by simp [Subalgebra.algebraMap_eq, galLift])

@[simp]
lemma algebraMap_galRestrictHom_apply (σ : L →ₐ[K] L) (x : B) :
    algebraMap B L (galRestrictHom A K L B σ x) = σ (algebraMap B L x) := by
  simp [galRestrictHom, Subalgebra.algebraMap_eq]

@[simp, nolint unusedHavesSuffices] -- false positive from unfolding galRestrictHom
lemma galRestrictHom_symm_algebraMap_apply (σ : B →ₐ[A] B) (x : B) :
    (galRestrictHom A K L B).symm σ (algebraMap B L x) = algebraMap B L (σ x) := by
  have := (IsFractionRing.injective A K).isDomain
  have := IsIntegralClosure.isLocalization A K L B (Algebra.IsIntegral.of_finite _ _).isAlgebraic
  simp [galRestrictHom, galLift, Subalgebra.algebraMap_eq]

/-- The restriction `Aut(L/K) → Aut(B/A)` in an AKLB setup. -/
noncomputable
def galRestrict : (L ≃ₐ[K] L) ≃* (B ≃ₐ[A] B) :=
  (AlgEquiv.algHomUnitsEquiv K L).symm.trans
    ((Units.mapEquiv <| galRestrictHom A K L B).trans (AlgEquiv.algHomUnitsEquiv A B))

variable {K L}

lemma coe_galRestrict_apply (σ : L ≃ₐ[K] L) :
    (galRestrict A K L B σ : B →ₐ[A] B) = galRestrictHom A K L B σ := rfl

variable {B}

lemma galRestrict_apply (σ : L ≃ₐ[K] L) (x : B) :
    galRestrict A K L B σ x = galRestrictHom A K L B σ x := rfl

lemma algebraMap_galRestrict_apply (σ : L ≃ₐ[K] L) (x : B) :
    algebraMap B L (galRestrict A K L B σ x) = σ (algebraMap B L x) :=
  algebraMap_galRestrictHom_apply A K L B σ.toAlgHom x

variable (K L B)

lemma prod_galRestrict_eq_norm [IsGalois K L] [IsIntegrallyClosed A] (x : B) :
    (∏ σ : L ≃ₐ[K] L, galRestrict A K L B σ x) =
    algebraMap A B (IsIntegralClosure.mk' (R := A) A (Algebra.norm K <| algebraMap B L x)
      (Algebra.isIntegral_norm K (IsIntegralClosure.isIntegral A L x).algebraMap)) := by
  apply IsIntegralClosure.algebraMap_injective B A L
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_eq A K L]
  simp only [map_prod, algebraMap_galRestrict_apply, IsIntegralClosure.algebraMap_mk',
    Algebra.norm_eq_prod_automorphisms, AlgHom.coe_coe, RingHom.coe_comp, Function.comp_apply]
