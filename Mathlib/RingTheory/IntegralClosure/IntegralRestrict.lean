/-
Copyright (c) 2023 Andrew Yang, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.NormTrace

/-!
# Restriction of various maps between fields to integrally closed subrings.

In this file, we assume `A` is an integrally closed domain; `K` is the fraction ring of `A`;
`L` is a finite (separable) extension of `K`; `B` is the integral closure of `A` in `L`.
We call this the AKLB setup.

## Main definition
- `galRestrict`: The restriction `Aut(L/K) → Aut(B/A)` as an `MulEquiv` in an AKLB setup.
- `Algebra.intTrace`: The trace map of a finite extension of integrally closed domains `B/A` is
defined to be the restriction of the trace map of `Frac(B)/Frac(A)`.
- `Algebra.intNorm`: The norm map of a finite extension of integrally closed domains `B/A` is
defined to be the restriction of the norm map of `Frac(B)/Frac(A)`.

-/
open nonZeroDivisors

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L]

section galois

variable [Algebra.IsAlgebraic K L]

/-- The lift `End(B/A) → End(L/K)` in an ALKB setup.
This is inverse to the restriction. See `galRestrictHom`. -/
noncomputable
def galLift (σ : B →ₐ[A] B) : L →ₐ[K] L :=
  haveI := (IsFractionRing.injective A K).isDomain
  haveI := NoZeroSMulDivisors.trans_faithfulSMul A K L
  haveI := IsIntegralClosure.isLocalization A K L B
  haveI H : ∀ (y :  Algebra.algebraMapSubmonoid B A⁰),
      IsUnit (((algebraMap B L).comp σ) (y : B)) := by
    rintro ⟨_, x, hx, rfl⟩
    simpa only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, AlgHom.commutes,
      isUnit_iff_ne_zero, ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _),
      ← IsScalarTower.algebraMap_apply] using nonZeroDivisors.ne_zero hx
  haveI H_eq : (IsLocalization.lift (S := L) H).comp (algebraMap K L) = (algebraMap K L) := by
    apply IsLocalization.ringHom_ext A⁰
    ext
    simp only [RingHom.coe_comp, Function.comp_apply, ← IsScalarTower.algebraMap_apply A K L,
      IsScalarTower.algebraMap_apply A B L, IsLocalization.lift_eq,
      RingHom.coe_coe, AlgHom.commutes]
  { IsLocalization.lift (S := L) H with commutes' := DFunLike.congr_fun H_eq }

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
    simp only [AlgEquiv.symm_apply_apply, AlgHom.coe_codRestrict, AlgHom.coe_restrictScalars',
      AlgHom.coe_comp, IsScalarTower.coe_toAlgHom', Function.comp_apply,
      AlgHom.mul_apply, IsIntegralClosure.algebraMap_equiv, Subalgebra.algebraMap_eq]
    rfl
  invFun := galLift A K L B
  left_inv σ :=
    have := (IsFractionRing.injective A K).isDomain
    have := IsIntegralClosure.isLocalization A K L B
    AlgHom.coe_ringHom_injective <| IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid B A⁰)
      <| RingHom.ext fun x ↦ by simp [Subalgebra.algebraMap_eq, galLift]
  right_inv σ :=
    have := (IsFractionRing.injective A K).isDomain
    have := IsIntegralClosure.isLocalization A K L B
    AlgHom.ext fun x ↦ IsIntegralClosure.algebraMap_injective B A L
      (by simp [Subalgebra.algebraMap_eq, galLift])

@[simp]
lemma algebraMap_galRestrictHom_apply (σ : L →ₐ[K] L) (x : B) :
    algebraMap B L (galRestrictHom A K L B σ x) = σ (algebraMap B L x) := by
  simp [galRestrictHom, Subalgebra.algebraMap_eq]

@[simp, nolint unusedHavesSuffices] -- false positive from unfolding galRestrictHom
lemma galRestrictHom_symm_algebraMap_apply (σ : B →ₐ[A] B) (x : B) :
    (galRestrictHom A K L B).symm σ (algebraMap B L x) = algebraMap B L (σ x) := by
  have := (IsFractionRing.injective A K).isDomain
  have := IsIntegralClosure.isLocalization A K L B
  simp [galRestrictHom, galLift]

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

end galois

variable [FiniteDimensional K L]

lemma prod_galRestrict_eq_norm [IsGalois K L] [IsIntegrallyClosed A] (x : B) :
    (∏ σ : L ≃ₐ[K] L, galRestrict A K L B σ x) =
    algebraMap A B (IsIntegralClosure.mk' (R := A) A (Algebra.norm K <| algebraMap B L x)
      (Algebra.isIntegral_norm K (IsIntegralClosure.isIntegral A L x).algebraMap)) := by
  apply IsIntegralClosure.algebraMap_injective B A L
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_eq A K L]
  simp only [map_prod, algebraMap_galRestrict_apply, IsIntegralClosure.algebraMap_mk',
    Algebra.norm_eq_prod_automorphisms, RingHom.coe_comp, Function.comp_apply]

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

noncomputable
instance (priority := 900) [IsDomain A] [IsDomain B] [IsIntegrallyClosed B]
    [Module.Finite A B] [NoZeroSMulDivisors A B] : Fintype (B ≃ₐ[A] B) :=
  haveI : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  haveI : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  Fintype.ofEquiv _ (galRestrict A (FractionRing A) (FractionRing B) B).toEquiv

variable {Aₘ Bₘ} [CommRing Aₘ] [CommRing Bₘ] [Algebra Aₘ Bₘ] [Algebra A Aₘ] [Algebra B Bₘ]
variable [Algebra A Bₘ] [IsScalarTower A Aₘ Bₘ] [IsScalarTower A B Bₘ]
variable (M : Submonoid A) [IsLocalization M Aₘ]
variable [IsLocalization (Algebra.algebraMapSubmonoid B M) Bₘ]

section trace

/-- The restriction of the trace on `L/K` restricted onto `B/A` in an AKLB setup.
See `Algebra.intTrace` instead. -/
noncomputable
def Algebra.intTraceAux [IsIntegrallyClosed A] :
    B →ₗ[A] A :=
  (IsIntegralClosure.equiv A (integralClosure A K) K A).toLinearMap.comp
    ((((Algebra.trace K L).restrictScalars A).comp
      (IsScalarTower.toAlgHom A B L).toLinearMap).codRestrict
        (Subalgebra.toSubmodule <| integralClosure A K) (fun x ↦ isIntegral_trace
          (IsIntegral.algebraMap (IsIntegralClosure.isIntegral A L x))))

variable {A K L B}

lemma Algebra.map_intTraceAux [IsIntegrallyClosed A] (x : B) :
    algebraMap A K (Algebra.intTraceAux A K L B x) = Algebra.trace K L (algebraMap B L x) :=
  IsIntegralClosure.algebraMap_equiv A (integralClosure A K) K A _

variable (A B)
variable [IsDomain A] [IsIntegrallyClosed A] [IsDomain B] [IsIntegrallyClosed B]
variable [Module.Finite A B] [NoZeroSMulDivisors A B]

/-- The trace of a finite extension of integrally closed domains `B/A` is the restriction of
the trace on `Frac(B)/Frac(A)` onto `B/A`. See `Algebra.algebraMap_intTrace`. -/
noncomputable
def Algebra.intTrace : B →ₗ[A] A :=
  haveI : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  haveI : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  haveI : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  Algebra.intTraceAux A (FractionRing A) (FractionRing B) B

variable {A B}

lemma Algebra.algebraMap_intTrace (x : B) :
    algebraMap A K (Algebra.intTrace A B x) = Algebra.trace K L (algebraMap B L x) := by
  haveI : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  haveI : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  haveI : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  haveI := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  apply (FractionRing.algEquiv A K).symm.injective
  rw [AlgEquiv.commutes, Algebra.intTrace, Algebra.map_intTraceAux,
    ← AlgEquiv.commutes (FractionRing.algEquiv B L)]
  apply Algebra.trace_eq_of_equiv_equiv (FractionRing.algEquiv A K).toRingEquiv
    (FractionRing.algEquiv B L).toRingEquiv
  apply IsLocalization.ringHom_ext A⁰
  simp only [AlgEquiv.toRingEquiv_eq_coe, ← AlgEquiv.coe_ringHom_commutes, RingHom.comp_assoc,
    AlgHom.comp_algebraMap_of_tower, ← IsScalarTower.algebraMap_eq, RingHom.comp_assoc]

lemma Algebra.algebraMap_intTrace_fractionRing (x : B) :
    algebraMap A (FractionRing A) (Algebra.intTrace A B x) =
      Algebra.trace (FractionRing A) (FractionRing B) (algebraMap B _ x) := by
  haveI : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  haveI : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  haveI : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  exact Algebra.map_intTraceAux x

variable (A B)

lemma Algebra.intTrace_eq_trace [Module.Free A B] : Algebra.intTrace A B = Algebra.trace A B := by
  ext x
  haveI : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  haveI : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  apply IsFractionRing.injective A (FractionRing A)
  rw [Algebra.algebraMap_intTrace_fractionRing, Algebra.trace_localization A A⁰]

open nonZeroDivisors

variable [IsDomain Aₘ] [IsIntegrallyClosed Aₘ] [IsDomain Bₘ] [IsIntegrallyClosed Bₘ]
variable [NoZeroSMulDivisors Aₘ Bₘ] [Module.Finite Aₘ Bₘ]

include M in
lemma Algebra.intTrace_eq_of_isLocalization
    (x : B) :
    algebraMap A Aₘ (Algebra.intTrace A B x) = Algebra.intTrace Aₘ Bₘ (algebraMap B Bₘ x) := by
  by_cases hM : 0 ∈ M
  · subsingleton [IsLocalization.uniqueOfZeroMem (S := Aₘ) hM]
  replace hM : M ≤ A⁰ := fun x hx ↦ mem_nonZeroDivisors_iff_ne_zero.mpr (fun e ↦ hM (e ▸ hx))
  let K := FractionRing A
  let L := FractionRing B
  have : IsIntegralClosure B A L :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  have : IsLocalization (algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  let f : Aₘ →+* K := IsLocalization.map _ (T := A⁰) (RingHom.id A) hM
  letI := f.toAlgebra
  have : IsScalarTower A Aₘ K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  letI := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M Aₘ K
  let g : Bₘ →+* L := IsLocalization.map _
      (M := algebraMapSubmonoid B M) (T := algebraMapSubmonoid B A⁰)
      (RingHom.id B) (Submonoid.monotone_map hM)
  letI := g.toAlgebra
  have : IsScalarTower B Bₘ L := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  letI := ((algebraMap K L).comp f).toAlgebra
  have : IsScalarTower Aₘ K L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Aₘ Bₘ L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext M
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra (R := Bₘ), RingHom.comp_assoc,
      RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A B Bₘ,
      IsLocalization.map_comp, RingHom.comp_id, ← RingHom.comp_assoc, IsLocalization.map_comp,
      RingHom.comp_id, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  letI := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (algebraMapSubmonoid B M) Bₘ L
  have : FiniteDimensional K L := .of_isLocalization A B A⁰
  have : IsIntegralClosure Bₘ Aₘ L :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  apply IsFractionRing.injective Aₘ K
  rw [← IsScalarTower.algebraMap_apply, Algebra.algebraMap_intTrace_fractionRing,
    Algebra.algebraMap_intTrace (L := L), ← IsScalarTower.algebraMap_apply]

end trace

section norm

variable [IsIntegrallyClosed A]

/-- The restriction of the norm on `L/K` restricted onto `B/A` in an AKLB setup.
See `Algebra.intNorm` instead. -/
noncomputable
def Algebra.intNormAux [Algebra.IsSeparable K L] :
    B →* A where
  toFun := fun s ↦ IsIntegralClosure.mk' (R := A) A (Algebra.norm K (algebraMap B L s))
    (isIntegral_norm K <| IsIntegral.map (IsScalarTower.toAlgHom A B L)
      (IsIntegralClosure.isIntegral A L s))
  map_one' := by simp
  map_mul' := fun x y ↦ by simpa using IsIntegralClosure.mk'_mul _ _ _ _ _

variable {A K L B}

lemma Algebra.map_intNormAux [Algebra.IsSeparable K L] (x : B) :
    algebraMap A K (Algebra.intNormAux A K L B x) = Algebra.norm K (algebraMap B L x) := by
  dsimp [Algebra.intNormAux]
  exact IsIntegralClosure.algebraMap_mk' _ _ _

variable (A B)
variable [IsDomain A] [IsDomain B] [IsIntegrallyClosed B]
variable [Module.Finite A B] [NoZeroSMulDivisors A B]
variable [Algebra.IsSeparable (FractionRing A) (FractionRing B)] -- TODO: remove this

/-- The norm of a finite extension of integrally closed domains `B/A` is the restriction of
the norm on `Frac(B)/Frac(A)` onto `B/A`. See `Algebra.algebraMap_intNorm`. -/
noncomputable
def Algebra.intNorm : B →* A :=
  haveI : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  haveI : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  haveI : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  Algebra.intNormAux A (FractionRing A) (FractionRing B) B

variable {A B}

lemma Algebra.algebraMap_intNorm (x : B) :
    algebraMap A K (Algebra.intNorm A B x) = Algebra.norm K (algebraMap B L x) := by
  haveI : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  haveI : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  haveI : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  haveI := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  apply (FractionRing.algEquiv A K).symm.injective
  rw [AlgEquiv.commutes, Algebra.intNorm, Algebra.map_intNormAux,
    ← AlgEquiv.commutes (FractionRing.algEquiv B L)]
  apply Algebra.norm_eq_of_equiv_equiv (FractionRing.algEquiv A K).toRingEquiv
    (FractionRing.algEquiv B L).toRingEquiv
  apply IsLocalization.ringHom_ext A⁰
  simp only [AlgEquiv.toRingEquiv_eq_coe, ← AlgEquiv.coe_ringHom_commutes, RingHom.comp_assoc,
    AlgHom.comp_algebraMap_of_tower, ← IsScalarTower.algebraMap_eq, RingHom.comp_assoc]

@[simp]
lemma Algebra.algebraMap_intNorm_fractionRing (x : B) :
    algebraMap A (FractionRing A) (Algebra.intNorm A B x) =
      Algebra.norm (FractionRing A) (algebraMap B (FractionRing B) x) := by
  haveI : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  haveI : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  haveI : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  exact Algebra.map_intNormAux x

variable (A B)

lemma Algebra.intNorm_eq_norm [Module.Free A B] : Algebra.intNorm A B = Algebra.norm A := by
  ext x
  haveI : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  haveI : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  apply IsFractionRing.injective A (FractionRing A)
  rw [Algebra.algebraMap_intNorm_fractionRing, Algebra.norm_localization A A⁰]

@[simp]
lemma Algebra.intNorm_zero : Algebra.intNorm A B 0 = 0 := by
  haveI : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  haveI : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  haveI : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  apply IsFractionRing.injective A (FractionRing A)
  simp

variable {A B}

@[simp]
lemma Algebra.intNorm_eq_zero {x : B} : Algebra.intNorm A B x = 0 ↔ x = 0 := by
  haveI : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  haveI : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  haveI : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  rw [← (IsFractionRing.injective A (FractionRing A)).eq_iff,
    ← (IsFractionRing.injective B (FractionRing B)).eq_iff]
  simp only [algebraMap_intNorm_fractionRing, map_zero, norm_eq_zero_iff]

lemma Algebra.intNorm_ne_zero {x : B} : Algebra.intNorm A B x ≠ 0 ↔ x ≠ 0 := by simp

variable [IsDomain Aₘ] [IsIntegrallyClosed Aₘ] [IsDomain Bₘ] [IsIntegrallyClosed Bₘ]
variable [NoZeroSMulDivisors Aₘ Bₘ] [Module.Finite Aₘ Bₘ]
variable [Algebra.IsSeparable (FractionRing Aₘ) (FractionRing Bₘ)]

include M in
lemma Algebra.intNorm_eq_of_isLocalization (x : B) :
    algebraMap A Aₘ (Algebra.intNorm A B x) = Algebra.intNorm Aₘ Bₘ (algebraMap B Bₘ x) := by
  by_cases hM : 0 ∈ M
  · subsingleton [IsLocalization.uniqueOfZeroMem (S := Aₘ) hM]
  replace hM : M ≤ A⁰ := fun x hx ↦ mem_nonZeroDivisors_iff_ne_zero.mpr (fun e ↦ hM (e ▸ hx))
  let K := FractionRing A
  let L := FractionRing B
  have : IsIntegralClosure B A L :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  have : IsLocalization (algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  let f : Aₘ →+* K := IsLocalization.map _ (T := A⁰) (RingHom.id A) hM
  letI := f.toAlgebra
  have : IsScalarTower A Aₘ K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  letI := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M Aₘ K
  let g : Bₘ →+* L := IsLocalization.map _
      (M := algebraMapSubmonoid B M) (T := algebraMapSubmonoid B A⁰)
      (RingHom.id B) (Submonoid.monotone_map hM)
  letI := g.toAlgebra
  have : IsScalarTower B Bₘ L := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  letI := ((algebraMap K L).comp f).toAlgebra
  have : IsScalarTower Aₘ K L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Aₘ Bₘ L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext M
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra (R := Bₘ), RingHom.comp_assoc,
      RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A B Bₘ,
      IsLocalization.map_comp, RingHom.comp_id, ← RingHom.comp_assoc, IsLocalization.map_comp,
      RingHom.comp_id, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  letI := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (algebraMapSubmonoid B M) Bₘ L
  have : FiniteDimensional K L := .of_isLocalization A B A⁰
  have : IsIntegralClosure Bₘ Aₘ L :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  apply IsFractionRing.injective Aₘ K
  rw [← IsScalarTower.algebraMap_apply, Algebra.algebraMap_intNorm_fractionRing,
    Algebra.algebraMap_intNorm (L := L), ← IsScalarTower.algebraMap_apply]

end norm

lemma Algebra.algebraMap_intNorm_of_isGalois
    [IsDomain A] [IsIntegrallyClosed A] [IsDomain B] [IsIntegrallyClosed B]
    [Module.Finite A B] [NoZeroSMulDivisors A B] [IsGalois (FractionRing A) (FractionRing B)]
    {x : B} :
    algebraMap A B (Algebra.intNorm A B x) = ∏ σ : B ≃ₐ[A] B, σ x := by
  haveI : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  haveI : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  rw [← (galRestrict A (FractionRing A) (FractionRing B) B).toEquiv.prod_comp]
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  convert (prod_galRestrict_eq_norm A (FractionRing A) (FractionRing B) B x).symm
