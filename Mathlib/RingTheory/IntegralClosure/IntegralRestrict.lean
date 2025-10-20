/-
Copyright (c) 2023 Andrew Yang, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.Norm.Transitivity

/-!
# Restriction of various maps between fields to integrally closed subrings.

In this file, we assume `A` is an integrally closed domain; `K` is the fraction ring of `A`;
`L` is a finite extension of `K`; `B` is the integral closure of `A` in `L`.
We call this the AKLB setup.

## Main definition
- `galRestrict`: The restriction `Aut(L/K) → Aut(B/A)` as an `MulEquiv` in an AKLB setup.
- `Algebra.intTrace`: The trace map of a finite extension of integrally closed domains `B/A` is
defined to be the restriction of the trace map of `Frac(B)/Frac(A)`.
- `Algebra.intNorm`: The norm map of a finite extension of integrally closed domains `B/A` is
defined to be the restriction of the norm map of `Frac(B)/Frac(A)`.

-/
open nonZeroDivisors

variable (A K L L₂ L₃ B B₂ B₃ : Type*)
variable [CommRing A] [CommRing B] [CommRing B₂] [CommRing B₃]
variable [Algebra A B] [Algebra A B₂] [Algebra A B₃]
variable [Field K] [Field L] [Field L₂] [Field L₃]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]
variable [Algebra K L₂] [Algebra A L₂] [IsScalarTower A K L₂]
variable [Algebra K L₃] [Algebra A L₃] [IsScalarTower A K L₃]
variable [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]
variable [Algebra B₂ L₂] [IsScalarTower A B₂ L₂] [IsIntegralClosure B₂ A L₂]
variable [Algebra B₃ L₃] [IsScalarTower A B₃ L₃] [IsIntegralClosure B₃ A L₃]

section galois

section galRestrict'
variable {K L L₂ L₃}
omit [IsFractionRing A K]

/-- A generalization of `galRestrictHom` beyond endomorphisms. -/
noncomputable
def galRestrict' (f : L →ₐ[K] L₂) : (B →ₐ[A] B₂) :=
  (IsIntegralClosure.equiv A (integralClosure A L₂) L₂ B₂).toAlgHom.comp
      (((f.restrictScalars A).comp (IsScalarTower.toAlgHom A B L)).codRestrict
        (integralClosure A L₂) (fun x ↦ IsIntegral.map _ (IsIntegralClosure.isIntegral A L x)))

@[simp]
lemma algebraMap_galRestrict'_apply (σ : L →ₐ[K] L₂) (x : B) :
    algebraMap B₂ L₂ (galRestrict' A B B₂ σ x) = σ (algebraMap B L x) := by
  simp [galRestrict', galRestrict', Subalgebra.algebraMap_eq]

@[simp]
theorem galRestrict'_id : galRestrict' A B B (.id K L) = .id A B := by
  ext
  apply IsIntegralClosure.algebraMap_injective B A L
  simp

theorem galRestrict'_comp (σ : L →ₐ[K] L₂) (σ' : L₂ →ₐ[K] L₃) :
    galRestrict' A B B₃ (σ'.comp σ) = (galRestrict' A B₂ B₃ σ').comp (galRestrict' A B B₂ σ) := by
  ext x
  apply (IsIntegralClosure.equiv A (integralClosure A L₃) L₃ B₃).symm.injective
  ext
  simp [galRestrict', Subalgebra.algebraMap_eq]

end galRestrict'

variable [Algebra.IsAlgebraic K L]

section galLift
variable {A B B₂ B₃}

/-- A generalization of the lift `End(B/A) → End(L/K)` in an ALKB setup.
This is inverse to the restriction. See `galRestrictHom`. -/
noncomputable
def galLift (σ : B →ₐ[A] B₂) : L →ₐ[K] L₂ :=
  haveI := (IsFractionRing.injective A K).isDomain
  haveI := NoZeroSMulDivisors.trans_faithfulSMul A K L₂
  haveI := IsIntegralClosure.isLocalization A K L B
  haveI H : ∀ (y :  Algebra.algebraMapSubmonoid B A⁰),
      IsUnit (((algebraMap B₂ L₂).comp σ) (y : B)) := by
    rintro ⟨_, x, hx, rfl⟩
    simpa only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, AlgHom.commutes,
      isUnit_iff_ne_zero, ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _),
      ← IsScalarTower.algebraMap_apply] using nonZeroDivisors.ne_zero hx
  haveI H_eq : (IsLocalization.lift (S := L) H).comp (algebraMap K L) = (algebraMap K L₂) := by
    apply IsLocalization.ringHom_ext A⁰
    ext
    simp only [RingHom.coe_comp, Function.comp_apply, ← IsScalarTower.algebraMap_apply A K L,
      ← IsScalarTower.algebraMap_apply A K L₂,
      IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A B₂ L₂,
      IsLocalization.lift_eq, RingHom.coe_coe, AlgHom.commutes]
  { IsLocalization.lift (S := L) H with commutes' := DFunLike.congr_fun H_eq }

omit [IsIntegralClosure B₂ A L₂] in
@[simp]
theorem galLift_algebraMap_apply (σ : B →ₐ[A] B₂) (x : B) :
    galLift K L L₂ σ (algebraMap B L x) = algebraMap B₂ L₂ (σ x) := by
  simp [galLift]

@[simp]
theorem galLift_id : galLift K L L (.id A B) = .id K L := by
  ext; simp [galLift]

omit [IsIntegralClosure B₃ A L₃] in
theorem galLift_comp [Algebra.IsAlgebraic K L₂] (σ : B →ₐ[A] B₂) (σ' : B₂ →ₐ[A] B₃) :
    galLift K L L₃ (σ'.comp σ) = (galLift K L₂ L₃ σ').comp (galLift K L L₂ σ) :=
  have := (IsFractionRing.injective A K).isDomain
  have := IsIntegralClosure.isLocalization A K L B
  AlgHom.coe_ringHom_injective <| IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid B A⁰)
    <| RingHom.ext fun x ↦ by simp

@[simp]
theorem galLift_galRestrict' (σ : L →ₐ[K] L₂) :
    galLift K L L₂ (galRestrict' A B B₂ σ) = σ :=
  have := (IsFractionRing.injective A K).isDomain
  have := IsIntegralClosure.isLocalization A K L B
  AlgHom.coe_ringHom_injective <| IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid B A⁰)
    <| RingHom.ext fun x ↦ by simp [galRestrict', Subalgebra.algebraMap_eq, galLift]

@[simp]
theorem galRestrict'_galLift (σ : B →ₐ[A] B₂) :
    galRestrict' A B B₂ (galLift K L L₂ σ) = σ :=
  have := (IsFractionRing.injective A K).isDomain
  have := IsIntegralClosure.isLocalization A K L B
  AlgHom.ext fun x ↦ IsIntegralClosure.algebraMap_injective B₂ A L₂
    (by simp [galRestrict', Subalgebra.algebraMap_eq, galLift])

/--
A version of `galLift` for `AlgEquiv`.
-/
@[simps! -fullyApplied apply symm_apply]
noncomputable
def galLiftEquiv [Algebra.IsAlgebraic K L₂] (σ : B ≃ₐ[A] B₂) : L ≃ₐ[K] L₂ :=
  AlgEquiv.ofAlgHom (galLift K L L₂ σ.toAlgHom) (galLift K L₂ L σ.symm.toAlgHom)
  (by simp [← galLift_comp]) (by simp [← galLift_comp])

theorem galLiftEquiv_algebraMap_apply [Algebra.IsAlgebraic K L₂] (σ : B ≃ₐ[A] B₂) (x : B) :
    galLiftEquiv K L L₂ σ (algebraMap B L x) = algebraMap B₂ L₂ (σ x) := by
  simp [galLiftEquiv]

end galLift

/-- The restriction `End(L/K) → End(B/A)` in an AKLB setup.
Also see `galRestrict` for the `AlgEquiv` version. -/
@[simps -isSimp]
noncomputable
def galRestrictHom : (L →ₐ[K] L) ≃* (B →ₐ[A] B) where
  toFun f := galRestrict' A B B f
  map_mul' σ₁ σ₂ := galRestrict'_comp _ _ _ _ σ₂ σ₁
  invFun := galLift K L L
  left_inv σ := galLift_galRestrict' _ _ _ σ
  right_inv σ := galRestrict'_galLift _ _ _ σ

@[simp]
lemma algebraMap_galRestrictHom_apply (σ : L →ₐ[K] L) (x : B) :
    algebraMap B L (galRestrictHom A K L B σ x) = σ (algebraMap B L x) :=
  algebraMap_galRestrict'_apply _ _ _ _ _

@[simp, nolint unusedHavesSuffices] -- false positive from unfolding galRestrictHom
lemma galRestrictHom_symm_algebraMap_apply (σ : B →ₐ[A] B) (x : B) :
    (galRestrictHom A K L B).symm σ (algebraMap B L x) = algebraMap B L (σ x) :=
  galLift_algebraMap_apply _ _ _ _ _

/-- The restriction `Aut(L/K) → Aut(B/A)` in an AKLB setup. -/
noncomputable
def galRestrict : Gal(L/K) ≃* (B ≃ₐ[A] B) :=
  (AlgEquiv.algHomUnitsEquiv K L).symm.trans
    ((Units.mapEquiv <| galRestrictHom A K L B).trans (AlgEquiv.algHomUnitsEquiv A B))

variable {K L}

lemma coe_galRestrict_apply (σ : Gal(L/K)) :
    (galRestrict A K L B σ : B →ₐ[A] B) = galRestrictHom A K L B σ := rfl

variable {B}

lemma galRestrict_apply (σ : Gal(L/K)) (x : B) :
    galRestrict A K L B σ x = galRestrictHom A K L B σ x := rfl

lemma algebraMap_galRestrict_apply (σ : Gal(L/K)) (x : B) :
    algebraMap B L (galRestrict A K L B σ x) = σ (algebraMap B L x) :=
  algebraMap_galRestrictHom_apply A K L B σ.toAlgHom x

variable (K) in
lemma galRestrict_symm_algebraMap_apply (σ : B ≃ₐ[A] B) (x : B) :
    (galRestrict A K L B).symm σ (algebraMap B L x) = algebraMap B L (σ x) :=
  galRestrictHom_symm_algebraMap_apply A K L B σ x

end galois

variable [FiniteDimensional K L]

lemma prod_galRestrict_eq_norm [IsGalois K L] [IsIntegrallyClosed A] (x : B) :
    (∏ σ : Gal(L/K), galRestrict A K L B σ x) =
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
  ext
  exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A K) (FractionRing.algEquiv B L) _

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
def Algebra.intNormAux :
    B →* A where
  toFun := fun s ↦ IsIntegralClosure.mk' (R := A) A (Algebra.norm K (algebraMap B L s))
    (isIntegral_norm K <| IsIntegral.map (IsScalarTower.toAlgHom A B L)
      (IsIntegralClosure.isIntegral A L s))
  map_one' := by simp
  map_mul' := fun x y ↦ by simpa using IsIntegralClosure.mk'_mul _ _ _ _ _

variable {A K L B}

omit [FiniteDimensional K L] in
lemma Algebra.map_intNormAux (x : B) :
    algebraMap A K (Algebra.intNormAux A K L B x) = Algebra.norm K (algebraMap B L x) := by
  dsimp [Algebra.intNormAux]
  exact IsIntegralClosure.algebraMap_mk' _ _ _

variable (A B)
variable [IsDomain A] [IsDomain B] [IsIntegrallyClosed B]
variable [Module.Finite A B] [NoZeroSMulDivisors A B]

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
  ext
  exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A K) (FractionRing.algEquiv B L) _

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

theorem Algebra.intNorm_intNorm {C : Type*} [CommRing C] [IsDomain C] [IsIntegrallyClosed C]
    [Algebra A C] [Algebra B C] [IsScalarTower A B C] [Module.Finite A C] [Module.Finite B C]
    [NoZeroSMulDivisors A C] [NoZeroSMulDivisors B C] (x : C) :
    intNorm A B (intNorm B C x) = intNorm A C x := by
  apply FaithfulSMul.algebraMap_injective A (FractionRing A)
  rw [algebraMap_intNorm_fractionRing, algebraMap_intNorm_fractionRing,
    algebraMap_intNorm_fractionRing, Algebra.norm_norm]

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
theorem Algebra.intNorm_map_algEquiv [IsDomain B₂] [IsIntegrallyClosed B₂] [Module.Finite A B₂]
    [NoZeroSMulDivisors A B₂] (x : B) (σ : B ≃ₐ[A] B₂) :
    Algebra.intNorm A B₂ (σ x) = Algebra.intNorm A B x := by
  apply FaithfulSMul.algebraMap_injective A (FractionRing A)
  rw [algebraMap_intNorm_fractionRing, algebraMap_intNorm_fractionRing,
    ← galLiftEquiv_algebraMap_apply (FractionRing A) (FractionRing B), norm_eq_of_algEquiv]

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

variable [IsDomain A] [IsIntegrallyClosed A] [IsDomain B] [IsIntegrallyClosed B]
  [Module.Finite A B] [NoZeroSMulDivisors A B]

lemma Algebra.algebraMap_intNorm_of_isGalois [IsGalois (FractionRing A) (FractionRing B)] {x : B} :
    algebraMap A B (Algebra.intNorm A B x) = ∏ σ : B ≃ₐ[A] B, σ x := by
  haveI : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  haveI : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  rw [← (galRestrict A (FractionRing A) (FractionRing B) B).toEquiv.prod_comp]
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  convert (prod_galRestrict_eq_norm A (FractionRing A) (FractionRing B) B x).symm

theorem Algebra.dvd_algebraMap_intNorm_self [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    (x : B) : x ∣ algebraMap A B (intNorm A B x) := by
  classical
  by_cases hx : x = 0
  · exact ⟨1, by simp [hx]⟩
  let K := FractionRing A
  let L := FractionRing B
  let E := AlgebraicClosure L
  suffices IsIntegral A ((algebraMap B L x)⁻¹ * (algebraMap A L (intNorm A B x))) by
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp <|
      _root_.IsIntegral.tower_top (A := B) this
    refine ⟨y, ?_⟩
    apply FaithfulSMul.algebraMap_injective B L
    rw [← IsScalarTower.algebraMap_apply, map_mul, hy, mul_inv_cancel_left₀]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective B L)).mpr hx
  rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom A L E)
    (FaithfulSMul.algebraMap_injective L E), IsScalarTower.coe_toAlgHom', map_mul, map_inv₀,
    IsScalarTower.algebraMap_apply A K L, algebraMap_intNorm (L := L),
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, norm_eq_prod_embeddings,
    ← Finset.univ.mul_prod_erase _ (Finset.mem_univ (IsScalarTower.toAlgHom K L E)),
    IsScalarTower.coe_toAlgHom', ← IsScalarTower.algebraMap_apply, inv_mul_cancel_left₀]
  · refine _root_.IsIntegral.prod _ fun σ _ ↦ ?_
    change IsIntegral A ((σ.restrictScalars A) (IsScalarTower.toAlgHom A B L x))
    rw [isIntegral_algHom_iff _ (RingHom.injective _),
      isIntegral_algHom_iff _ (FaithfulSMul.algebraMap_injective B L)]
    exact IsIntegral.isIntegral x
  · have := NoZeroSMulDivisors.trans_faithfulSMul B L E
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective B E)).mpr hx
