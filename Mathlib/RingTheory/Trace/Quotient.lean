/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Riccardo Brasca
-/
module

public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!

We gather results about the relations between the trace map on `B → A` and the trace map on
quotients and localizations.

## Main Results

* `Algebra.trace_quotient_eq_of_isDedekindDomain` : The trace map on `B → A` coincides with the
  trace map on `B⧸pB → A⧸p`.

-/

public section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

open IsLocalRing FiniteDimensional Module Submodule IsLocalization.AtPrime

section IsLocalRing

local notation "p" => maximalIdeal R
local notation "pS" => Ideal.map (algebraMap R S) p

variable [Module.Free R S] [Module.Finite R S]

attribute [local instance] Ideal.Quotient.field

lemma Algebra.trace_quotient_mk [IsLocalRing R] (x : S) :
    Algebra.trace (R ⧸ p) (S ⧸ pS) (Ideal.Quotient.mk pS x) =
      Ideal.Quotient.mk p (Algebra.trace R S x) := by
  classical
  let ι := Module.Free.ChooseBasisIndex R S
  let b : Module.Basis ι R S := Module.Free.chooseBasis R S
  rw [trace_eq_matrix_trace b, trace_eq_matrix_trace (basisQuotient b), AddMonoidHom.map_trace]
  congr 1
  ext i j
  simp only [leftMulMatrix_apply, coe_lmul_eq_mul, LinearMap.toMatrix_apply,
    basisQuotient_apply, LinearMap.mul_apply', Matrix.map_apply, ← map_mul,
    basisQuotient_repr]

end IsLocalRing

section IsDedekindDomain

variable (p : Ideal R) [p.IsMaximal]
variable (Rₚ Sₚ : Type*) [CommRing Rₚ] [CommRing Sₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
variable [IsLocalRing Rₚ] [Algebra S Sₚ] [Algebra R Sₚ] [Algebra Rₚ Sₚ]
variable [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ]
variable [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ]

attribute [local instance] Ideal.Quotient.field

local notation "pS" => Ideal.map (algebraMap R S) p
local notation "pSₚ" => Ideal.map (algebraMap Rₚ Sₚ) (maximalIdeal Rₚ)

variable (S)

lemma trace_quotient_eq_trace_localization_quotient (x) :
    Algebra.trace (R ⧸ p) (S ⧸ pS) (Ideal.Quotient.mk pS x) =
      (equivQuotMaximalIdeal p Rₚ).symm
        (Algebra.trace (Rₚ ⧸ maximalIdeal Rₚ) (Sₚ ⧸ pSₚ) (algebraMap S _ x)) := by
  have : IsScalarTower R (Rₚ ⧸ maximalIdeal Rₚ) (Sₚ ⧸ pSₚ) := by
    apply IsScalarTower.of_algebraMap_eq'
    rw [IsScalarTower.algebraMap_eq R Rₚ (Rₚ ⧸ _), IsScalarTower.algebraMap_eq R Rₚ (Sₚ ⧸ _),
      ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq Rₚ]
  rw [Algebra.trace_eq_of_equiv_equiv (equivQuotMaximalIdeal p Rₚ)
    (equivQuotientMapMaximalIdeal S p Rₚ Sₚ)]
  · congr
  · ext x
    simp only [equivQuotMaximalIdeal, RingHom.quotientKerEquivOfSurjective,
      RingEquiv.coe_ringHom_trans, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
      Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfRightInverse.apply, RingHom.kerLift_mk,
      equivQuotientMapMaximalIdeal, Ideal.Quotient.algebraMap_quotient_map_quotient]
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

open nonZeroDivisors in
/-- The trace map on `B → A` coincides with the trace map on `B⧸pB → A⧸p`. -/
lemma Algebra.trace_quotient_eq_of_isDedekindDomain (x) [IsDedekindDomain R] [IsDomain S]
    [Module.IsTorsionFree R S] [Module.Finite R S] [IsIntegrallyClosed S] :
    Algebra.trace (R ⧸ p) (S ⧸ pS) (Ideal.Quotient.mk pS x) =
      Ideal.Quotient.mk p (Algebra.intTrace R S x) := by
  let Rₚ := Localization.AtPrime p
  let Sₚ := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  letI : Algebra Rₚ Sₚ := localizationAlgebra p.primeCompl S
  haveI : IsScalarTower R Rₚ Sₚ := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq])
  haveI : IsLocalization (Submonoid.map (algebraMap R S) (Ideal.primeCompl p)) Sₚ :=
    inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ)
  have e : Algebra.algebraMapSubmonoid S p.primeCompl ≤ S⁰ :=
    Submonoid.map_le_of_le_comap _ <| p.primeCompl_le_nonZeroDivisors.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective _ _))
  haveI : IsDomain Sₚ := IsLocalization.isDomain_of_le_nonZeroDivisors _ e
  haveI : IsTorsionFree Rₚ Sₚ := by
    rw [isTorsionFree_iff_algebraMap_injective, RingHom.injective_iff_ker_eq_bot,
      RingHom.ker_eq_bot_iff_eq_zero]
    simp
  haveI : Module.Finite Rₚ Sₚ := .of_isLocalization R S p.primeCompl
  haveI : IsIntegrallyClosed Sₚ := isIntegrallyClosed_of_isLocalization _ _ e
  have : IsPrincipalIdealRing Rₚ := by
    by_cases hp : p = ⊥
    · infer_instance
    · have := (IsDedekindDomain.isDedekindDomainDvr R).2 p hp inferInstance
      infer_instance
  haveI : Module.Free Rₚ Sₚ := Module.free_of_finite_type_torsion_free'
  apply (equivQuotMaximalIdeal p Rₚ).injective
  rw [trace_quotient_eq_trace_localization_quotient S p Rₚ Sₚ, IsScalarTower.algebraMap_eq S Sₚ,
    RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, Algebra.trace_quotient_mk,
    RingEquiv.apply_symm_apply, ← Algebra.intTrace_eq_trace,
    ← Algebra.intTrace_eq_of_isLocalization R S p.primeCompl (Aₘ := Rₚ) (Bₘ := Sₚ) x,
    ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  simp only [equivQuotMaximalIdeal, RingHom.quotientKerEquivOfSurjective, RingEquiv.coe_trans,
    Function.comp_apply, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfRightInverse.apply,
    RingHom.kerLift_mk]

end IsDedekindDomain
