/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Riccardo Brasca
-/
module

import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.LocalRing.Quotient

/-!

We gather results about the relations between the trace map on `B → A` and the trace map on
quotients and localizations.

## Main Results

* `Algebra.trace_quotient_eq_of_isDedekindDomain` : The trace map on `B → A` coincides with the
  trace map on `B⧸pB → A⧸p`.

-/

public section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

open IsLocalRing Module Submodule IsLocalization.AtPrime

instance QuotientMapQuotient.projective (I : Ideal R) [Module.Projective R S] :
    Module.Projective (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
  Module.Projective.of_equiv'
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).symm.toLinearEquiv

lemma Algebra.trace_quotient_mk [Module.Projective R S] [Module.Finite R S]
    (I : Ideal R) (x : S) :
    Algebra.trace (R ⧸ I) (S ⧸ I.map (algebraMap R S)) (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk I (Algebra.trace R S x) := by
  rw [← Algebra.trace_eq_of_algEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I),
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk, Algebra.trace_apply,
    ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
  rfl

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

lemma trace_quotient_eq_trace_localization_quotient [Module.Finite (R ⧸ p) (S ⧸ pS)]
    [Module.Finite (Rₚ ⧸ maximalIdeal Rₚ) (Sₚ ⧸ pSₚ)] (x) :
    Algebra.trace (R ⧸ p) (S ⧸ pS) (Ideal.Quotient.mk pS x) =
      (equivQuotMaximalIdeal p Rₚ).symm
        (Algebra.trace (Rₚ ⧸ maximalIdeal Rₚ) (Sₚ ⧸ pSₚ) (algebraMap S _ x)) := by
  have : IsScalarTower R (Rₚ ⧸ maximalIdeal Rₚ) (Sₚ ⧸ pSₚ) := by
    apply IsScalarTower.of_algebraMap_eq'
    rw [IsScalarTower.algebraMap_eq R Rₚ (Rₚ ⧸ _), IsScalarTower.algebraMap_eq R Rₚ (Sₚ ⧸ _),
      ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq Rₚ]
  rw [Algebra.trace_eq_of_equiv_equiv (equivQuotMaximalIdeal p Rₚ).toRingEquiv
    (equivQuotientMapMaximalIdeal S p Rₚ Sₚ)]
  · congr
  · ext x
    simp only [AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp, RingHom.coe_coe,
      Function.comp_apply, equivQuotMaximalIdeal_apply_mk,
      Ideal.Quotient.algebraMap_quotient_map_quotient, equivQuotientMapMaximalIdeal_apply_mk]
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      Ideal.Quotient.mk_algebraMap]

open nonZeroDivisors in
/-- The trace map on `B → A` coincides with the trace map on `B⧸pB → A⧸p`. -/
lemma Algebra.trace_quotient_eq_of_isDedekindDomain (x) [IsDedekindDomain R] [IsDomain S]
    [Module.IsTorsionFree R S] [Module.Finite R S] [IsIntegrallyClosed S] :
    Algebra.trace (R ⧸ p) (S ⧸ pS) (Ideal.Quotient.mk pS x) =
      Ideal.Quotient.mk p (Algebra.intTrace R S x) := by
  let Rₚ := Localization.AtPrime p
  let Sₚ := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  have e : Algebra.algebraMapSubmonoid S p.primeCompl ≤ S⁰ :=
    Submonoid.map_le_of_le_comap _ <| p.primeCompl_le_nonZeroDivisors.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective _ _))
  have : IsIntegrallyClosed Sₚ := isIntegrallyClosed_of_isLocalization _ _ e
  apply (equivQuotMaximalIdeal p Rₚ).injective
  rw [trace_quotient_eq_trace_localization_quotient S p Rₚ Sₚ, IsScalarTower.algebraMap_eq S Sₚ,
    RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, Algebra.trace_quotient_mk,
    ← Algebra.intTrace_eq_trace, ← Algebra.intTrace_eq_of_isLocalization R S p.primeCompl x]
  simp

end IsDedekindDomain
