/-
Copyright (c) 2025 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.FieldTheory.Separable

/-!
# Instances for Dedekind domains
This file contains various instances to work with localization of a ring extension.

A very common situation in number theory is to have an extension of (say) Dedekind domains `R` and
`S`, and to prove a property of this extension it is useful to consider the localization `Rₚ` of `R`
at `P`, a prime ideal of `R`. One also works with the corresponding localization `Sₚ` of `S` and the
fraction fields `K` and `L` of `R` and `S`. In this situation there are many compatible algebra
structures and various properties of the rings involved. This file contains a collection of such
instances.

## Implementation details
In general one wants all the results below for any algebra satisfying `IsLocalization`, but those
cannot be instances (since Lean has no way of guessing the submonoid). Having the instances in the
special case of *the* localization at a prime ideal is useful in working with Dedekind domains.

-/

open nonZeroDivisors IsLocalization Algebra IsFractionRing IsScalarTower

attribute [local instance] FractionRing.liftAlgebra

variable {R : Type*} (S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [Algebra R S]

local notation3 "K" => FractionRing R
local notation3 "L" => FractionRing S
section

theorem algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul {A : Type*} (B : Type*)
    [CommSemiring A] [CommSemiring B] [Algebra A B] [NoZeroDivisors B] [FaithfulSMul A B]
    {S : Submonoid A} (hS : S ≤ A⁰) : algebraMapSubmonoid B S ≤ B⁰ :=
  map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective A B) hS

variable (Rₘ Sₘ : Type*) [CommRing Rₘ] [CommRing Sₘ] [Algebra R Rₘ] [NoZeroSMulDivisors R S]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)] {M : Submonoid R} [IsLocalization M Rₘ]
    [Algebra Rₘ Sₘ] [Algebra S Sₘ] [Algebra R Sₘ] [IsScalarTower R Rₘ Sₘ]
    [IsScalarTower R S Sₘ] [IsLocalization (algebraMapSubmonoid S M) Sₘ]
    [Algebra (FractionRing Rₘ) (FractionRing Sₘ)]
    [IsScalarTower Rₘ (FractionRing Rₘ) (FractionRing Sₘ)]

include R S in
theorem FractionRing.isSeparable_of_isLocalization (hM : M ≤ R⁰) :
    Algebra.IsSeparable (FractionRing Rₘ) (FractionRing Sₘ) := by
  let M' := algebraMapSubmonoid S M
  have hM' : algebraMapSubmonoid S M ≤ S⁰ := algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul
    _ hM
  let f₁ : Rₘ →+* K := map _ (T := R⁰) (RingHom.id R) hM
  let f₂ : Sₘ →+* L := map _ (T := S⁰) (RingHom.id S) hM'
  algebraize [f₁, f₂]
  have := localization_isScalarTower_of_submonoid_le Rₘ K _ _ hM
  have := localization_isScalarTower_of_submonoid_le Sₘ L _ _ hM'
  have := isFractionRing_of_isDomain_of_isLocalization M Rₘ K
  have := isFractionRing_of_isDomain_of_isLocalization M' Sₘ L
  have : IsDomain Rₘ := isDomain_of_le_nonZeroDivisors _ hM
  apply Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv Rₘ K).symm.toRingEquiv
    (FractionRing.algEquiv Sₘ L).symm.toRingEquiv
  apply ringHom_ext R⁰
  ext
  simp only [AlgEquiv.toRingEquiv_eq_coe, RingHom.coe_comp,
      RingHom.coe_coe, Function.comp_apply, ← algebraMap_apply]
  rw [algebraMap_apply R Rₘ (FractionRing R), AlgEquiv.coe_ringEquiv, AlgEquiv.commutes,
    algebraMap_apply R S L, algebraMap_apply S Sₘ L, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
  simp only [← algebraMap_apply]
  rw [algebraMap_apply R Rₘ (FractionRing Rₘ), ← algebraMap_apply Rₘ, ← algebraMap_apply]

end

variable {P : Ideal R} [P.IsPrime]

local notation3 "P'" => algebraMapSubmonoid S P.primeCompl
local notation3 "Rₚ" => Localization.AtPrime P
local notation3 "Sₚ" => Localization P'

variable [FaithfulSMul R S]

noncomputable instance : Algebra Sₚ L :=
  (map _ (T := S⁰) (RingHom.id S)
    (algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _
      P.primeCompl_le_nonZeroDivisors)).toAlgebra

instance : IsScalarTower S Sₚ L :=
  localization_isScalarTower_of_submonoid_le _ _ _ _
    (algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _
      P.primeCompl_le_nonZeroDivisors)

instance : IsFractionRing Rₚ K :=
  isFractionRing_of_isDomain_of_isLocalization P.primeCompl _ _

instance : IsFractionRing Sₚ L :=
  isFractionRing_of_isDomain_of_isLocalization P' _ _

noncomputable instance : Algebra Rₚ L :=
  (lift (M := P.primeCompl) (g := algebraMap R L) <|
    fun ⟨x, hx⟩ ↦ by simpa using fun h ↦ hx <| by simp [h]).toAlgebra

-- Make sure there are no diamonds in the case `R = S`.
example : instAlgebraLocalizationAtPrime P = instAlgebraAtPrimeFractionRing (S := R) := by
  with_reducible_and_instances rfl

instance : IsScalarTower Rₚ K L :=
  of_algebraMap_eq' (ringHom_ext P.primeCompl
    (RingHom.ext fun x ↦ by simp [RingHom.algebraMap_toAlgebra]))

instance : IsScalarTower R Rₚ K :=
  of_algebraMap_eq' (RingHom.ext fun x ↦ by simp [RingHom.algebraMap_toAlgebra])

instance : IsScalarTower Rₚ Sₚ L := by
  refine IsScalarTower.of_algebraMap_eq' <| IsLocalization.ringHom_ext P.primeCompl ?_
  rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq R Rₚ Sₚ, IsScalarTower.algebraMap_eq R S Sₚ,
    ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq S Sₚ L, IsScalarTower.algebraMap_eq Rₚ K L,
    RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq,
    ← IsScalarTower.algebraMap_eq]

instance [IsDedekindDomain S] : IsDedekindDomain Sₚ :=
  isDedekindDomain S
    (algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ P.primeCompl_le_nonZeroDivisors) _

instance [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S] [hP : NeZero P] :
    IsPrincipalIdealRing Sₚ :=
  IsDedekindDomain.isPrincipalIdealRing_localization_over_prime S P (fun h ↦ hP.1 h)

instance [Algebra.IsSeparable K L] :
    -- Without the following line there is a timeout
    letI : Algebra Rₚ (FractionRing Sₚ) := OreLocalization.instAlgebra
    Algebra.IsSeparable (FractionRing Rₚ) (FractionRing Sₚ) :=
  let _ : Algebra Rₚ (FractionRing Sₚ) := OreLocalization.instAlgebra
  FractionRing.isSeparable_of_isLocalization S _ _ P.primeCompl_le_nonZeroDivisors
