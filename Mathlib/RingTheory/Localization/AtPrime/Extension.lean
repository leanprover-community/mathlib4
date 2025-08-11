/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.RingTheory.RingHom.Finite

/-!
# Localization at prime in an extension

Let `R ⊆ S` be an extension of rings and `p` be a prime ideal of `R`. Denote by `Rₚ` the
localization of `R` at the complement of `p` and by `Sₚ` the localization of `S` at the (image)
of the complement of `p`.

In this file, we prove results about the extension `Rₚ ⊆ Sₚ`. We also prove results about the
tower of extensions `Rₚ ⊆ Sₚ ⊆ Tₚ` where `Tₚ` is the localization of `T` at the (image) of the
complement of `p` for a ring `T` such that `S ⊆ T`.

-/

open Ideal Algebra IsLocalRing

variable {R S T : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (p : Ideal R) [p.IsPrime]

section misc

variable [IsDomain R] [IsDomain S] [FaithfulSMul R S]

namespace IsLocalization.AtPrime

variable (Rₚ Sₚ : Type*) [CommRing Rₚ] [CommRing Sₚ] [Algebra R Rₚ] [Algebra S Sₚ] [Algebra Rₚ Sₚ]
variable [IsLocalization.AtPrime Rₚ p] [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ]

variable (S) in
theorem algebraMapSubmonoid_primeCompl_le_nonZeroDivisors :
    algebraMapSubmonoid S p.primeCompl ≤ nonZeroDivisors S := by
  apply algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul
  refine fun _ h ↦  mem_nonZeroDivisors_of_ne_zero <| not_zero_of_mem_primeCompl h

include S p

theorem noZeroSMulDivisors_isLocalization' :
    NoZeroSMulDivisors S Sₚ := by
  have : IsDomain Sₚ :=
    isDomain_of_le_nonZeroDivisors _ (algebraMapSubmonoid_primeCompl_le_nonZeroDivisors S p)
  rw [NoZeroSMulDivisors.iff_algebraMap_injective,
    injective_iff_isRegular (algebraMapSubmonoid S p.primeCompl)]
  exact fun ⟨x, hx⟩ ↦ isRegular_iff_ne_zero'.mpr <|
    ne_of_mem_of_not_mem hx <| by simp [Algebra.algebraMapSubmonoid]

variable (S) [Algebra R Sₚ] [IsScalarTower R Rₚ Sₚ] [IsScalarTower R S Sₚ]

include Rₚ

theorem noZeroSMulDivisors_isLocalization_isLocalization :
    NoZeroSMulDivisors Rₚ Sₚ :=
  NoZeroSMulDivisors_of_isLocalization R S Rₚ Sₚ (primeCompl_le_nonZeroDivisors p)

theorem noZeroSMulDivisors_isLocalization :
    NoZeroSMulDivisors R Sₚ := by
  have := faithfulSMul Rₚ R p
  have := noZeroSMulDivisors_isLocalization_isLocalization S p Rₚ Sₚ
  exact NoZeroSMulDivisors.trans_faithfulSMul R Rₚ _

end IsLocalization.AtPrime

namespace Localization.AtPrime

local notation "Rₚ" => Localization.AtPrime p
local notation "Sₚ" => Localization (algebraMapSubmonoid S p.primeCompl)

instance : NoZeroSMulDivisors R Sₚ :=
  IsLocalization.AtPrime.noZeroSMulDivisors_isLocalization S p Rₚ _

instance : NoZeroSMulDivisors S Sₚ := IsLocalization.AtPrime.noZeroSMulDivisors_isLocalization' p _

instance : NoZeroSMulDivisors Rₚ Sₚ :=
  IsLocalization.AtPrime.noZeroSMulDivisors_isLocalization_isLocalization S p _ _

instance [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S] [NeZero p] :
    IsPrincipalIdealRing Sₚ :=
  IsDedekindDomain.isPrincipalIdealRing_localization_over_prime S p (NeZero.ne p)

end Localization.AtPrime

end misc

noncomputable section tower

variable [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

namespace IsLocalization.AtPrime

variable (Rₚ Sₚ Tₚ : Type*) [CommRing Rₚ] [CommRing Sₚ] [CommRing Tₚ] [Algebra R Rₚ] [Algebra S Sₚ]
  [Algebra Rₚ Sₚ] [Algebra T Tₚ] [Algebra Rₚ Tₚ] [Algebra Sₚ Tₚ]
variable [IsLocalization.AtPrime Rₚ p] [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ]
variable [IsLocalization (algebraMapSubmonoid T p.primeCompl) Tₚ]

variable (S T)

theorem isLocalization_map_map :
    IsLocalization (algebraMapSubmonoid T (algebraMapSubmonoid S p.primeCompl)) Tₚ := by
  rwa [show algebraMapSubmonoid T (algebraMapSubmonoid S p.primeCompl) =
      (algebraMapSubmonoid T p.primeCompl) by simp]

variable [Algebra S Tₚ] [IsScalarTower S T Tₚ] [IsScalarTower S Sₚ Tₚ]

include p in
theorem noZeroSMulDivisors_isLocalization_isLocalization' [IsDomain R] [IsDomain S] [IsDomain T]
    [NoZeroSMulDivisors R S] [NoZeroSMulDivisors S T] : NoZeroSMulDivisors Sₚ Tₚ := by
  have := isLocalization_map_map S T p Tₚ
  refine NoZeroSMulDivisors_of_isLocalization S T Sₚ Tₚ <|
     algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ (primeCompl_le_nonZeroDivisors p)

end IsLocalization.AtPrime

namespace Localization.AtPrime

open IsLocalization.AtPrime

local notation "Rₚ" => Localization.AtPrime p
local notation "Sₚ" => Localization (algebraMapSubmonoid S p.primeCompl)
local notation "Tₚ" => Localization (algebraMapSubmonoid T p.primeCompl)

/--
Let `R ⊆ S ⊆ T` be a tower of rings. Let `Sₚ` and `Tₚ` denote the localizations of `S` and `T` at
the prime ideal `p` of `R`. Then `Tₚ` is a `Sₚ`-algebra.
This cannot be an instance since it creates a diamond when `S = T`.
-/
def algebra_localization_localization : Algebra Sₚ Tₚ := by
  have := isLocalization_map_map S T p Tₚ
  exact localizationAlgebra (algebraMapSubmonoid S p.primeCompl) T

attribute [local instance] algebra_localization_localization

instance : IsScalarTower S Sₚ Tₚ := by
  have := isLocalization_map_map S T p
  refine IsScalarTower.of_algebraMap_eq' ?_
  rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq]

instance : IsScalarTower R Sₚ Tₚ := by
  refine IsScalarTower.of_algebraMap_eq' ?_
  rw [IsScalarTower.algebraMap_eq R S Sₚ, ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq S,
    ← IsScalarTower.algebraMap_eq]

instance [Module.Finite S T] : Module.Finite Sₚ Tₚ := by
  have := isLocalization_map_map S T p Tₚ
  exact Module.Finite.of_isLocalization S T (Algebra.algebraMapSubmonoid S p.primeCompl)

variable [IsDomain R] [IsDomain T]

instance [IsDomain S] [NoZeroSMulDivisors R S] [NoZeroSMulDivisors S T] :
    NoZeroSMulDivisors Sₚ Tₚ :=
  noZeroSMulDivisors_isLocalization_isLocalization' S T p _ _

variable [NoZeroSMulDivisors R T]

instance : IsScalarTower Rₚ Sₚ Tₚ := by
  refine ⟨fun a b c ↦ a.ind fun ⟨a₁, a₂⟩ ↦ ?_⟩
  have : a₂.val ≠ 0 := nonZeroDivisors.ne_zero <| primeCompl_le_nonZeroDivisors p <| a₂.prop
  rw [← smul_right_inj this, ← smul_assoc (M := R) (N := Sₚ), ← smul_assoc (M := R) (α := Sₚ),
    ← smul_assoc (M := R) (α := Tₚ), Localization.smul_mk, smul_eq_mul, Localization.mk_eq_mk',
    IsLocalization.mk'_mul_cancel_left, algebraMap_smul, algebraMap_smul, smul_assoc]

attribute [local instance] FractionRing.liftAlgebra

instance [IsDomain S] [NoZeroSMulDivisors R S] [NoZeroSMulDivisors S T]
    [Algebra.IsSeparable (FractionRing S) (FractionRing T)] :
    Algebra.IsSeparable (FractionRing Sₚ) (FractionRing Tₚ) := by
  have := isLocalization_map_map S T p Tₚ
  exact FractionRing.isSeparable_of_isLocalization T _ _ <|
    algebraMapSubmonoid_primeCompl_le_nonZeroDivisors S p

end Localization.AtPrime

end tower
