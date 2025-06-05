/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu, Jujian Zhang
-/
import Mathlib.Algebra.Field.Equiv
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Artinian rings

A ring is said to be left (or right) Artinian if it is Artinian as a left (or right) module over
itself, or simply Artinian if it is both left and right Artinian.

## Main definitions

* `IsArtinianRing R` is the proposition that `R` is a left Artinian ring.

## Main results

* `IsArtinianRing.localization_surjective`: the canonical homomorphism from a commutative artinian
  ring to any localization of itself is surjective.

* `IsArtinianRing.isNilpotent_jacobson_bot`: the Jacobson radical of a commutative artinian ring
  is a nilpotent ideal.

## Implementation Details

The predicate `IsArtinianRing` is defined in `Mathlib/RingTheory/Artinian/Ring.lean` instead,
so that we can apply basic API on artinian modules to division rings without a heavy import.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]

## Tags

Artinian, artinian, Artinian ring, artinian ring

-/

open Set Submodule IsArtinian

namespace IsArtinianRing

@[stacks 00J8]
theorem isNilpotent_jacobson_bot {R} [Ring R] [IsArtinianRing R] :
    IsNilpotent (Ideal.jacobson (⊥ : Ideal R)) :=
  Ideal.jacobson_bot (R := R) ▸ IsSemiprimaryRing.isNilpotent

variable {R : Type*} [CommRing R] [IsArtinianRing R]

lemma jacobson_eq_radical (I : Ideal R) : I.jacobson = I.radical := by
  simp_rw [Ideal.jacobson, Ideal.radical_eq_sInf, IsArtinianRing.isPrime_iff_isMaximal]

theorem isNilpotent_nilradical : IsNilpotent (nilradical R) := by
  rw [nilradical, ← jacobson_eq_radical]
  exact isNilpotent_jacobson_bot

variable (R) in
/-- Commutative artinian reduced local ring is a field. -/
theorem isField_of_isReduced_of_isLocalRing [IsReduced R] [IsLocalRing R] : IsField R :=
  (IsArtinianRing.equivPi R).trans (RingEquiv.piUnique _) |>.toMulEquiv.isField
    (Ideal.Quotient.field _).toIsField

section IsUnit

open nonZeroDivisors

/-- If an element of an artinian ring is not a zero divisor then it is a unit. -/
theorem isUnit_of_mem_nonZeroDivisors {a : R} (ha : a ∈ R⁰) : IsUnit a :=
  IsUnit.isUnit_iff_mulLeft_bijective.mpr <|
    IsArtinian.bijective_of_injective_endomorphism (LinearMap.mulLeft R a)
      fun _ _ ↦ (mul_cancel_left_mem_nonZeroDivisors ha).mp

/-- In an artinian ring, an element is a unit iff it is a non-zero-divisor.
See also `isUnit_iff_mem_nonZeroDivisors_of_finite`. -/
theorem isUnit_iff_mem_nonZeroDivisors {a : R} : IsUnit a ↔ a ∈ R⁰ :=
  ⟨IsUnit.mem_nonZeroDivisors, isUnit_of_mem_nonZeroDivisors⟩

theorem isUnit_submonoid_eq : IsUnit.submonoid R = R⁰ := by
  ext; simp [IsUnit.mem_submonoid_iff, isUnit_iff_mem_nonZeroDivisors]

end IsUnit

section Localization

variable (S : Submonoid R) (L : Type*) [CommSemiring L] [Algebra R L] [IsLocalization S L]
include S

/-- Localizing an artinian ring can only reduce the amount of elements. -/
theorem localization_surjective : Function.Surjective (algebraMap R L) := by
  intro r'
  obtain ⟨r₁, s, rfl⟩ := IsLocalization.mk'_surjective S r'
  rsuffices ⟨r₂, h⟩ : ∃ r : R, IsLocalization.mk' L 1 s = algebraMap R L r
  · exact ⟨r₁ * r₂, by rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul, h]⟩
  obtain ⟨n, r, hr⟩ := IsArtinian.exists_pow_succ_smul_dvd (s : R) (1 : R)
  use r
  rw [smul_eq_mul, smul_eq_mul, pow_succ, mul_assoc] at hr
  apply_fun algebraMap R L at hr
  simp only [map_mul] at hr
  rw [← IsLocalization.mk'_one (M := S) L, IsLocalization.mk'_eq_iff_eq, mul_one,
    Submonoid.coe_one, ← (IsLocalization.map_units L (s ^ n)).mul_left_cancel hr, map_mul]

theorem localization_artinian : IsArtinianRing L :=
  (localization_surjective S L).isArtinianRing

/-- `IsArtinianRing.localization_artinian` can't be made an instance, as it would make `S` + `R`
into metavariables. However, this is safe. -/
instance : IsArtinianRing (Localization S) :=
  localization_artinian S _

end Localization

end IsArtinianRing
