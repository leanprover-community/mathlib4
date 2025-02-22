/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu, Jujian Zhang
-/
import Mathlib.Algebra.Field.Equiv
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Algebra.Module.Torsion
import Mathlib.RingTheory.Noetherian.Basic

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

The predicate `IsArtinianRing` is defined in `Mathlib.RingTheory.Artinian.Ring` instead, so that we
can apply basic API on artinian modules to division rings without a heavy import.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [samuel]

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

lemma jacobson_eq_nilradical : (⊥ : Ideal R).jacobson = nilradical R :=
    jacobson_eq_radical _

theorem isNilpotent_nilradical : IsNilpotent (nilradical R) := by
  rw [nilradical, ← jacobson_eq_radical]
  exact isNilpotent_jacobson_bot

variable (R) in
/-- Commutative artinian reduced local ring is a field. -/
theorem isField_of_isReduced_of_isLocalRing [IsReduced R] [IsLocalRing R] : IsField R :=
  (IsArtinianRing.equivPi R).trans (RingEquiv.piUnique _) |>.toMulEquiv.isField
    _ (Ideal.Quotient.field _).toIsField

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
  -- TODO: can `rsuffices` be used to move the `exact` below before the proof of this `obtain`?
  obtain ⟨r₂, h⟩ : ∃ r : R, IsLocalization.mk' L 1 s = algebraMap R L r := by
    obtain ⟨n, r, hr⟩ := IsArtinian.exists_pow_succ_smul_dvd (s : R) (1 : R)
    use r
    rw [smul_eq_mul, smul_eq_mul, pow_succ, mul_assoc] at hr
    apply_fun algebraMap R L at hr
    simp only [map_mul] at hr
    rw [← IsLocalization.mk'_one (M := S) L, IsLocalization.mk'_eq_iff_eq, mul_one,
      Submonoid.coe_one, ← (IsLocalization.map_units L (s ^ n)).mul_left_cancel hr, map_mul]
  exact ⟨r₁ * r₂, by rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul, h]⟩

theorem localization_artinian : IsArtinianRing L :=
  (localization_surjective S L).isArtinianRing

/-- `IsArtinianRing.localization_artinian` can't be made an instance, as it would make `S` + `R`
into metavariables. However, this is safe. -/
instance : IsArtinianRing (Localization S) :=
  localization_artinian S _

end Localization

section temp


lemma is_noetherian_of_tower_of_surjective {R S : Type} (M : Type)
    [CommSemiring R] [Semiring S]
    [AddCommMonoid M] [Algebra R S] [Module S M] [Module R M] [IsScalarTower R S M]
    (h : Function.Surjective (algebraMap R S)) :
    IsNoetherian R M ↔ IsNoetherian S M := by

  sorry

lemma isNoetherianOfTowerOfSurjective {R S : Type*} (M : Type*) [CommSemiring R] [Semiring S]
  [AddCommMonoid M] [Algebra R S] [Module S M] [Module R M] [IsScalarTower R S M]
  (h : Function.Surjective (algebraMap R S)) :
  IsNoetherian R M ↔ IsNoetherian S M := by
  refine ⟨isNoetherian_of_tower R, ?_⟩
  simp_rw [isNoetherian_iff]
  sorry

lemma isArtinianOfTowerOfSurjective {R S : Type*} (M : Type*) [CommRing R] [CommRing S]
  [AddCommGroup M] [Algebra R S] [Module S M] [Module R M] [IsScalarTower R S M]
  (h : Function.Surjective (algebraMap R S)) :
  IsArtinian R M ↔ IsArtinian S M := by

  sorry

lemma isArtinianTopIff {R M : Type*} [Semiring R] [AddCommGroup M] [Module R M] :
  IsArtinian R (⊤ : Submodule R M) ↔ IsArtinian R M := by
  constructor
  · intro h

    sorry
  · intro h

    sorry

lemma isNoetherianIffIsArtinianOfMul {R : Type*} [CommRing R] (I J : Ideal R) [I.IsMaximal]
  (H : IsNoetherian R (I * J : Submodule R R) ↔ IsArtinian R (I * J : Submodule R R)) :
  IsNoetherian R J ↔ IsArtinian R J := by
  let IJ := Submodule.comap J.subtype (I * J)
  have : Module.IsTorsionBySet R (J ⧸ IJ) I := by
    intro x ⟨y, hy⟩
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.mkQ_surjective IJ x
    rw [Subtype.coe_mk, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    show _ ∈ I * J
    simp [Ideal.mul_mem_mul hy hx]
  letI : Module (R ⧸ I) (J ⧸ IJ) := this.module
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  have : Function.Surjective (algebraMap R (R ⧸ I)) := Ideal.Quotient.mk_surjective
  have : IsNoetherian R (J ⧸ IJ) ↔ IsArtinian R (J ⧸ IJ) := by
    -- rw [isNoetherianOfTowerOfSurjective (J ⧸ IJ) this,
    --     (Module.finiteLengthTfaeOfField (R ⧸ I) (J ⧸ IJ)).out 1 2,
    --     ← isArtinianOfTowerOfSurjective (J ⧸ IJ) this]
    sorry
  constructor
  · intro hNoetherianJ
    haveI := this.mp inferInstance
    haveI : IsArtinian R (I * J : Submodule R R) := H.mp (isNoetherian_of_le Ideal.mul_le_left)
    -- apply isArtinian_of_range_eq_ker
      -- (Submodule.ofLe Ideal.mul_le_left : (I * J : Submodule R R) →ₗ[R] J) IJ.mkQ
      -- (Submodule.ofLe_injective Ideal.mul_le_left)
      -- (Submodule.mkQ_surjective IJ)
      -- (by simp [Submodule.range_ofLe])
    sorry
  · intro hArtinianJ
    haveI := this.mpr inferInstance
    haveI : IsNoetherian R (I * J : Submodule R R) := H.mpr (isArtinian_of_le Ideal.mul_le_left)
    -- exact isNoetherianOfRangeEqKer
    --   (Submodule.ofLe Ideal.mul_le_left : (I * J : Submodule R R) →ₗ[R] J) IJ.mkQ
    --   (Submodule.ofLe_injective Ideal.mul_le_left)
    --   (Submodule.mkQ_surjective IJ)
    --   (by simp [Submodule.range_ofLe])
    sorry

lemma isNoetherianIffIsArtinianOfProdEqBot {R : Type*} [CommRing R] (s : Multiset (Ideal R))
  (hs : ∀ I ∈ s, Ideal.IsMaximal I) (h' : Multiset.prod s = ⊥) :
  IsNoetherianRing R ↔ IsArtinianRing R := by
  rw [isNoetherianRing_iff, ← isNoetherian_top_iff, isArtinianRing_iff, ← isArtinianTopIff]
  by_contra h
  suffices ¬(IsNoetherian R (⊥ : Ideal R) ↔ IsArtinian R (⊥ : Ideal R)) by
    apply this
    exact ⟨fun _ => inferInstance, fun _ => inferInstance⟩
  rw [← h']
  clear h'
  induction s using Multiset.induction with
  | empty =>
    rw [Multiset.prod_zero, Ideal.one_eq_top]
    exact h
  | cons a s hs' =>
    rw [Multiset.prod_cons]
    intro hs''
    apply hs' (fun I hMem => hs I (Multiset.mem_cons_of_mem hMem))
    haveI := hs a (Multiset.mem_cons_self a s)
    apply isNoetherianIffIsArtinianOfMul _ _ hs''

end temp

end IsArtinianRing
