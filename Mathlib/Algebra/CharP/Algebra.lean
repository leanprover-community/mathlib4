/-
Copyright (c) 2021 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster, Eric Wieser
-/
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.FreeAlgebra
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Characteristics of algebras

In this file we describe the characteristic of `R`-algebras.

In particular we are interested in the characteristic of free algebras over `R`
and the fraction field `FractionRing R`.


## Main results

- `charP_of_injective_algebraMap` If `R →+* A` is an injective algebra map
  then `A` has the same characteristic as `R`.

Instances constructed from this result:
- Any `FreeAlgebra R X` has the same characteristic as `R`.
- The `FractionRing R` of an integral domain `R` has the same characteristic as `R`.

-/

/-- Given `R →+* A`, then `char A ∣ char R`. -/
theorem CharP.dvd_of_ringHom {R A : Type*} [NonAssocSemiring R] [NonAssocSemiring A]
    (f : R →+* A) (p q : ℕ) [CharP R p] [CharP A q] : q ∣ p := by
  refine (CharP.cast_eq_zero_iff A q p).mp ?_
  rw [← map_natCast f p, CharP.cast_eq_zero, map_zero]

/-- Given `R →+* A`, where `R` is a domain with `char R > 0`, then `char A = char R`. -/
theorem CharP.of_ringHom_of_ne_zero {R A : Type*} [NonAssocSemiring R] [NoZeroDivisors R]
    [NonAssocSemiring A] [Nontrivial A]
    (f : R →+* A) (p : ℕ) (hp : p ≠ 0) [CharP R p] : CharP A p := by
  have := f.domain_nontrivial
  have H := (CharP.char_is_prime_or_zero R p).resolve_right hp
  obtain ⟨q, hq⟩ := CharP.exists A
  obtain ⟨k, e⟩ := dvd_of_ringHom f p q
  have := Nat.isUnit_iff.mp ((H.2 e).resolve_left (Nat.isUnit_iff.not.mpr (char_ne_one A q)))
  rw [this, mul_one] at e
  exact e ▸ hq

/-- If a ring homomorphism `R →+* A` is injective then `A` has the same characteristic as `R`. -/
theorem charP_of_injective_ringHom {R A : Type*} [NonAssocSemiring R] [NonAssocSemiring A]
    {f : R →+* A} (h : Function.Injective f) (p : ℕ) [CharP R p] : CharP A p where
  cast_eq_zero_iff x := by
    rw [← CharP.cast_eq_zero_iff R p x, ← map_natCast f x, map_eq_zero_iff f h]

/-- If the algebra map `R →+* A` is injective then `A` has the same characteristic as `R`. -/
theorem charP_of_injective_algebraMap {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (h : Function.Injective (algebraMap R A)) (p : ℕ) [CharP R p] : CharP A p :=
  charP_of_injective_ringHom h p

theorem charP_of_injective_algebraMap' (R : Type*) {A : Type*} [CommRing R] [Semiring A]
    [Algebra R A] [FaithfulSMul R A] (p : ℕ) [CharP R p] : CharP A p :=
  charP_of_injective_ringHom (FaithfulSMul.algebraMap_injective R A) p

/-- If a ring homomorphism `R →+* A` is injective and `R` has characteristic zero
then so does `A`. -/
theorem charZero_of_injective_ringHom {R A : Type*} [NonAssocSemiring R] [NonAssocSemiring A]
    {f : R →+* A} (h : Function.Injective f) [CharZero R] : CharZero A where
  cast_injective _ _ _ := CharZero.cast_injective <| h <| by simpa only [map_natCast f]

/-- If the algebra map `R →+* A` is injective and `R` has characteristic zero then so does `A`. -/
theorem charZero_of_injective_algebraMap {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (h : Function.Injective (algebraMap R A)) [CharZero R] : CharZero A :=
  charZero_of_injective_ringHom h

/-- If `R →+* A` is injective, and `A` is of characteristic `p`, then `R` is also of
characteristic `p`. Similar to `RingHom.charZero`. -/
theorem RingHom.charP {R A : Type*} [NonAssocSemiring R] [NonAssocSemiring A] (f : R →+* A)
    (H : Function.Injective f) (p : ℕ) [CharP A p] : CharP R p := by
  obtain ⟨q, h⟩ := CharP.exists R
  exact CharP.eq _ (charP_of_injective_ringHom H q) ‹CharP A p› ▸ h

/-- If `R →+* A` is injective, then `R` is of characteristic `p` if and only if `A` is also of
characteristic `p`. Similar to `RingHom.charZero_iff`. -/
protected theorem RingHom.charP_iff {R A : Type*} [NonAssocSemiring R] [NonAssocSemiring A]
    (f : R →+* A) (H : Function.Injective f) (p : ℕ) : CharP R p ↔ CharP A p :=
  ⟨fun _ ↦ charP_of_injective_ringHom H p, fun _ ↦ f.charP H p⟩

/-- If a ring homomorphism `R →+* A` is injective then `A` has the same exponential characteristic
as `R`. -/
lemma expChar_of_injective_ringHom {R A : Type*}
    [NonAssocSemiring R] [NonAssocSemiring A] {f : R →+* A} (h : Function.Injective f)
    (q : ℕ) [hR : ExpChar R q] : ExpChar A q := by
  rcases hR with _ | hprime
  · haveI := charZero_of_injective_ringHom h; exact .zero
  haveI := charP_of_injective_ringHom h q; exact .prime hprime

/-- If `R →+* A` is injective, and `A` is of exponential characteristic `p`, then `R` is also of
exponential characteristic `p`. Similar to `RingHom.charZero`. -/
lemma RingHom.expChar {R A : Type*} [NonAssocSemiring R] [NonAssocSemiring A] (f : R →+* A)
    (H : Function.Injective f) (p : ℕ) [ExpChar A p] : ExpChar R p := by
  cases ‹ExpChar A p› with
  | zero => haveI := f.charZero; exact .zero
  | prime hp => haveI := f.charP H p; exact .prime hp

/-- If `R →+* A` is injective, then `R` is of exponential characteristic `p` if and only if `A` is
also of exponential characteristic `p`. Similar to `RingHom.charZero_iff`. -/
lemma RingHom.expChar_iff {R A : Type*} [NonAssocSemiring R] [NonAssocSemiring A] (f : R →+* A)
    (H : Function.Injective f) (p : ℕ) : ExpChar R p ↔ ExpChar A p :=
  ⟨fun _ ↦ expChar_of_injective_ringHom H p, fun _ ↦ f.expChar H p⟩

/-- If the algebra map `R →+* A` is injective then `A` has the same exponential characteristic
as `R`. -/
lemma expChar_of_injective_algebraMap {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (h : Function.Injective (algebraMap R A)) (q : ℕ) [ExpChar R q] : ExpChar A q :=
  expChar_of_injective_ringHom h q

theorem ExpChar.of_injective_algebraMap' (R : Type*) {A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [FaithfulSMul R A] (q : ℕ) [ExpChar R q] : ExpChar A q :=
  expChar_of_injective_ringHom (FaithfulSMul.algebraMap_injective R A) q

/-!
As an application, a `ℚ`-algebra has characteristic zero.
-/


-- `CharP.charP_to_charZero A _ (charP_of_injective_algebraMap h 0)` does not work
-- here as it would require `Ring A`.
section QAlgebra

variable (R : Type*) [Nontrivial R]

/-- A nontrivial `ℚ`-algebra has `CharP` equal to zero.

This cannot be a (local) instance because it would immediately form a loop with the
instance `DivisionRing.toRatAlgebra`. It's probably easier to go the other way: prove `CharZero R`
and automatically receive an `Algebra ℚ R` instance.
-/
theorem algebraRat.charP_zero [Semiring R] [Algebra ℚ R] : CharP R 0 :=
  charP_of_injective_algebraMap (algebraMap ℚ R).injective 0

/-- A nontrivial `ℚ`-algebra has characteristic zero.

This cannot be a (local) instance because it would immediately form a loop with the
instance `DivisionRing.toRatAlgebra`. It's probably easier to go the other way: prove `CharZero R`
and automatically receive an `Algebra ℚ R` instance.
-/
theorem algebraRat.charZero [Ring R] [Algebra ℚ R] : CharZero R :=
  @CharP.charP_to_charZero R _ (algebraRat.charP_zero R)

end QAlgebra

/-!
An algebra over a field has the same characteristic as the field.
-/

lemma RingHom.charP_iff_charP {K L : Type*} [DivisionRing K] [NonAssocSemiring L] [Nontrivial L]
    (f : K →+* L) (p : ℕ) : CharP K p ↔ CharP L p := by
  simp only [charP_iff, ← f.injective.eq_iff, map_natCast f, map_zero f]

section

variable (K L : Type*) [Field K] [CommSemiring L] [Nontrivial L] [Algebra K L]

protected theorem Algebra.charP_iff (p : ℕ) : CharP K p ↔ CharP L p :=
  (algebraMap K L).charP_iff_charP p

theorem Algebra.ringChar_eq : ringChar K = ringChar L := by
  rw [ringChar.eq_iff, Algebra.charP_iff K L]
  apply ringChar.charP

end

namespace FreeAlgebra

variable {R X : Type*} [CommSemiring R] (p : ℕ)

/-- If `R` has characteristic `p`, then so does `FreeAlgebra R X`. -/
instance charP [CharP R p] : CharP (FreeAlgebra R X) p :=
  charP_of_injective_algebraMap FreeAlgebra.algebraMap_leftInverse.injective p

/-- If `R` has characteristic `0`, then so does `FreeAlgebra R X`. -/
instance charZero [CharZero R] : CharZero (FreeAlgebra R X) :=
  charZero_of_injective_algebraMap FreeAlgebra.algebraMap_leftInverse.injective

end FreeAlgebra

namespace IsFractionRing

variable (R : Type*) {K : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
variable (p : ℕ)

/-- If `R` has characteristic `p`, then so does Frac(R). -/
theorem charP_of_isFractionRing [CharP R p] : CharP K p :=
  charP_of_injective_algebraMap (IsFractionRing.injective R K) p

/-- If `R` has characteristic `0`, then so does Frac(R). -/
theorem charZero_of_isFractionRing [CharZero R] : CharZero K :=
  @CharP.charP_to_charZero K _ (charP_of_isFractionRing R 0)

variable [IsDomain R]

/-- If `R` has characteristic `p`, then so does `FractionRing R`. -/
instance charP [CharP R p] : CharP (FractionRing R) p :=
  charP_of_isFractionRing R p

/-- If `R` has characteristic `0`, then so does `FractionRing R`. -/
instance charZero [CharZero R] : CharZero (FractionRing R) :=
  charZero_of_isFractionRing R

end IsFractionRing
