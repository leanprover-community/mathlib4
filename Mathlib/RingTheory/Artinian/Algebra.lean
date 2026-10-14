/-
Copyright (c) 2025 Michal Staromiejski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Staromiejski
-/
module

public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs

import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Algebras over Artinian rings

In this file we collect results about algebras over Artinian rings.
-/

public section

namespace IsArtinianRing

variable {R A : Type*}
variable [CommRing R] [IsArtinianRing R] [Ring A] [Algebra R A]

open nonZeroDivisors

/-- In an `R`-algebra over an Artinian ring `R`, if an element is integral and
is not a zero divisor, then it is a unit. -/
theorem isUnit_of_isIntegral_of_nonZeroDivisor {a : A}
    (hi : IsIntegral R a) (ha : a ∈ A⁰) : IsUnit a :=
  let B := Algebra.adjoin R {a}
  let b : B := ⟨a, Algebra.self_mem_adjoin_singleton R a⟩
  haveI : Module.Finite R B := Algebra.finite_adjoin_simple_of_isIntegral hi
  haveI : IsArtinianRing B := isArtinian_of_tower R inferInstance
  have hinj : Function.Injective B.subtype := Subtype.val_injective
  have hb : b ∈ B⁰ := comap_nonZeroDivisors_le_of_injective hinj ha
  (isUnit_of_mem_nonZeroDivisors hb).map B.subtype

/-- Integral element of an algebra over Artinian ring `R` is either a zero divisor or a unit. -/
theorem isUnit_iff_nonZeroDivisor_of_isIntegral {a : A}
    (hi : IsIntegral R a) : IsUnit a ↔ a ∈ A⁰ :=
  ⟨IsUnit.mem_nonZeroDivisors, isUnit_of_isIntegral_of_nonZeroDivisor hi⟩

/-- In an `R`-algebra over an Artinian ring `R`, if an element is integral and
is not a zero divisor, then it is a unit. -/
theorem isUnit_of_nonZeroDivisor_of_isIntegral' [Algebra.IsIntegral R A] {a : A}
    (ha : a ∈ A⁰) : IsUnit a :=
  isUnit_of_isIntegral_of_nonZeroDivisor (R := R) (Algebra.IsIntegral.isIntegral a) ha

/-- Integral element of an algebra over Artinian ring `R` is either a zero divisor or a unit. -/
theorem isUnit_iff_nonZeroDivisor_of_isIntegral' [Algebra.IsIntegral R A] {a : A} :
    IsUnit a ↔ a ∈ A⁰ :=
  isUnit_iff_nonZeroDivisor_of_isIntegral (R := R) (Algebra.IsIntegral.isIntegral a)

theorem isUnit_submonoid_eq_of_isIntegral [Algebra.IsIntegral R A] : IsUnit.submonoid A = A⁰ := by
  ext; simpa [IsUnit.mem_submonoid_iff] using isUnit_iff_nonZeroDivisor_of_isIntegral' (R := R)

theorem isUnit_of_isIntegral_of_isUnit {B : Subalgebra R A} {a : B} (hi : IsIntegral R (a : A))
    (ha : IsUnit (a : A)) : IsUnit a :=
  isUnit_of_isIntegral_of_nonZeroDivisor
    ((isIntegral_algHom_iff B.val Subtype.val_injective).mp hi)
    (comap_nonZeroDivisors_le_of_injective (f := B.val) Subtype.val_injective
      ha.mem_nonZeroDivisors)

/-- Over an Artinian ring `R`, an `R`-subalgebra `B` of `A` contains the inverse of every unit
of `A` which lies in `B` and is integral over `R`. For instance, when `R = K` is a field, a
`K`-subalgebra of `Module.End K V` with `V` finite-dimensional is closed under taking inverses. -/
theorem inv_mem_of_isIntegral {B : Subalgebra R A} {u : Aˣ} (hi : IsIntegral R (u : A))
    (hu : (u : A) ∈ B) : ((u⁻¹ : Aˣ) : A) ∈ B := by
  obtain ⟨v, hv⟩ := isUnit_of_isIntegral_of_isUnit (a := (⟨u, hu⟩ : B)) hi u.isUnit
  have : Units.map (B.val : B →* A) v = u := Units.ext (congrArg Subtype.val hv)
  rw [← this, ← map_inv]
  exact (↑v⁻¹ : B).2

end IsArtinianRing
