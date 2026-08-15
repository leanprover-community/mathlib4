/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # Rings with finite quotients

A commutative ring is said to have finite quotients if, for any nonzero ideal `I` of `R`, the
quotient `R ⧸ I` is finite.

This file defines the class `Ring.HasFiniteQuotients` and its basic API.

## Main results
- `Ring.HasFiniteQuotients.of_module_finite`: Assume that `R` has finite quotients and that `S` is
  a domain and a finite `R`-module. Then `S` has finite quotients.
- `Ring.HasFiniteQuotients.instOfIsDomainOfFG`: A domain that is also a finite `ℤ`-module
  has finite quotients.

-/

public section

/--
A ring `R` has finite quotients if the quotient `R ⧸ I` is finite for all nonzero ideals of `R`.
-/
class Ring.HasFiniteQuotients (R : Type*) [CommRing R] : Prop where
  finiteQuotient {I : Ideal R} : I ≠ ⊥ → Finite (R ⧸ I)

namespace Ring.HasFiniteQuotients

variable {R : Type*} [CommRing R]

/-- A finite ring has finite quotients. -/
instance [Finite R] : Ring.HasFiniteQuotients R where
  finiteQuotient := fun _ ↦ Quotient.finite _

section properties

variable [HasFiniteQuotients R]

/-- A nonzero prime ideal of a ring with finite quotients is maximal. -/
theorem maximalOfPrime {P : Ideal R} [P.IsPrime] (hp : P ≠ ⊥) :
    P.IsMaximal :=
  have : Finite (R ⧸ P) := finiteQuotient hp
  Ideal.Quotient.maximal_of_isField P <| Finite.isField_of_domain (R ⧸ P)

instance [IsDomain R] [PerfectField (FractionRing R)] (P : Ideal R) [P.IsPrime] :
    PerfectField P.ResidueField := by
  rcases eq_or_ne P ⊥ with rfl | hP
  · exact PerfectField.of_ringEquiv (FractionRing.algEquiv R _).toRingEquiv
  · have : Finite (R ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP
    infer_instance

variable (R) in
/--
Assume that `R` has finite quotients and that `S` is a domain and a finite `R`-module. Then
`S` has finite quotients.
-/
theorem of_module_finite (S : Type*) [CommRing S] [IsDomain S]
    [Algebra R S] [Module.Finite R S] :
    HasFiniteQuotients S where
  finiteQuotient {I} hI := by
    obtain hR | hR := subsingleton_or_nontrivial R
    · have : Finite S := Module.finite_of_finite R
      exact Quotient.finite _
    let J : Ideal R := Ideal.under R I
    have : Finite (R ⧸ J) := finiteQuotient <| Ideal.under_ne_bot R hI
    have : Module.Finite (R ⧸ J) (S ⧸ I) := Module.Finite.of_restrictScalars_finite R _ _
    exact Module.finite_of_finite (R ⧸ J)

end properties

/-- The ring `ℤ` has finite quotients. -/
instance : HasFiniteQuotients ℤ where
  finiteQuotient {I} hI := by
    obtain ⟨n, rfl⟩ := Submodule.IsPrincipal.principal I
    have : NeZero n := ⟨by simpa using hI⟩
    exact inferInstanceAs <| Finite (ℤ ⧸ Ideal.span {n})

/-- A domain that is finitely generated has finite quotients. -/
instance [IsDomain R] [Module.Finite ℤ R] : HasFiniteQuotients R :=
  .of_module_finite ℤ R

end Ring.HasFiniteQuotients
