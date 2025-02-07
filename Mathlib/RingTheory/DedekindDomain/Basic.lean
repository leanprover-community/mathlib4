/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Dedekind rings and domains

This file defines the notion of a Dedekind ring (domain),
as a Noetherian integrally closed commutative ring (domain) of Krull dimension at most one.

## Main definitions

 - `IsDedekindRing` defines a Dedekind ring as a commutative ring that is
   Noetherian, integrally closed in its field of fractions and has Krull dimension at most one.
   `isDedekindRing_iff` shows that this does not depend on the choice of field of fractions.
 - `IsDedekindDomain` defines a Dedekind domain as a Dedekind ring that is a domain.

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

`IsDedekindRing` and `IsDedekindDomain` form a cycle in the typeclass hierarchy:
`IsDedekindRing R + IsDomain R` imply `IsDedekindDomain R`, which implies `IsDedekindRing R`.
This should be safe since the start and end point is the literal same expression,
which the tabled typeclass synthesis algorithm can deal with.

Often, definitions assume that Dedekind rings are not fields. We found it more practical
to add a `(h : ¬ IsField A)` assumption whenever this is explicitly needed.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/


variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]

open scoped nonZeroDivisors Polynomial

open Ideal Ring

namespace Ring

@[deprecated (since := "2025-02-05")] alias DimensionLEOne.isIntegralClosure :=
  Ring.KrullDimLE.of_isIntegral

@[deprecated (since := "2025-02-05")] alias DimensionLEOne.integralClosure :=
  Ring.KrullDimLE.integralClosure

variable {R}

end Ring

/-- A Dedekind ring is a commutative ring that is Noetherian, integrally closed, and
has Krull dimension at most one.

This is exactly `IsDedekindDomain` minus the `IsDomain` hypothesis.

The integral closure condition is independent of the choice of field of fractions:
use `isDedekindRing_iff` to prove `IsDedekindRing` for a given `fraction_map`.
-/
class IsDedekindRing
  extends IsNoetherian A A, Ring.KrullDimLE 1 A, IsIntegralClosure A A (FractionRing A) : Prop

/-- An integral domain is a Dedekind domain if and only if it is
Noetherian, has dimension ≤ 1, and is integrally closed in a given fraction field.
In particular, this definition does not depend on the choice of this fraction field. -/
theorem isDedekindRing_iff (K : Type*) [CommRing K] [Algebra A K] [IsFractionRing A K] :
    IsDedekindRing A ↔
      IsNoetherianRing A ∧ Ring.KrullDimLE 1 A ∧
        ∀ {x : K}, IsIntegral A x → ∃ y, algebraMap A K y = x :=
  ⟨fun _ => ⟨inferInstance, inferInstance,
             fun {_} => (isIntegrallyClosed_iff K).mp inferInstance⟩,
   fun ⟨hr, hd, hi⟩ => { hr, hd, (isIntegrallyClosed_iff K).mpr @hi with }⟩

/-- A Dedekind domain is an integral domain that is Noetherian, integrally closed, and
has Krull dimension at most one.

This is definition 3.2 of [Neukirch1992].

This is exactly `IsDedekindRing` plus the `IsDomain` hypothesis.

The integral closure condition is independent of the choice of field of fractions:
use `isDedekindDomain_iff` to prove `IsDedekindDomain` for a given `fraction_map`.

This is the default implementation, but there are equivalent definitions,
`IsDedekindDomainDvr` and `IsDedekindDomainInv`.
-/
class IsDedekindDomain
  extends IsDomain A, IsDedekindRing A : Prop

attribute [instance 90] IsDedekindDomain.toIsDomain

/-- Make a Dedekind domain from a Dedekind ring given that it is a domain.

`IsDedekindRing` and `IsDedekindDomain` form a cycle in the typeclass hierarchy:
`IsDedekindRing R + IsDomain R` imply `IsDedekindDomain R`, which implies `IsDedekindRing R`.
This should be safe since the start and end point is the literal same expression,
which the tabled typeclass synthesis algorithm can deal with.
-/
instance [IsDomain A] [IsDedekindRing A] : IsDedekindDomain A where

/-- An integral domain is a Dedekind domain iff and only if it is
Noetherian, has dimension ≤ 1, and is integrally closed in a given fraction field.
In particular, this definition does not depend on the choice of this fraction field. -/
theorem isDedekindDomain_iff (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] :
    IsDedekindDomain A ↔
      IsDomain A ∧ IsNoetherianRing A ∧ Ring.KrullDimLE 1 A ∧
        ∀ {x : K}, IsIntegral A x → ∃ y, algebraMap A K y = x :=
  ⟨fun _ => ⟨inferInstance, inferInstance, inferInstance,
             fun {_} => (isIntegrallyClosed_iff K).mp inferInstance⟩,
   fun ⟨hid, hr, hd, hi⟩ => { hid, hr, hd, (isIntegrallyClosed_iff K).mpr @hi with }⟩

-- See library note [lower instance priority]
instance (priority := 100) IsPrincipalIdealRing.isDedekindDomain
    [IsDomain A] [IsPrincipalIdealRing A] :
    IsDedekindDomain A where
