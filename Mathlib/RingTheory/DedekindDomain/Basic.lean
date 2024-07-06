/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Polynomial.RationalRoot

#align_import ring_theory.dedekind_domain.basic from "leanprover-community/mathlib"@"926daa81fd8acb2a04e15572c4ff20af2753c2ae"

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

/-- A ring `R` has Krull dimension at most one if all nonzero prime ideals are maximal. -/
class Ring.DimensionLEOne : Prop :=
  (maximalOfPrime : ∀ {p : Ideal R}, p ≠ ⊥ → p.IsPrime → p.IsMaximal)
#align ring.dimension_le_one Ring.DimensionLEOne

open Ideal Ring

theorem Ideal.IsPrime.isMaximal {R : Type*} [CommRing R] [DimensionLEOne R]
    {p : Ideal R} (h : p.IsPrime) (hp : p ≠ ⊥) : p.IsMaximal :=
  DimensionLEOne.maximalOfPrime hp h

namespace Ring

instance DimensionLEOne.principal_ideal_ring [IsDomain A] [IsPrincipalIdealRing A] :
    DimensionLEOne A where
  maximalOfPrime := fun nonzero _ =>
    IsPrime.to_maximal_ideal nonzero
#align ring.dimension_le_one.principal_ideal_ring Ring.DimensionLEOne.principal_ideal_ring

theorem DimensionLEOne.isIntegralClosure (B : Type*) [CommRing B] [IsDomain B] [Nontrivial R]
    [Algebra R A] [Algebra R B] [Algebra B A] [IsScalarTower R B A] [IsIntegralClosure B R A]
    [DimensionLEOne R] : DimensionLEOne B where
  maximalOfPrime := fun {p} ne_bot _ =>
    IsIntegralClosure.isMaximal_of_isMaximal_comap (R := R) A p
      (Ideal.IsPrime.isMaximal inferInstance (IsIntegralClosure.comap_ne_bot A ne_bot))
#align ring.dimension_le_one.is_integral_closure Ring.DimensionLEOne.isIntegralClosure

nonrec instance DimensionLEOne.integralClosure [Nontrivial R] [IsDomain A] [Algebra R A]
    [DimensionLEOne R] : DimensionLEOne (integralClosure R A) :=
  DimensionLEOne.isIntegralClosure R A (integralClosure R A)
#align ring.dimension_le_one.integral_closure Ring.DimensionLEOne.integralClosure

variable {R}

theorem DimensionLEOne.not_lt_lt [Ring.DimensionLEOne R] (p₀ p₁ p₂ : Ideal R) [hp₁ : p₁.IsPrime]
    [hp₂ : p₂.IsPrime] : ¬(p₀ < p₁ ∧ p₁ < p₂)
  | ⟨h01, h12⟩ => h12.ne ((hp₁.isMaximal (bot_le.trans_lt h01).ne').eq_of_le hp₂.ne_top h12.le)
#align ring.dimension_le_one.not_lt_lt Ring.DimensionLEOne.not_lt_lt

theorem DimensionLEOne.eq_bot_of_lt [Ring.DimensionLEOne R] (p P : Ideal R) [p.IsPrime]
    [P.IsPrime] (hpP : p < P) : p = ⊥ :=
  by_contra fun hp0 => not_lt_lt ⊥ p P ⟨Ne.bot_lt hp0, hpP⟩
#align ring.dimension_le_one.eq_bot_of_lt Ring.DimensionLEOne.eq_bot_of_lt

end Ring

/-- A Dedekind ring is a commutative ring that is Noetherian, integrally closed, and
has Krull dimension at most one.

This is exactly `IsDedekindDomain` minus the `IsDomain` hypothesis.

The integral closure condition is independent of the choice of field of fractions:
use `isDedekindRing_iff` to prove `IsDedekindRing` for a given `fraction_map`.
-/
class IsDedekindRing
  extends IsNoetherian A A, DimensionLEOne A, IsIntegralClosure A A (FractionRing A) : Prop

/-- An integral domain is a Dedekind domain if and only if it is
Noetherian, has dimension ≤ 1, and is integrally closed in a given fraction field.
In particular, this definition does not depend on the choice of this fraction field. -/
theorem isDedekindRing_iff (K : Type*) [CommRing K] [Algebra A K] [IsFractionRing A K] :
    IsDedekindRing A ↔
      IsNoetherianRing A ∧ DimensionLEOne A ∧
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
`is_dedekind_domain_dvr` and `is_dedekind_domain_inv`.
TODO: Prove that these are actually equivalent definitions.
-/
class IsDedekindDomain
  extends IsDomain A, IsDedekindRing A : Prop
#align is_dedekind_domain IsDedekindDomain

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
      IsDomain A ∧ IsNoetherianRing A ∧ DimensionLEOne A ∧
        ∀ {x : K}, IsIntegral A x → ∃ y, algebraMap A K y = x :=
  ⟨fun _ => ⟨inferInstance, inferInstance, inferInstance,
             fun {_} => (isIntegrallyClosed_iff K).mp inferInstance⟩,
   fun ⟨hid, hr, hd, hi⟩ => { hid, hr, hd, (isIntegrallyClosed_iff K).mpr @hi with }⟩
#align is_dedekind_domain_iff isDedekindDomain_iff

-- See library note [lower instance priority]
instance (priority := 100) IsPrincipalIdealRing.isDedekindDomain
    [IsDomain A] [IsPrincipalIdealRing A] :
    IsDedekindDomain A :=
  { PrincipalIdealRing.isNoetherianRing, Ring.DimensionLEOne.principal_ideal_ring A,
    UniqueFactorizationMonoid.instIsIntegrallyClosed with }
#align is_principal_ideal_ring.is_dedekind_domain IsPrincipalIdealRing.isDedekindDomain
