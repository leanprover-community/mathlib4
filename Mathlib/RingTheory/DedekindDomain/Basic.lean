/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio

! This file was ported from Lean 3 source module ring_theory.dedekind_domain.basic
! leanprover-community/mathlib commit 926daa81fd8acb2a04e15572c4ff20af2753c2ae
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Dedekind domains

This file defines the notion of a Dedekind domain (or Dedekind ring),
as a Noetherian integrally closed commutative ring of Krull dimension at most one.

## Main definitions

 - `is_dedekind_domain` defines a Dedekind domain as a commutative ring that is
   Noetherian, integrally closed in its field of fractions and has Krull dimension at most one.
   `is_dedekind_domain_iff` shows that this does not depend on the choice of field of fractions.

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

Often, definitions assume that Dedekind domains are not fields. We found it more practical
to add a `(h : ¬ is_field A)` assumption whenever this is explicitly needed.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/


variable (R A K : Type _) [CommRing R] [CommRing A] [Field K]

open scoped nonZeroDivisors Polynomial

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (p «expr ≠ » («expr⊥»() : ideal[ideal] R)) -/
/-- A ring `R` has Krull dimension at most one if all nonzero prime ideals are maximal. -/
def Ring.DimensionLeOne : Prop :=
  ∀ (p) (_ : p ≠ (⊥ : Ideal R)), p.IsPrime → p.IsMaximal
#align ring.dimension_le_one Ring.DimensionLeOne

open Ideal Ring

namespace Ring

theorem DimensionLeOne.principal_ideal_ring [IsDomain A] [IsPrincipalIdealRing A] :
    DimensionLeOne A := fun p nonzero prime =>
  haveI := Prime
  IsPrime.to_maximal_ideal nonzero
#align ring.dimension_le_one.principal_ideal_ring Ring.DimensionLeOne.principal_ideal_ring

theorem DimensionLeOne.isIntegralClosure (B : Type _) [CommRing B] [IsDomain B] [Nontrivial R]
    [Algebra R A] [Algebra R B] [Algebra B A] [IsScalarTower R B A] [IsIntegralClosure B R A]
    (h : DimensionLeOne R) : DimensionLeOne B := fun p ne_bot prime =>
  is_integral_closure.is_maximal_of_is_maximal_comap A p
    (h _ (is_integral_closure.comap_ne_bot A ne_bot) inferInstance)
#align ring.dimension_le_one.is_integral_closure Ring.DimensionLeOne.isIntegralClosure

theorem DimensionLeOne.integralClosure [Nontrivial R] [IsDomain A] [Algebra R A]
    (h : DimensionLeOne R) : DimensionLeOne (integralClosure R A) :=
  h.IsIntegralClosure R A (integralClosure R A)
#align ring.dimension_le_one.integral_closure Ring.DimensionLeOne.integralClosure

variable {R}

theorem DimensionLeOne.not_lt_lt (h : Ring.DimensionLeOne R) (p₀ p₁ p₂ : Ideal R) [hp₁ : p₁.IsPrime]
    [hp₂ : p₂.IsPrime] : ¬(p₀ < p₁ ∧ p₁ < p₂)
  | ⟨h01, h12⟩ => h12.Ne ((h p₁ (bot_le.trans_lt h01).ne' hp₁).eq_of_le hp₂.ne_top h12.le)
#align ring.dimension_le_one.not_lt_lt Ring.DimensionLeOne.not_lt_lt

theorem DimensionLeOne.eq_bot_of_lt (h : Ring.DimensionLeOne R) (p P : Ideal R) [hp : p.IsPrime]
    [hP : P.IsPrime] (hpP : p < P) : p = ⊥ :=
  by_contra fun hp0 => h.not_lt_lt ⊥ p P ⟨Ne.bot_lt hp0, hpP⟩
#align ring.dimension_le_one.eq_bot_of_lt Ring.DimensionLeOne.eq_bot_of_lt

end Ring

variable [IsDomain A]

/-- A Dedekind domain is an integral domain that is Noetherian, integrally closed, and
has Krull dimension at most one.

This is definition 3.2 of [Neukirch1992].

The integral closure condition is independent of the choice of field of fractions:
use `is_dedekind_domain_iff` to prove `is_dedekind_domain` for a given `fraction_map`.

This is the default implementation, but there are equivalent definitions,
`is_dedekind_domain_dvr` and `is_dedekind_domain_inv`.
TODO: Prove that these are actually equivalent definitions.
-/
class IsDedekindDomain : Prop where
  IsNoetherianRing : IsNoetherianRing A
  DimensionLeOne : DimensionLeOne A
  IsIntegrallyClosed : IsIntegrallyClosed A
#align is_dedekind_domain IsDedekindDomain

-- See library note [lower instance priority]
attribute [instance 100] IsDedekindDomain.isNoetherianRing IsDedekindDomain.isIntegrallyClosed

/-- An integral domain is a Dedekind domain iff and only if it is
Noetherian, has dimension ≤ 1, and is integrally closed in a given fraction field.
In particular, this definition does not depend on the choice of this fraction field. -/
theorem isDedekindDomain_iff (K : Type _) [Field K] [Algebra A K] [IsFractionRing A K] :
    IsDedekindDomain A ↔
      IsNoetherianRing A ∧
        DimensionLeOne A ∧ ∀ {x : K}, IsIntegral A x → ∃ y, algebraMap A K y = x :=
  ⟨fun ⟨hr, hd, hi⟩ => ⟨hr, hd, fun x => (isIntegrallyClosed_iff K).mp hi⟩, fun ⟨hr, hd, hi⟩ =>
    ⟨hr, hd, (isIntegrallyClosed_iff K).mpr @hi⟩⟩
#align is_dedekind_domain_iff isDedekindDomain_iff

-- See library note [lower instance priority]
instance (priority := 100) IsPrincipalIdealRing.isDedekindDomain [IsPrincipalIdealRing A] :
    IsDedekindDomain A :=
  ⟨PrincipalIdealRing.isNoetherianRing, Ring.DimensionLeOne.principal_ideal_ring A,
    UniqueFactorizationMonoid.isIntegrallyClosed⟩
#align is_principal_ideal_ring.is_dedekind_domain IsPrincipalIdealRing.isDedekindDomain

