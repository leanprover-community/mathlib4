/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.RingTheory.IntegralClosure
import Mathlib.RingTheory.Localization.Integral

#align_import ring_theory.integrally_closed from "leanprover-community/mathlib"@"d35b4ff446f1421bd551fafa4b8efd98ac3ac408"

/-!
# Integrally closed rings

An integrally closed ring `R` in an algebra `A` contains all the elements of `A` that are
integral over `R`. A special case of integrally closed rings are the Dedekind domains.
[Stacks: integrally closed ring](https://stacks.math.columbia.edu/tag/00GP)

## Main definitions

* `IsIntegrallyClosed R A` states `R` contains all integral elements of `A`

## Main results

* `AlgEquiv.isIntegrallyClosed_iff e`, where `e` is an isomorphism of `R`-algebras `A` and `A'`,
  states `R` is integrally closed in `A` iff it is integrally closed in `A'`.
* `isIntegrallyClosed_fractionRing_iff K`, where `K` is a fraction field of `R`, states `R`
  is integrally closed iff it is the integral closure of `R` in `K`

## TODO: Related notions

The following definitions are closely related, especially in their applications in Mathlib.

A *normal domain* is a domain that is integrally closed in its field of fractions.
[Stacks: normal domain](https://stacks.math.columbia.edu/tag/0309)
Normal domains are the major usecase of `IsIntegrallyClosed` at the time of writing, and we have
quite a few results that can be moved wholesale to a new `NormalDomain` definition.
In fact, before PR #6126 `IsIntegrallyClosed` was exactly defined to be a normal domain.
(So you might want to copy some of its API when you define normal domains.)

A normal ring means that localizations at all prime ideals are normal domains.
[Stacks: normal ring](https://stacks.math.columbia.edu/tag/00GV)
This implies integral closedness in its `FractionRing`,
[Stacks: Lemma 10.37.12](https://stacks.math.columbia.edu/tag/034M)
but is equivalent to it only under some conditions (reduced + finitely many minimal primes),
[Stacks: Lemma 10.37.16](https://stacks.math.columbia.edu/tag/034M)
in which case it's also equivalent to being a finite product of normal domains.

We'd need to add these conditions if we want exactly the products of Dedekind domains.

In fact noetherianity is sufficient to guarantee finitely many minimal primes, so `IsDedekindRing`
could be defined as `IsReduced`, `IsNoetherian`, `Ring.DimensionLEOne`, and either
`IsIntegrallyClosed` or `NormalDomain`. If we use `NormalDomain` then `IsReduced` is automatic,
but we could also consider a version of `NormalDomain` that only requires the localizations are
`IsIntegrallyClosed` in their `FractionRings` but may not be domains,
and that may not equivalent to the ring itself being `IsIntegallyClosed` in its `FractionRing`
(even for noetherian rings?).
-/


open scoped nonZeroDivisors Polynomial

open Polynomial

/-- `R` is integrally closed in `A` if all integral elements of `A` are also elements of `R`.
[Stacks: integrally closed ring](https://stacks.math.columbia.edu/tag/00GP)
-/
@[mk_iff]
class IsIntegrallyClosed (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] : Prop where
  /-- All integral elements of `A` are also elements of `R`. -/
  algebraMap_eq_of_integral :
    ∀ {x : A}, IsIntegral R x → ∃ y, algebraMap R A y = x
#align is_integrally_closed IsIntegrallyClosed

section Iff

variable {R : Type*} [CommRing R]

section Algebra

variable {A : Type*} [CommRing A] [Algebra R A]

/-- `R` is integrally closed in the ring extension `A`
iff it is the integral closure of itself in `A`. -/
theorem isIntegrallyClosed_iff_isIntegralClosure (h : Function.Injective (algebraMap R A)) :
    IsIntegrallyClosed R A ↔ IsIntegralClosure R R A :=
  (IsIntegrallyClosed_iff _ _).trans <| by
    constructor
    · intro cl
      refine' ⟨h, ⟨cl, _⟩⟩
      rintro ⟨y, y_eq⟩
      rw [← y_eq]
      exact isIntegral_algebraMap
    · rintro ⟨-, cl⟩ x hx
      exact cl.mp hx
#align is_integrally_closed_iff_is_integral_closure isIntegrallyClosed_iff_isIntegralClosure

variable {A' : Type*} [CommRing A'] [Algebra R A']

theorem AlgebraMap.isIntegrallyClosed (f : A →ₐ[R] A') (hf : Function.Injective ↑f)
    (h : IsIntegrallyClosed R A') :
    IsIntegrallyClosed R A :=
  ⟨fun hx => let ⟨y, hy⟩ := h.algebraMap_eq_of_integral (map_isIntegral f hx)
   ⟨y, hf (by rw [f.map_algebraMap, hy])⟩⟩

theorem AlgEquiv.isIntegrallyClosed_iff (e : A ≃ₐ[R] A') :
    IsIntegrallyClosed R A ↔ IsIntegrallyClosed R A' :=
  ⟨AlgebraMap.isIntegrallyClosed e.symm e.symm.injective,
   AlgebraMap.isIntegrallyClosed e e.injective⟩

end Algebra

section FractionRing

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
variable (K' : Type*) [Field K'] [Algebra R K'] [IsFractionRing R K']

/-- `R` is integrally closed iff all integral elements of its fraction field `K`
are also elements of `R`. -/
theorem isIntegrallyClosed_fractionRing_iff :
    IsIntegrallyClosed R K ↔
      ∀ {x : K'}, IsIntegral R x → ∃ y, algebraMap R K' y = x :=
  (IsLocalization.algEquiv R⁰ K K').isIntegrallyClosed_iff.trans (IsIntegrallyClosed_iff _ _)
#align is_integrally_closed_iff isIntegrallyClosed_fractionRing_iff

end FractionRing

end Iff

namespace IsIntegrallyClosed

variable {R : Type*} [CommRing R] [id : IsDomain R]

section Algebra

variable {A : Type*} [CommRing A] [Algebra R A]

variable [iic : IsIntegrallyClosed R A]

theorem isIntegral_iff {x : A} : IsIntegral R x ↔ ∃ y : R, algebraMap R A y = x :=
  ⟨IsIntegrallyClosed.algebraMap_eq_of_integral,
   by rintro ⟨_, rfl⟩; exact isIntegral_algebraMap⟩
#align is_integrally_closed.is_integral_iff IsIntegrallyClosed.isIntegral_iff

theorem exists_algebraMap_eq_of_isIntegral_pow {x : A} {n : ℕ} (hn : 0 < n)
    (hx : IsIntegral R <| x ^ n) : ∃ y : R, algebraMap R A y = x :=
  isIntegral_iff.mp <| isIntegral_of_pow hn hx
#align is_integrally_closed.exists_algebra_map_eq_of_is_integral_pow IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow

theorem exists_algebraMap_eq_of_pow_mem_subalgebra {A : Type*} [CommRing A] [Algebra R A]
    {S : Subalgebra R A} [IsIntegrallyClosed S A] {x : A} {n : ℕ} (hn : 0 < n)
    (hx : x ^ n ∈ S) : ∃ y : S, algebraMap S A y = x :=
  exists_algebraMap_eq_of_isIntegral_pow hn <| isIntegral_iff.mpr ⟨⟨x ^ n, hx⟩, rfl⟩
#align is_integrally_closed.exists_algebra_map_eq_of_pow_mem_subalgebra IsIntegrallyClosed.exists_algebraMap_eq_of_pow_mem_subalgebra

variable (A)

theorem integralClosure_eq_bot_iff : integralClosure R A = ⊥ ↔ IsIntegrallyClosed R A := by
  refine' eq_bot_iff.trans _
  constructor
  · rw [IsIntegrallyClosed_iff _ A]
    intro h x hx
    exact Set.mem_range.mp (Algebra.mem_bot.mp (h hx))
  · intro h x hx
    rw [Algebra.mem_bot, Set.mem_range]
    exact isIntegral_iff.mp hx
#align is_integrally_closed.integral_closure_eq_bot_iff IsIntegrallyClosed.integralClosure_eq_bot_iff

variable (R)

@[simp]
theorem integralClosure_eq_bot : integralClosure R A = ⊥ :=
  (integralClosure_eq_bot_iff A).mpr ‹_›
#align is_integrally_closed.integral_closure_eq_bot IsIntegrallyClosed.integralClosure_eq_bot


end Algebra

section Injective

-- TODO: this section can be generalized from `IsFractionRing` to any `Algebra` that is injective,
-- but there is no way to hook that assumption up to the typeclass system.

variable {K : Type*} [Field K] [Algebra R K] [ifr : IsFractionRing R K]

variable [iic : IsIntegrallyClosed R K]

instance : IsIntegralClosure R R K :=
  (isIntegrallyClosed_iff_isIntegralClosure (IsFractionRing.injective _ _)).mp iic

end Injective

end IsIntegrallyClosed

namespace integralClosure

open IsIntegrallyClosed

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

instance isIntegrallyClosed :
    IsIntegrallyClosed (integralClosure R A) A :=
  (integralClosure_eq_bot_iff A).mp integralClosure_idem
#align integral_closure.is_integrally_closed_of_finite_extension integralClosure.isIntegrallyClosed

end integralClosure
