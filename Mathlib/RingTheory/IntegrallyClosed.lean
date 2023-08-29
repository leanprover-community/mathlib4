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

An integrally closed domain `R` contains all the elements of `Frac(R)` that are
integral over `R`. A special case of integrally closed domains are the Dedekind domains.

## Main definitions

* `IsIntegrallyClosed R` states `R` contains all integral elements of `Frac(R)`

## Main results

* `isIntegrallyClosed_iff K`, where `K` is a fraction field of `R`, states `R`
  is integrally closed iff it is the integral closure of `R` in `K`
-/


open scoped nonZeroDivisors Polynomial

open Polynomial

/-- `R` is integrally closed if all integral elements of `Frac(R)` are also elements of `R`.

This definition uses `FractionRing R` to denote `Frac(R)`. See `isIntegrallyClosed_iff`
if you want to choose another field of fractions for `R`.
-/
class IsIntegrallyClosed (R : Type*) [CommRing R] [IsDomain R] : Prop where
  /-- All integral elements of `Frac(R)` are also elements of `R`. -/
  algebraMap_eq_of_integral :
    ∀ {x : FractionRing R}, IsIntegral R x → ∃ y, algebraMap R (FractionRing R) y = x
#align is_integrally_closed IsIntegrallyClosed

section Iff

variable {R : Type*} [CommRing R] [IsDomain R]

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- `R` is integrally closed iff all integral elements of its fraction field `K`
are also elements of `R`. -/
theorem isIntegrallyClosed_iff :
    IsIntegrallyClosed R ↔ ∀ {x : K}, IsIntegral R x → ∃ y, algebraMap R K y = x := by
  let e : K ≃ₐ[R] FractionRing R := IsLocalization.algEquiv R⁰ _ _
  -- ⊢ IsIntegrallyClosed R ↔ ∀ {x : K}, IsIntegral R x → ∃ y, ↑(algebraMap R K) y  …
  constructor
  -- ⊢ IsIntegrallyClosed R → ∀ {x : K}, IsIntegral R x → ∃ y, ↑(algebraMap R K) y  …
  · rintro ⟨cl⟩
    -- ⊢ ∀ {x : K}, IsIntegral R x → ∃ y, ↑(algebraMap R K) y = x
    refine' fun hx => _
    -- ⊢ ∃ y, ↑(algebraMap R K) y = x✝
    obtain ⟨y, hy⟩ := cl ((isIntegral_algEquiv e).mpr hx)
    -- ⊢ ∃ y, ↑(algebraMap R K) y = x✝
    exact ⟨y, e.algebraMap_eq_apply.mp hy⟩
    -- 🎉 no goals
  · rintro cl
    -- ⊢ IsIntegrallyClosed R
    refine' ⟨fun hx => _⟩
    -- ⊢ ∃ y, ↑(algebraMap R (FractionRing R)) y = x✝
    obtain ⟨y, hy⟩ := cl ((isIntegral_algEquiv e.symm).mpr hx)
    -- ⊢ ∃ y, ↑(algebraMap R (FractionRing R)) y = x✝
    exact ⟨y, e.symm.algebraMap_eq_apply.mp hy⟩
    -- 🎉 no goals
#align is_integrally_closed_iff isIntegrallyClosed_iff

/-- `R` is integrally closed iff it is the integral closure of itself in its field of fractions. -/
theorem isIntegrallyClosed_iff_isIntegralClosure : IsIntegrallyClosed R ↔ IsIntegralClosure R R K :=
  (isIntegrallyClosed_iff K).trans <| by
    constructor
    -- ⊢ (∀ {x : K}, IsIntegral R x → ∃ y, ↑(algebraMap R K) y = x) → IsIntegralClosu …
    · intro cl
      -- ⊢ IsIntegralClosure R R K
      refine' ⟨IsFractionRing.injective R K, ⟨cl, _⟩⟩
      -- ⊢ (∃ y, ↑(algebraMap R K) y = x✝) → IsIntegral R x✝
      rintro ⟨y, y_eq⟩
      -- ⊢ IsIntegral R x✝
      rw [← y_eq]
      -- ⊢ IsIntegral R (↑(algebraMap R K) y)
      exact isIntegral_algebraMap
      -- 🎉 no goals
    · rintro ⟨-, cl⟩ x hx
      -- ⊢ ∃ y, ↑(algebraMap R K) y = x
      exact cl.mp hx
      -- 🎉 no goals
#align is_integrally_closed_iff_is_integral_closure isIntegrallyClosed_iff_isIntegralClosure

end Iff

namespace IsIntegrallyClosed

variable {R : Type*} [CommRing R] [id : IsDomain R] [iic : IsIntegrallyClosed R]

variable {K : Type*} [Field K] [Algebra R K] [ifr : IsFractionRing R K]

instance : IsIntegralClosure R R K :=
  (isIntegrallyClosed_iff_isIntegralClosure K).mp iic

theorem isIntegral_iff {x : K} : IsIntegral R x ↔ ∃ y : R, algebraMap R K y = x :=
  IsIntegralClosure.isIntegral_iff
#align is_integrally_closed.is_integral_iff IsIntegrallyClosed.isIntegral_iff

theorem exists_algebraMap_eq_of_isIntegral_pow {x : K} {n : ℕ} (hn : 0 < n)
    (hx : IsIntegral R <| x ^ n) : ∃ y : R, algebraMap R K y = x :=
  isIntegral_iff.mp <| isIntegral_of_pow hn hx
#align is_integrally_closed.exists_algebra_map_eq_of_is_integral_pow IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow

theorem exists_algebraMap_eq_of_pow_mem_subalgebra {K : Type*} [Field K] [Algebra R K]
    {S : Subalgebra R K} [IsIntegrallyClosed S] [IsFractionRing S K] {x : K} {n : ℕ} (hn : 0 < n)
    (hx : x ^ n ∈ S) : ∃ y : S, algebraMap S K y = x :=
  exists_algebraMap_eq_of_isIntegral_pow hn <| isIntegral_iff.mpr ⟨⟨x ^ n, hx⟩, rfl⟩
#align is_integrally_closed.exists_algebra_map_eq_of_pow_mem_subalgebra IsIntegrallyClosed.exists_algebraMap_eq_of_pow_mem_subalgebra

variable (K)

theorem integralClosure_eq_bot_iff : integralClosure R K = ⊥ ↔ IsIntegrallyClosed R := by
  refine' eq_bot_iff.trans _
  -- ⊢ integralClosure R K ≤ ⊥ ↔ IsIntegrallyClosed R
  constructor
  -- ⊢ integralClosure R K ≤ ⊥ → IsIntegrallyClosed R
  · rw [isIntegrallyClosed_iff K]
    -- ⊢ integralClosure R K ≤ ⊥ → ∀ {x : K}, IsIntegral R x → ∃ y, ↑(algebraMap R K) …
    intro h x hx
    -- ⊢ ∃ y, ↑(algebraMap R K) y = x
    exact Set.mem_range.mp (Algebra.mem_bot.mp (h hx))
    -- 🎉 no goals
  · intro h x hx
    -- ⊢ x ∈ ⊥
    rw [Algebra.mem_bot, Set.mem_range]
    -- ⊢ ∃ y, ↑(algebraMap R K) y = x
    exact isIntegral_iff.mp hx
    -- 🎉 no goals
#align is_integrally_closed.integral_closure_eq_bot_iff IsIntegrallyClosed.integralClosure_eq_bot_iff

variable (R)

@[simp]
theorem integralClosure_eq_bot : integralClosure R K = ⊥ :=
  (integralClosure_eq_bot_iff K).mpr ‹_›
#align is_integrally_closed.integral_closure_eq_bot IsIntegrallyClosed.integralClosure_eq_bot

end IsIntegrallyClosed

namespace integralClosure

open IsIntegrallyClosed

variable {R : Type*} [CommRing R]

variable (K : Type*) [Field K] [Algebra R K]

variable [IsDomain R] [IsFractionRing R K]

variable {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]

-- Can't be an instance because you need to supply `K`.
theorem isIntegrallyClosedOfFiniteExtension [FiniteDimensional K L] :
    IsIntegrallyClosed (integralClosure R L) :=
  letI : IsFractionRing (integralClosure R L) L := isFractionRing_of_finite_extension K L
  (integralClosure_eq_bot_iff L).mp integralClosure_idem
#align integral_closure.is_integrally_closed_of_finite_extension integralClosure.isIntegrallyClosedOfFiniteExtension

end integralClosure
