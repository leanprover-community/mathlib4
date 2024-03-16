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

An integrally closed ring `R` contains all the elements of `Frac(R)` that are
integral over `R`. A special case of integrally closed rings are the Dedekind domains.

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
class IsIntegrallyClosed (R : Type*) [CommRing R] : Prop where
  /-- All integral elements of `Frac(R)` are also elements of `R`. -/
  algebraMap_eq_of_integral :
    ∀ {x : FractionRing R}, IsIntegral R x → ∃ y, algebraMap R (FractionRing R) y = x
#align is_integrally_closed IsIntegrallyClosed

section Iff

variable {R : Type*} [CommRing R]
variable (K : Type*) [CommRing K] [Algebra R K] [IsFractionRing R K]

/-- `R` is integrally closed iff all integral elements of its fraction field `K`
are also elements of `R`. -/
theorem isIntegrallyClosed_iff :
    IsIntegrallyClosed R ↔ ∀ {x : K}, IsIntegral R x → ∃ y, algebraMap R K y = x := by
  let e : K ≃ₐ[R] FractionRing R := IsLocalization.algEquiv R⁰ _ _
  constructor
  · rintro ⟨cl⟩
    refine' fun hx => _
    obtain ⟨y, hy⟩ := cl ((isIntegral_algEquiv e).mpr hx)
    exact ⟨y, e.algebraMap_eq_apply.mp hy⟩
  · rintro cl
    refine' ⟨fun hx => _⟩
    obtain ⟨y, hy⟩ := cl ((isIntegral_algEquiv e.symm).mpr hx)
    exact ⟨y, e.symm.algebraMap_eq_apply.mp hy⟩
#align is_integrally_closed_iff isIntegrallyClosed_iff

/-- `R` is integrally closed iff it is the integral closure of itself in its field of fractions. -/
theorem isIntegrallyClosed_iff_isIntegralClosure : IsIntegrallyClosed R ↔ IsIntegralClosure R R K :=
  (isIntegrallyClosed_iff K).trans <| by
    constructor
    · intro cl
      refine' ⟨IsFractionRing.injective R K, ⟨cl, _⟩⟩
      rintro ⟨y, y_eq⟩
      rw [← y_eq]
      exact isIntegral_algebraMap
    · rintro ⟨-, cl⟩ x hx
      exact cl.mp hx
#align is_integrally_closed_iff_is_integral_closure isIntegrallyClosed_iff_isIntegralClosure

end Iff

namespace IsIntegrallyClosed

variable {R S : Type*} [CommRing R] [CommRing S] [id : IsDomain R] [iic : IsIntegrallyClosed R]
variable {K : Type*} [CommRing K] [Algebra R K] [ifr : IsFractionRing R K]

instance : IsIntegralClosure R R K :=
  (isIntegrallyClosed_iff_isIntegralClosure K).mp iic

theorem isIntegral_iff {x : K} : IsIntegral R x ↔ ∃ y : R, algebraMap R K y = x :=
  IsIntegralClosure.isIntegral_iff
#align is_integrally_closed.is_integral_iff IsIntegrallyClosed.isIntegral_iff

theorem exists_algebraMap_eq_of_isIntegral_pow {x : K} {n : ℕ} (hn : 0 < n)
    (hx : IsIntegral R <| x ^ n) : ∃ y : R, algebraMap R K y = x :=
  isIntegral_iff.mp <| hx.of_pow hn
#align is_integrally_closed.exists_algebra_map_eq_of_is_integral_pow IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow

theorem exists_algebraMap_eq_of_pow_mem_subalgebra {K : Type*} [CommRing K] [Algebra R K]
    {S : Subalgebra R K} [IsIntegrallyClosed S] [IsFractionRing S K] {x : K} {n : ℕ} (hn : 0 < n)
    (hx : x ^ n ∈ S) : ∃ y : S, algebraMap S K y = x :=
  exists_algebraMap_eq_of_isIntegral_pow hn <| isIntegral_iff.mpr ⟨⟨x ^ n, hx⟩, rfl⟩
#align is_integrally_closed.exists_algebra_map_eq_of_pow_mem_subalgebra IsIntegrallyClosed.exists_algebraMap_eq_of_pow_mem_subalgebra

variable (R S K)

lemma _root_.IsIntegralClosure.of_isIntegrallyClosed
    [Algebra S R] [Algebra S K] [IsScalarTower S R K] (hRS : Algebra.IsIntegral S R) :
    IsIntegralClosure R S K := by
  refine ⟨IsLocalization.injective _ le_rfl, fun {x} ↦
    ⟨fun hx ↦ IsIntegralClosure.isIntegral_iff.mp (IsIntegral.tower_top (A := R) hx), ?_⟩⟩
  rintro ⟨y, rfl⟩
  exact IsIntegral.map (IsScalarTower.toAlgHom S R K) (hRS y)

variable {R}

theorem integralClosure_eq_bot_iff : integralClosure R K = ⊥ ↔ IsIntegrallyClosed R := by
  refine' eq_bot_iff.trans _
  constructor
  · rw [isIntegrallyClosed_iff K]
    intro h x hx
    exact Set.mem_range.mp (Algebra.mem_bot.mp (h hx))
  · intro h x hx
    rw [Algebra.mem_bot, Set.mem_range]
    exact isIntegral_iff.mp hx
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
variable [IsFractionRing R K]
variable {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]

-- Can't be an instance because you need to supply `K`.
theorem isIntegrallyClosedOfFiniteExtension [IsDomain R] [FiniteDimensional K L] :
    IsIntegrallyClosed (integralClosure R L) :=
  letI : IsFractionRing (integralClosure R L) L := isFractionRing_of_finite_extension K L
  (integralClosure_eq_bot_iff L).mp integralClosure_idem
#align integral_closure.is_integrally_closed_of_finite_extension integralClosure.isIntegrallyClosedOfFiniteExtension

end integralClosure
