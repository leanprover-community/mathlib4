/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import Mathlib.Tactic.ComputeDegree

/-!
# Integral elements of quadratic algebras

Let `R` be a commutative ring and `K` a commutative `R`-algebra in which `R` is integrally closed
(for instance an integrally closed domain and its fraction field). We characterize the elements of
`QuadraticAlgebra K a b` that are integral over `R`.

## Main results

* `QuadraticAlgebra.isIntegral_omega`: when `a` and `b` lie in `R`, the generator `ω` is
  integral over `R`.
* `QuadraticAlgebra.re_mem_range_of_im_mem_range`: if `a` and `b` lie in `R`, `z` is integral over
  `R` and `z.im` lies in `R`, then `z.re` also lies in `R`.
* `QuadraticAlgebra.isIntegral_iff`: an element of `QuadraticAlgebra K a b` is integral over `R`
  iff its trace and its norm lie in `R`.
-/

public section

namespace QuadraticAlgebra

variable {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] {a b : K}
  {z : QuadraticAlgebra K a b}

@[simp]
theorem isIntegral_star_iff :
    IsIntegral R (star z) ↔ IsIntegral R z :=
  isIntegral_algEquiv (starAlgEquiv.restrictScalars R) (x := z)

open Polynomial in
/-- An element whose trace and norm lie in `R` is integral over `R`. -/
theorem isIntegral_of_trace_mem_range_of_norm_mem_range (ht : trace z ∈ Set.range (algebraMap R K))
    (hn : norm z ∈ Set.range (algebraMap R K)) :
    IsIntegral R z := by
  obtain ⟨t, ht⟩ := ht
  obtain ⟨n, hn⟩ := hn
  refine ⟨X ^ 2 - C t * X + C n, by monicity!, ?_⟩
  simp [IsScalarTower.algebraMap_apply R K (QuadraticAlgebra K a b), ht, hn,
    ← Algebra.smul_def, sq_sub_trace_smul_add_norm_eq_zero]

/-- When `a` and `b` lie in `R`, the generator `ω` is integral over `R`. -/
theorem isIntegral_omega (ha : a ∈ Set.range (algebraMap R K))
    (hb : b ∈ Set.range (algebraMap R K)) :
    IsIntegral R (ω : QuadraticAlgebra K a b) := by
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  exact isIntegral_of_trace_mem_range_of_norm_mem_range ⟨b, by simp⟩ ⟨-a, by simp [norm_def]⟩

variable [IsIntegrallyClosedIn R K]

/-- The trace of an element integral over `R` lies in `R`. -/
theorem trace_mem_range_of_isIntegral (hz : IsIntegral R z) :
    trace z ∈ Set.range (algebraMap R K) :=
  IsIntegrallyClosedIn.isIntegral_iff.mp <|
    (algebraMap_trace_eq_add_star z ▸ hz.add (isIntegral_star_iff.mpr hz)).tower_bot
      algebraMap_injective

/-- The norm of an element integral over `R` lies in `R`. -/
theorem norm_mem_range_of_isIntegral (hz : IsIntegral R z) :
    norm z ∈ Set.range (algebraMap R K) :=
  IsIntegrallyClosedIn.isIntegral_iff.mp <|
    (algebraMap_norm_eq_mul_star z ▸ hz.mul (isIntegral_star_iff.mpr hz)).tower_bot
      algebraMap_injective

/-- If `a` and `b` lie in `R`, `z` is integral over `R` and `z.im` lies in `R`, then `z.re` also
lies in `R`. -/
theorem re_mem_range_of_im_mem_range (ha : a ∈ Set.range (algebraMap R K))
    (hb : b ∈ Set.range (algebraMap R K)) (h : IsIntegral R z)
    (him : z.im ∈ Set.range (algebraMap R K)) : z.re ∈ Set.range (algebraMap R K) := by
  obtain ⟨m, hm⟩ := him
  have : IsIntegral R (z - m • ω) := h.sub ((isIntegral_omega ha hb).smul _)
  rwa [← re_smul_add_im_smul z, ← hm, algebraMap_smul, add_sub_cancel_right,
    ← Algebra.algebraMap_eq_smul_one, ← IsScalarTower.coe_toAlgHom' R K,
    isIntegral_algHom_iff _ algebraMap_injective, IsIntegrallyClosedIn.isIntegral_iff] at this

/-- An element of `QuadraticAlgebra K a b` is integral over `R` iff its trace and its norm lie
in `R`. -/
theorem isIntegral_iff :
    IsIntegral R z ↔
      trace z ∈ Set.range (algebraMap R K) ∧ norm z ∈ Set.range (algebraMap R K) :=
  ⟨fun h ↦ ⟨trace_mem_range_of_isIntegral h, norm_mem_range_of_isIntegral h⟩,
    fun h ↦ isIntegral_of_trace_mem_range_of_norm_mem_range h.1 h.2⟩

end QuadraticAlgebra
