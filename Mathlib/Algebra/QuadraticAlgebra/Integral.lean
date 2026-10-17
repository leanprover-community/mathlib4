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

* `QuadraticAlgebra.isIntegral_omega`: when `a` and `b` come from `R`, the generator `ω` is
  integral over `R`.
* `QuadraticAlgebra.isIntegral_iff`: an element of `QuadraticAlgebra K a b` is integral over `R`
  iff its trace and its norm lie in `R`.
* `QuadraticAlgebra.re_mem_range_of_im_mem_range`: if `z` is integral over `R` and `z.im` lies in
  `R`, then `z.re` also lies in `R`.
-/

public section

namespace QuadraticAlgebra

variable {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] {a b : K}

/-- The conjugate of an element integral over `R` is integral over `R`. -/
theorem isIntegral_star {z : QuadraticAlgebra K a b} (hz : IsIntegral R z) :
    IsIntegral R (star z) :=
  hz.map (starAlgEquiv.restrictScalars R)

@[simp]
theorem isIntegral_star_iff {z : QuadraticAlgebra K a b} :
    IsIntegral R (star z) ↔ IsIntegral R z :=
  ⟨fun h ↦ star_star z ▸ isIntegral_star h, isIntegral_star⟩

open Polynomial in
/-- An element whose trace and norm lie in `R` is integral over `R`. -/
theorem isIntegral_of_trace_mem_range_of_norm_mem_range {z : QuadraticAlgebra K a b}
    (ht : trace z ∈ Set.range (algebraMap R K)) (hn : norm z ∈ Set.range (algebraMap R K)) :
    IsIntegral R z := by
  obtain ⟨t, ht⟩ := ht
  obtain ⟨n, hn⟩ := hn
  refine ⟨X ^ 2 - C t * X + C n, by monicity!, ?_⟩
  simpa [IsScalarTower.algebraMap_apply R K (QuadraticAlgebra K a b), ht, hn,
    ← Algebra.smul_def] using sq_sub_trace_smul_add_norm_eq_zero z

/-- The generator `ω` is integral over `R`. -/
theorem isIntegral_omega {a b : R} :
    IsIntegral R (ω : QuadraticAlgebra K (algebraMap R K a) (algebraMap R K b)) :=
  isIntegral_of_trace_mem_range_of_norm_mem_range ⟨b, by simp⟩ ⟨-a, by simp [norm_def]⟩

variable [IsIntegrallyClosedIn R K]

/-- The trace of an element integral over `R` lies in `R`. -/
theorem trace_mem_range_of_isIntegral {z : QuadraticAlgebra K a b} (hz : IsIntegral R z) :
    trace z ∈ Set.range (algebraMap R K) :=
  IsIntegrallyClosedIn.isIntegral_iff.mp <|
    (algebraMap_trace_eq_add_star z ▸ hz.add (isIntegral_star hz)).tower_bot algebraMap_injective

/-- The norm of an element integral over `R` lies in `R`. -/
theorem norm_mem_range_of_isIntegral {z : QuadraticAlgebra K a b} (hz : IsIntegral R z) :
    norm z ∈ Set.range (algebraMap R K) :=
  IsIntegrallyClosedIn.isIntegral_iff.mp <|
    (algebraMap_norm_eq_mul_star z ▸ hz.mul (isIntegral_star hz)).tower_bot algebraMap_injective

/-- If `z` is integral over `R` and `z.im` lies in `R`, then `z.re` also lies in `R`. -/
theorem re_mem_range_of_im_mem_range {a b : R}
    {z : QuadraticAlgebra K (algebraMap R K a) (algebraMap R K b)} (h : IsIntegral R z)
    (him : z.im ∈ Set.range (algebraMap R K)) : z.re ∈ Set.range (algebraMap R K) := by
  obtain ⟨m, hm⟩ := him
  have : IsIntegral R (z - m • ω) := h.sub (isIntegral_omega.smul _)
  rwa [← re_smul_add_im_smul z, ← hm, algebraMap_smul, add_sub_cancel_right,
    ← Algebra.algebraMap_eq_smul_one, ← IsScalarTower.coe_toAlgHom' R K,
    isIntegral_algHom_iff _ algebraMap_injective, IsIntegrallyClosedIn.isIntegral_iff] at this

/-- An element of `QuadraticAlgebra K a b` is integral over `R` iff its trace and its norm lie
in `R`. -/
theorem isIntegral_iff {z : QuadraticAlgebra K a b} :
    IsIntegral R z ↔
      trace z ∈ Set.range (algebraMap R K) ∧ norm z ∈ Set.range (algebraMap R K) :=
  ⟨fun h ↦ ⟨trace_mem_range_of_isIntegral h, norm_mem_range_of_isIntegral h⟩,
    fun h ↦ isIntegral_of_trace_mem_range_of_norm_mem_range h.1 h.2⟩

end QuadraticAlgebra
