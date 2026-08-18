/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic

/-!
# Discriminant of a quadratic algebra

This file introduces the discriminant of a quadratic algebra `QuadraticAlgebra R a b` (with the
convention `ω² = a + b·ω`), describes how it transforms under a change of generator, and derives,
over a field, a criterion for `QuadraticAlgebra K a b` to be a field.

## Main definitions

* `QuadraticAlgebra.discr`: the discriminant `discr a b = b ^ 2 + 4 * a`.

## Main results

* `QuadraticAlgebra.discr_changeGenerator`: the discriminant scales by `u ^ 2` under the change
  of generator `ω ↦ u • ω + k`.
* `QuadraticAlgebra.exists_sq_eq_iff_isSquare_discr`: over a ring with `2` invertible,
  `X ^ 2 - b * X - a` has a root iff `discr a b` is a square.
* `QuadraticAlgebra.isField_iff_not_isSquare_discr`: over a field with `2 ≠ 0`,
  `QuadraticAlgebra K a b` is a field iff `discr a b` is not a square.
-/

@[expose] public section

namespace QuadraticAlgebra

variable {R : Type*}

section discr

/-- The discriminant of the quadratic algebra `QuadraticAlgebra R a b`, that is, the
discriminant `b ^ 2 + 4 * a` of the polynomial `X ^ 2 - b * X - a`. -/
def discr [CommSemiring R] (a b : R) : R := b ^ 2 + 4 * a

theorem discr_def [CommSemiring R] (a b : R) : discr a b = b ^ 2 + 4 * a := rfl

/-- Under the change of generator `ω ↦ u • ω + k` (see `QuadraticAlgebra.changeGenerator`), the
discriminant is multiplied by `u ^ 2`. -/
theorem discr_changeGenerator [CommRing R] (a b u k : R) :
    discr (u ^ 2 * a - u * b * k - k ^ 2) (u * b + 2 * k) = u ^ 2 * discr a b := by
  rw [discr_def, discr_def]; ring

@[deprecated (since := "2026-08-14")] alias discr_map := discr_changeGenerator

/-- The discriminant is the square of the different `ω - star ω`. -/
theorem algebraMap_discr [CommRing R] (a b : R) :
    algebraMap R (QuadraticAlgebra R a b) (discr a b) = (ω - star ω) ^ 2 := by
  rw [discr_def]; ext <;> simp [sq] <;> ring

-- The `a = 1` case of `Mathlib.Algebra.QuadraticDiscriminant`, reproved to avoid its heavy
-- transitive import of `Mathlib.Order.Filter.AtTopBot.Field`.
/-- If `2` is invertible, the polynomial `X ^ 2 - b * X - a` has a root if and only if the
discriminant is a square. -/
theorem exists_sq_eq_iff_isSquare_discr [CommRing R] [Invertible (2 : R)] {a b : R} :
    (∃ r : R, r ^ 2 = a + b * r) ↔ IsSquare (discr a b) := by
  rw [isSquare_iff_exists_sq]
  have h2 := mul_invOf_self (2 : R)
  refine ⟨fun ⟨r, hr⟩ ↦ ⟨2 * r - b, by rw [discr_def]; grind⟩, fun ⟨s, hs⟩ ↦ ⟨⅟2 * (b + s), ?_⟩⟩
  rw [discr_def] at hs
  grind

end discr

section field

-- This `Fact (∀ r, r ^ 2 ≠ …)` instance is the bridge that lets the `Field` instance on
-- `QuadraticAlgebra K a b` fire from `¬ IsSquare (discr a b)` alone (the `b = 0` bridge from
-- `¬ IsSquare a` lives in `Basic.lean`).
instance {K : Type*} [Field K] {a b : K} [NeZero (2 : K)] [Fact (¬ IsSquare (discr a b))] :
    Fact (∀ r : K, r ^ 2 ≠ a + b * r) :=
  letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  ⟨not_exists.mp <| exists_sq_eq_iff_isSquare_discr.not.mpr Fact.out⟩

variable {K : Type*} [Field K]

/-- If `discr a b` is a square, `QuadraticAlgebra K a b` is not a field. -/
theorem not_isField_of_isSquare_discr [NeZero (2 : K)] {a b : K}
    (h : IsSquare (discr a b)) : ¬ IsField (QuadraticAlgebra K a b) := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  obtain ⟨r, hr⟩ := exists_sq_eq_iff_isSquare_discr.mpr h
  intro hfield
  let := hfield.toField
  have : (⟨r, -1⟩ : QuadraticAlgebra K a b) ∈ nonZeroDivisors (QuadraticAlgebra K a b) := by
    simp [mem_nonZeroDivisors_iff_ne_zero, QuadraticAlgebra.ext_iff]
  rw [← norm_mem_nonZeroDivisors_iff, show norm ⟨r, -1⟩ = 0 by rw [norm_def]; grind] at this
  exact zero_notMem_nonZeroDivisors this

/-- If `2 ≠ 0` in the field `K`, `QuadraticAlgebra K a b` is a field iff `discr a b` is
not a square. -/
theorem isField_iff_not_isSquare_discr [NeZero (2 : K)] {a b : K} :
    IsField (QuadraticAlgebra K a b) ↔ ¬ IsSquare (discr a b) := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  refine ⟨fun hfield h ↦ not_isField_of_isSquare_discr h hfield, fun h ↦ ?_⟩
  have : Fact (¬ IsSquare (discr a b)) := ⟨h⟩
  exact Field.toIsField (QuadraticAlgebra K a b)

-- The general bridge makes the `Field` instance inferable from `¬ IsSquare (discr a b)`
-- if `2 ≠ 0` in the field.
example {a b : ℚ} [Fact (¬ IsSquare (discr a b))] : Field (QuadraticAlgebra ℚ a b) := inferInstance

end field

end QuadraticAlgebra
