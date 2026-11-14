/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/

module

public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic

/-!
# Integers of valuative relations

This file introduces `ValuativeRel.integer` analog to `Valuation.integer`, the subring of elements
valuatively less or equal to 1.

TODO: existing usage of `(ValuativeRel.valuation R).integer` should be converted to
`ValuativeRel.integer R`, including those under notations `𝒪[K]` and such.
-/

public section

namespace ValuativeRel
variable {R : Type*} [Ring R] [ValuativeRel R]

variable (R) in
/-- The ring of integers under a given `ValuativeRel` is the subring of elements valuatively
less or equal to 1. -/
@[expose]
def integer : Subring R where
  carrier := { x | x ≤ᵥ 1 }
  one_mem' := by simp
  mul_mem' {x y} hx hy := by simpa using mul_vle_mul hx hy
  zero_mem' := by simp
  add_mem' {x y} hx hy := vle_add hx hy
  neg_mem' {x} hx := by simpa using hx

theorem mem_integer_iff {x : R} : x ∈ integer R ↔ x ≤ᵥ 1 := by rfl

theorem integer_eq_valuationInteger {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation R Γ₀) [v.Compatible] :
    integer R = v.integer := by
  ext x
  simp [mem_integer_iff, v.mem_integer_iff, v.vle_iff_le]

variable (R) in
@[simp]
theorem valuationInteger_valuation_eq_integer : (ValuativeRel.valuation R).integer = integer R :=
  (integer_eq_valuationInteger (ValuativeRel.valuation R)).symm

end ValuativeRel
