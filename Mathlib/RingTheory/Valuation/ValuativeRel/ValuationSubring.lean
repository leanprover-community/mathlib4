/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/

module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.Valuation.ValuativeRel.Integer

/-!
# Valuation subrings and valuative relations

This file introduces `ValuativeRel.valuationSubring` analog to `Valuation.valuationSubring`. It
upgrades `ValuativeRel.integer` to a `ValuationSubring` for fields.

Furthermore, we show that the type `ValuativeRel R` and the type `ValuationSubring R` are
equivalent at `ValuativeRel.equivValuationSubring`.
-/

public section

namespace ValuativeRel
variable {K : Type*} [Field K] [ValuativeRel K]

variable (K) in
/-- The valuation subring associated to a `ValuativeRel`, consisting of elements valuatively
less or equal to 1. -/
@[expose]
def valuationSubring : ValuationSubring K where
  __ := integer K
  mem_or_inv_mem' x := by simpa [mem_integer_iff] using vle_one_or_inv_vle_one

theorem mem_valuationSubring_iff {x : K} : x ∈ valuationSubring K ↔ x ≤ᵥ 1 := by rfl

theorem valuationSubring_eq_valuationValuationSubring {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) [v.Compatible] :
    valuationSubring K = v.valuationSubring := by
  ext x
  simp [mem_valuationSubring_iff, v.mem_valuationSubring_iff, v.vle_iff_le]

variable (K) in
@[simp]
theorem valuationValuationSubring_valuation_eq_valuationSubring :
    (ValuativeRel.valuation K).valuationSubring = valuationSubring K :=
  (valuationSubring_eq_valuationValuationSubring (ValuativeRel.valuation K)).symm

/-- The `ValuativeRel` induced by a valuation subring. -/
@[instance_reducible, expose]
def ofValuationSubring (r : ValuationSubring K) : ValuativeRel K where
  vle x y := x = 0 ∨ y ≠ 0 ∧ x / y ∈ r
  vle_total x y := by
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    simpa [hx, hy] using r.mem_or_inv_mem (x / y)
  vle_trans {z y x} hxy hyz := by
    rcases hxy with hxy | hxy
    · simp [hxy]
    rcases hyz with hyz | hyz
    · simp [hxy.1] at hyz
    · simp [(div_mul_div_cancel₀ hxy.1) ▸ (mul_mem hxy.2 hyz.2), hyz.1]
  vle_add {x y z} hxy hyz := by aesop (add simp [add_div])
  mul_vle_mul_left {x y} hxy z := by
    by_cases h : z = 0
    · simp [h]
    · simpa [mul_div_mul_right _ _ h, h] using hxy
  vle_mul_cancel {x y z} hz hxy := by
    have h : z ≠ 0 := by simpa using hz
    simpa [mul_div_mul_right _ _ h, h] using hxy
  not_vle_one_zero := by simp
  vle_mul_comm {x y} := by by_cases h : x * y = 0 <;> simp [h, mul_comm y x]

omit [ValuativeRel K] in
theorem ofValuationSubring.vle_def (r : ValuationSubring K) {x y : K} :
    letI := ofValuationSubring r
    x ≤ᵥ y ↔ x = 0 ∨ y ≠ 0 ∧ x / y ∈ r := by
  rfl

omit [ValuativeRel K] in
theorem ofValuationSubring.vle_iff_exists (r : ValuationSubring K) {x y : K} :
    letI := ofValuationSubring r
    x ≤ᵥ y ↔ ∃ a ∈ r, a * y = x := by
  by_cases h : x = 0 <;> aesop (add simp [vle_def])

omit [ValuativeRel K] in
@[simp]
theorem ofValuation_valuationSubringValuation_eq_ofValuationSubring (r : ValuationSubring K) :
    ofValuation r.valuation = ofValuationSubring r := by
  ext x y
  let := ofValuation r.valuation
  simp [ofValuationSubring.vle_iff_exists, Valuation.vle_iff_le r.valuation,
    ValuationSubring.valuation_le_iff]

variable (K) in
/-- The correspondence between `ValuativeRel` and `ValuationSubring` of a given field. -/
@[expose, simps]
def equivValuationSubring : ValuativeRel K ≃ ValuationSubring K where
  toFun v := valuationSubring K
  invFun := ofValuationSubring
  left_inv v := by
    ext x y
    by_cases hy : y = 0
    · simp [ofValuationSubring.vle_def, hy]
    aesop (add simp [mem_valuationSubring_iff, ofValuationSubring.vle_def, div_vle_one_iff])
  right_inv r := by
    aesop (add simp [mem_valuationSubring_iff, ofValuationSubring.vle_def])

end ValuativeRel
