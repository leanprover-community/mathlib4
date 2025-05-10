/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-! # Topological results for integer-valued rings

This file contains topological results for valuation rings taking values in the
multiplicative integers with zero adjoined. These are useful for cases where there
is a `Valued K ℤₘ₀` instance but no canonical base with which to embed this into
`NNReal`.
-/

open Multiplicative WithZero

open scoped Multiplicative Topology

namespace Valued.WithZeroMulInt

open Set Filter in
/-- In a `ℤₘ₀`-valued ring, powers of `x` tend to zero if `v x ≤ ofAdd (-1 : ℤ)`. -/
theorem tendsto_zero_pow_of_le_neg_one {K : Type*} [Ring K] [Valued K ℤₘ₀]
    {x : K} (hx : v x ≤ ofAdd (-1 : ℤ)) :
    Tendsto (fun (n : ℕ) => x ^ n) atTop (𝓝 0) := by
  simp only [(hasBasis_nhds_zero _ _).tendsto_right_iff, mem_setOf_eq, map_pow, eventually_atTop]
  have h_lt : ofAdd (-1 : ℤ) < (1 : ℤₘ₀) := by
    rw [← coe_one, coe_lt_coe, ← ofAdd_zero, ofAdd_lt]; linarith
  intro γ _
  by_cases hγ : γ.val ≤ 1
  · let m := - toAdd (unitsWithZeroEquiv γ) + 1 |>.toNat
    refine ⟨m, fun b hb => lt_of_le_of_lt
      (pow_le_pow_of_le_one zero_le' (le_trans hx <| le_of_lt h_lt) hb) ?_⟩
    replace hγ : 0 ≤ -toAdd (unitsWithZeroEquiv γ) + 1 := by
      rw [← coe_unitsWithZeroEquiv_eq_units_val, ← coe_one, coe_le_coe, ← toAdd_le, toAdd_one] at hγ
      linarith
    apply lt_of_le_of_lt <| pow_le_pow_left₀ zero_le' hx m
    rw [← coe_unitsWithZeroEquiv_eq_units_val, ← coe_pow, coe_lt_coe, ← ofAdd_nsmul,
      nsmul_eq_mul, Int.toNat_of_nonneg hγ, mul_neg, mul_one, neg_add_rev, neg_neg, ofAdd_add,
      ofAdd_neg, ofAdd_toAdd, mul_lt_iff_lt_one_right', Left.inv_lt_one_iff, ← ofAdd_zero, ofAdd_lt]
    exact zero_lt_one
  · refine ⟨1, fun b hb => lt_of_le_of_lt
      (pow_le_pow_of_le_one zero_le' (le_trans hx <| le_of_lt h_lt) hb) ?_⟩
    apply pow_one (v x) ▸ lt_trans (lt_of_le_of_lt hx h_lt) (lt_of_not_le hγ)

open Filter in
theorem exists_pow_lt_of_le_neg_one {K : Type*} [Ring K] [Valued K ℤₘ₀]
    {x : K} (hx : v x ≤ ofAdd (-1 : ℤ)) (γ : ℤₘ₀ˣ) :
    ∃ n, v x ^ n < γ := by
  simp_rw [← map_pow]
  let ⟨n, hn⟩ := eventually_atTop.1 <|
     ((hasBasis_nhds_zero _ _).tendsto_right_iff ).1 (tendsto_zero_pow_of_le_neg_one hx) γ trivial
  use n
  convert Set.mem_setOf_eq ▸ hn n le_rfl

end Valued.WithZeroMulInt
