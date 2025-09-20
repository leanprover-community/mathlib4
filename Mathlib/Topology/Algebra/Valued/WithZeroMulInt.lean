/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.Topology.Algebra.Valued.ValuationTopology

/-!
# Topological results for integer-valued rings

This file contains topological results for valuation rings taking values in the
multiplicative integers with zero adjoined. These are useful for cases where there
is a `Valued R ℤₘ₀` instance but no canonical base with which to embed this into
`NNReal`.
-/

open Filter WithZero Set
open scoped Topology

namespace Valued
variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]

-- TODO: use ValuativeRel after https://github.com/leanprover-community/mathlib4/issues/26833
lemma tendsto_zero_pow_of_v_lt_one [MulArchimedean Γ₀] [Valued R Γ₀] {x : R} (hx : v x < 1) :
    Tendsto (fun n : ℕ ↦ x ^ n) atTop (𝓝 0) := by
  simp only [(hasBasis_nhds_zero _ _).tendsto_right_iff, mem_setOf_eq, map_pow, eventually_atTop,
    forall_const]
  intro y
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hx y
  refine ⟨n, fun m hm ↦ ?_⟩
  refine hn.trans_le' ?_
  exact pow_le_pow_right_of_le_one' hx.le hm

/-- In a `ℤᵐ⁰`-valued ring, powers of `x` tend to zero if `v x ≤ exp (-1)`. -/
lemma tendsto_zero_pow_of_le_exp_neg_one [Valued R ℤᵐ⁰] {x : R} (hx : v x ≤ exp (-1)) :
    Tendsto (fun n : ℕ ↦ x ^ n) atTop (𝓝 0) := by
  refine tendsto_zero_pow_of_v_lt_one (hx.trans_lt ?_)
  rw [← exp_zero, exp_lt_exp]
  simp

lemma exists_pow_lt_of_le_exp_neg_one [Valued R ℤᵐ⁰] {x : R} (hx : v x ≤ exp (-1)) (γ : ℤᵐ⁰ˣ) :
    ∃ n, v x ^ n < γ := by
  refine exists_pow_lt₀ (hx.trans_lt ?_) _
  rw [← exp_zero, exp_lt_exp]
  simp

end Valued
