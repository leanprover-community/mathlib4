/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
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
variable {R : Type*} [Ring R] [Valued R ℤᵐ⁰] {x : R}

/-- In a `ℤᵐ⁰`-valued ring, powers of `x` tend to zero if `v x ≤ exp (-1)`. -/
lemma tendsto_zero_pow_of_le_exp_neg_one (hx : v x ≤ exp (-1)) :
    Tendsto (fun n : ℕ ↦ x ^ n) atTop (𝓝 0) := by
  simp only [(hasBasis_nhds_zero _ _).tendsto_right_iff, mem_setOf_eq, map_pow, eventually_atTop,
    forall_const, logEquiv.forall_congr_left, logEquiv_symm, coe_expEquiv_apply]
  obtain hvx | hvx := eq_or_ne (v x) 0
  · exact fun _ ↦ ⟨1, fun n hn ↦ by rw [hvx, zero_pow (by omega)]; exact exp_pos⟩
  refine fun γ ↦ ⟨(1 - γ).toNat, fun b hb ↦ lt_exp_of_log_lt ?_⟩
  calc
        (v x ^ b).log
    _ = b * (v x).log := by simp [log_pow]
    _ ≤ b * (-1) := by gcongr; simpa [log_le_iff_le_exp hvx]
    _ < γ := by omega

lemma exists_pow_lt_of_le_exp_neg_one (hx : v x ≤ exp (-1)) (γ : ℤᵐ⁰ˣ) : ∃ n, v x ^ n < γ := by
  let ⟨n, hn⟩ := eventually_atTop.1 <| (hasBasis_nhds_zero _ _ |>.tendsto_right_iff).1
    (tendsto_zero_pow_of_le_exp_neg_one hx) γ trivial
  exact ⟨n, by simpa using hn n le_rfl⟩

end Valued
