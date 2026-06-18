/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable

/-!
# Boundedness of `E2` at infinity

The weight 2 Eisenstein series `E2` is bounded at infinity. This follows
from its `q`-expansion `E2 z = 1 - 24 ∑_{n ≥ 1} σ₁(n) qⁿ`.
-/

open UpperHalfPlane hiding I
open Real Complex
open scoped ArithmeticFunction.sigma

@[expose] public noncomputable section

namespace EisensteinSeries

/-- The Eisenstein series `E2` is bounded at infinity. -/
theorem isBoundedAtImInfty_E2 : IsBoundedAtImInfty E2 := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  refine ⟨1 + 24 * ∑' n : ℕ+, ((n : ℕ) : ℝ) ^ 2 * Real.exp (-π) ^ (n : ℕ), 1, fun z hz => ?_⟩
  rw [E2_eq_tsum_cexp, show cexp (2 * ↑π * I * ↑z) = Function.Periodic.qParam 1 ↑z by
    simp [Function.Periodic.qParam]]
  set q : ℂ := Function.Periodic.qParam 1 ↑z
  have hr_lt_one : ‖Real.exp (-π)‖ < 1 := by
    simpa [Real.norm_of_nonneg (Real.exp_nonneg _), Real.exp_lt_one_iff] using Real.pi_pos
  have hq_norm : ‖q‖ ≤ Real.exp (-π) :=
    Function.Periodic.norm_qParam_le_of_one_half_le_im (by rw [UpperHalfPlane.coe_im]; linarith)
  have hbound : Summable fun n : ℕ+ ↦ ((n : ℕ) : ℝ) ^ 2 * Real.exp (-π) ^ (n : ℕ) :=
    (summable_pow_mul_geometric_of_norm_lt_one 2 hr_lt_one).comp_injective PNat.coe_injective
  have hterm : ∀ n : ℕ+, ‖σ 1 n * q ^ (n : ℕ)‖ ≤ n ^ 2 * Real.exp (-π) ^ (n : ℕ) := by
    intro n
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    gcongr
    have h : σ 1 n ≤ n ^ 2 := by simpa using ArithmeticFunction.sigma_le_pow_succ 1 n
    exact_mod_cast h
  have hnorm : Summable fun n : ℕ+ ↦ ‖σ 1 n * q ^ (n : ℕ)‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm hbound
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_one, norm_mul, Complex.norm_ofNat]
  gcongr
  exact (norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_le_tsum hterm hbound)

end EisensteinSeries

end
