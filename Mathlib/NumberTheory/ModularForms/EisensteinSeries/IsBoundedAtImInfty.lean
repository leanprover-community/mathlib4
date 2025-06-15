/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Mathlib.NumberTheory.ModularForms.Identities

/-!
# Boundedness of Eisenstein series

We show that Eisenstein series of weight `k` and level `Γ(N)` with congruence condition
`a : Fin 2 → ZMod N` are bounded at infinity.

## Outline of argument

We need to bound the value of the Eisenstein series (acted on by `A : SL(2,ℤ)`)
at a given point `z` in the upper half plane. Since these are modular forms of level `Γ(N)`,
it suffices to prove this for `z ∈ verticalStrip N z.im`.

We can then, first observe that the slash action just changes our `a` to `(a ᵥ* A)` and
we then use our bounds for Eisenstein series in these vertical strips to get the result.
-/

noncomputable section

open ModularForm UpperHalfPlane  Matrix SlashInvariantForm CongruenceSubgroup

open scoped MatrixGroups

namespace EisensteinSeries

lemma summable_norm_eisSummand {k : ℤ} (hk : 3 ≤ k) (z : ℍ) :
    Summable fun (x : Fin 2 → ℤ) ↦ ‖(eisSummand k x z)‖ := by
  have hk' : (2 : ℝ) < k := by norm_cast
  apply ((summable_one_div_norm_rpow hk').mul_left <| r z ^ (-k : ℝ)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _)
  intro b
  simp only [eisSummand, norm_zpow]
  exact_mod_cast summand_bound z (show 0 ≤ (k : ℝ) by positivity) b

/-- The norm of the restricted sum is less than the full sum of the norms. -/
lemma norm_le_tsum_norm (N : ℕ) (a : Fin 2 → ZMod N) (k : ℤ) (hk : 3 ≤ k) (z : ℍ) :
    ‖eisensteinSeries a k z‖  ≤ ∑' (x : Fin 2 → ℤ), ‖eisSummand k x z‖ := by
  simp_rw [eisensteinSeries]
  apply le_trans (norm_tsum_le_tsum_norm ((summable_norm_eisSummand hk z).subtype _))
    (Summable.tsum_subtype_le (fun (x : Fin 2 → ℤ) ↦ ‖(eisSummand k x z)‖) _ (fun _ ↦ norm_nonneg _)
      (summable_norm_eisSummand hk z))

@[deprecated (since := "2025-02-17")] alias abs_le_tsum_abs := norm_le_tsum_norm

/-- Eisenstein series are bounded at infinity. -/
theorem isBoundedAtImInfty_eisensteinSeries_SIF {N : ℕ+} (a : Fin 2 → ZMod N) {k : ℤ} (hk : 3 ≤ k)
    (A : SL(2, ℤ)) : IsBoundedAtImInfty ((eisensteinSeries_SIF a k).toFun ∣[k] A) := by
  simp_rw [UpperHalfPlane.isBoundedAtImInfty_iff, eisensteinSeries_SIF] at *
  refine ⟨∑'(x : Fin 2 → ℤ), r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-k) * ‖x‖ ^ (-k), 2, ?_⟩
  intro z hz
  obtain ⟨n, hn⟩ := (ModularGroup_T_zpow_mem_verticalStrip z N.2)
  rw [eisensteinSeries_slash_apply, ← eisensteinSeries_SIF_apply,
    ← T_zpow_width_invariant N k n (eisensteinSeries_SIF (a ᵥ* A) k) z]
  apply le_trans (norm_le_tsum_norm N (a ᵥ* A) k hk _)
  have hk' : (2 : ℝ) < k := by norm_cast
  apply (summable_norm_eisSummand hk _).tsum_le_tsum _
  · exact_mod_cast (summable_one_div_norm_rpow hk').mul_left <| r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-k)
  · intro x
    simp_rw [eisSummand, norm_zpow]
    exact_mod_cast
      summand_bound_of_mem_verticalStrip (lt_trans two_pos hk').le x two_pos
      (verticalStrip_anti_right N hz hn)

end EisensteinSeries
