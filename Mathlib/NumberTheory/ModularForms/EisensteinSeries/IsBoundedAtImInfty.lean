/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.NumberTheory.ModularForms.Identities

/-!
# Boundedness of Eisenstein series

We show that Eisenstein series of weight `k` and level `Γ(N)` with congruence condition
`a : Fin 2 → ZMod N` are bounded at infinity.
-/

noncomputable section

open ModularForm EisensteinSeries UpperHalfPlane Set Filter Function Complex Matrix
  SlashInvariantForm

open scoped Topology BigOperators Nat Classical MatrixGroups

namespace EisensteinSeries

lemma summable_lem (k : ℤ) (hk : 3 ≤ k) (z : ℍ) : Summable fun (x : Fin 2 → ℤ) =>
    Complex.abs (eisSummand k x z) := by
  have hk' : (2 : ℝ) < k := by norm_cast
  apply ((summable_one_div_norm_rpow hk').mul_left <| r z ^ (-k : ℝ)).of_nonneg_of_le
    (fun _ => Complex.abs.nonneg _)
  intro b
  rw [eisSummand]
  simp only [Fin.isValue, one_div, map_inv₀, map_zpow₀]
  rw [← inv_zpow, inv_zpow']
  have hk0 : 0 ≤ (k : ℝ) := by norm_cast; omega
  have := summand_bound z hk0 b
  norm_cast at *

lemma abs_le_tsum_abs (N : ℕ) (a : Fin 2 → ZMod N) (k : ℤ) (hk : 3 ≤ k) (z : ℍ):
    Complex.abs ((((eisensteinSeries a k))) z) ≤ ∑' (x : Fin 2 → ℤ),
      Complex.abs (eisSummand k x z) := by
  simp_rw [← Complex.norm_eq_abs, eisensteinSeries]
  apply le_trans (norm_tsum_le_tsum_norm ?_) (tsum_subtype_le (fun (x : Fin 2 → ℤ) =>
      ‖(eisSummand k x z)‖) _ (fun _ => norm_nonneg _) (summable_lem k hk z))
  apply (summable_lem k hk z).subtype

theorem eisensteinSeries_IsBoundedAtImInfty {N : ℕ+} (a : Fin 2 → ZMod N) (k : ℤ) (hk : 3 ≤ k)
    (A : SL(2, ℤ)) : IsBoundedAtImInfty ((eisensteinSeries_SIF a k).toFun ∣[(k : ℤ)] A) := by
    simp_rw [UpperHalfPlane.bounded_mem, eisensteinSeries_SIF] at *
    refine ⟨∑'(x : Fin 2 → ℤ), (r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-k)) * ‖x‖ ^ (-k), 2, ?_⟩
    intro z hz
    obtain ⟨n, hn⟩ := (ModularGroup_T_zpow_mem_verticalStrip z N N.2)
    rw [eisensteinSeries_slash_apply, ← eisensteinSeries_SIF_apply,
      ← SIF_lvl_N_periodic N k (eisensteinSeries_SIF (a ᵥ* A) k) z n]
    let Z := ((ModularGroup.T ^ ((N : ℤ) * n))) • z
    apply le_trans (abs_le_tsum_abs N _ _ hk (Z))
    apply tsum_le_tsum _ (summable_lem k hk _)
    · have hk' : (2 : ℝ) < k := by norm_cast
      have := (summable_one_div_norm_rpow hk').mul_left <| r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-k : ℝ)
      norm_cast at this
    · intro x
      have hk0 : 0 ≤ (k : ℝ) := by norm_cast; omega
      have := summand_bound Z hk0 x
      simp only [eisSummand, Fin.isValue, one_div, map_inv₀, map_zpow₀, zpow_neg, ge_iff_le]
      rw [← inv_zpow, inv_zpow']
      simp_rw [ ←  Int.cast_neg,   Real.rpow_intCast] at this
      apply le_trans this
      simp only [zpow_neg]
      gcongr
      · apply zpow_pos_of_pos (r_pos _)
      · have hk0 : 0 ≤ k := by linarith
        lift k to ℕ using hk0
        apply pow_le_pow_left (r_pos _).le
        apply r_lower_bound_on_verticalStrip (A := N) (B := 2) _ _
          ((verticalStrip_anti_right (N : ℕ) hz) hn)
