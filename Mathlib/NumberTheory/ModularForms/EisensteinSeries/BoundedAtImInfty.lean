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

lemma eisSummand_bound (k : ℤ) (hk : 3 ≤ k) (z : ℍ) (b : Fin 2 → ℤ) :
    Complex.abs (eisSummand k b z) ≤
    ((r z ^ k) * max (Int.natAbs (b 0) : ℝ) (Int.natAbs (b 1)) ^ k)⁻¹ := by
  have hk0 : 0 ≤ k := by omega
  lift k to ℕ using hk0
  simpa only [zpow_natCast, Fin.isValue, _root_.mul_inv_rev, Nat.cast_max] using
    (eisSummand_is_bounded_on_box (k := k) (max (b 0).natAbs (b 1).natAbs) z b (Int.ofNat_zero_le k)
      (by simp))

lemma summable_lem (k : ℤ) (hk : 3 ≤ k) (z : ℍ) : Summable fun (x : Fin 2 → ℤ) =>
    Complex.abs (eisSummand k x z) := by
  apply (summable_upper_bound hk z).of_nonneg_of_le (fun _ => Complex.abs.nonneg _)
    (eisSummand_bound k hk z)

lemma abs_le_tsum_abs (N : ℕ) (a : Fin 2 → ZMod N) (k : ℤ) (hk : 3 ≤ k) (z : ℍ):
    Complex.abs ((((eisensteinSeries a k))) z) ≤ ∑' (x : Fin 2 → ℤ),
      Complex.abs (eisSummand k x z) := by
  simp_rw [← Complex.norm_eq_abs, eisensteinSeries]
  apply le_trans (norm_tsum_le_tsum_norm ?_) (tsum_subtype_le (fun (x : Fin 2 → ℤ) =>
      ‖(eisSummand k x z)‖) _ (fun _ => norm_nonneg _) (summable_lem k hk z))
  apply (summable_lem k hk z).subtype

theorem eisensteinSeries_IsBoundedAtImInfty (N : ℕ+) (a : Fin 2 → ZMod N) (k : ℤ) (hk : 3 ≤ k)
    (A : SL(2, ℤ)) : IsBoundedAtImInfty ((eisensteinSeries_SIF a k).toFun ∣[(k : ℤ)] A) := by
    simp_rw [UpperHalfPlane.bounded_mem, eisensteinSeries_SIF] at *
    refine ⟨∑'(x : Fin 2 → ℤ),
      (r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ k * (max (x 0).natAbs (x 1).natAbs : ℝ) ^ k)⁻¹, 2, ?_⟩
    intro z hz
    obtain ⟨n, hn⟩ := (ModularGroup_T_zpow_mem_verticalStrip z N (by simp))
    rw [eisensteinSeries_slash_apply, ← eisensteinSeries_SIF_apply,
      ← SIF_lvl_N_periodic N k (eisensteinSeries_SIF (a ᵥ* A) k) z n]
    let Z := ((ModularGroup.T ^ ((N : ℤ) * n))) • z
    apply le_trans (abs_le_tsum_abs N _ _ hk (Z))
    apply tsum_le_tsum _ ((summable_upper_bound hk Z).of_nonneg_of_le
      (fun _ => Complex.abs.nonneg _) (eisSummand_bound k hk Z)) (summable_upper_bound hk _)
    intro x
    apply le_trans ((eisSummand_bound k hk Z x))
    simp only [Fin.isValue, _root_.mul_inv_rev]
    gcongr
    · apply zpow_pos_of_pos (r_pos _)
    · have hk0 : 0 ≤ k := by linarith
      lift k to ℕ using hk0
      push_cast
      apply pow_le_pow_left (r_pos _).le
      apply r_lower_bound_on_verticalStrip (A := N) (B := 2)
          (z:= ⟨Z, (verticalStrip_mem_le (N : ℕ) 2 z.im hz) hn⟩)
