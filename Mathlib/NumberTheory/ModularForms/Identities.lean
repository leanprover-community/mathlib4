/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Identities of ModularForms and SlashInvariantForms

Collection of useful identities of modular forms.
-/

noncomputable section

open ModularForm UpperHalfPlane Matrix CongruenceSubgroup Matrix.SpecialLinearGroup

namespace SlashInvariantForm

/- TODO: Once we have cusps, do this more generally, same below. -/
theorem vAdd_width_periodic (N : ℕ) (k n : ℤ) (f : SlashInvariantForm (Gamma N) k) (z : ℍ) :
    f (((N * n) : ℝ) +ᵥ z) = f z := by
  norm_cast
  rw [← modular_T_zpow_smul z (N * n), MulAction.compHom_smul_def, slash_action_eqn']
  · simp [-map_zpow, ModularGroup.coe_T_zpow (N * n)]
  · simpa using Subgroup.mem_map_of_mem (mapGL ℝ) <|
      ModularGroup_T_pow_mem_Gamma _ _ (Int.dvd_mul_right N n)

theorem T_zpow_width_invariant (N : ℕ) (k n : ℤ) (f : SlashInvariantForm (Gamma N) k) (z : ℍ) :
    f (((ModularGroup.T ^ (N * n))) • z) = f z := by
  rw [modular_T_zpow_smul z (N * n)]
  simpa only [Int.cast_mul, Int.cast_natCast] using vAdd_width_periodic N k n f z

lemma slash_S_apply (f : ℍ → ℂ) (k : ℤ) (z : ℍ) :
    (f ∣[k] ModularGroup.S) z = f (UpperHalfPlane.mk (-z)⁻¹ z.im_inv_neg_coe_pos) * z ^ (-k) := by
  rw [SL_slash_apply, denom, UpperHalfPlane.modular_S_smul]
  simp [ModularGroup.S]

end SlashInvariantForm
