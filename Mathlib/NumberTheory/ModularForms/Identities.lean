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

open ModularForm UpperHalfPlane Matrix CongruenceSubgroup

namespace SlashInvariantForm

/- TODO: Once we have cusps, do this more generally, same below. -/
theorem vAdd_width_periodic (N : ℕ) (k n : ℤ) (f : SlashInvariantForm (Gamma N) k) (z : ℍ) :
    f (((N * n) : ℝ) +ᵥ z) = f z := by
  norm_cast
  rw [← modular_T_zpow_smul z (N * n)]
  have := (ModularGroup_T_pow_mem_Gamma N (N * n) (Int.dvd_mul_right N n))
  convert slash_action_eqn' f (Subgroup.mem_map_of_mem _ this) z
  rw [SpecialLinearGroup.mapGL_coe_matrix, SpecialLinearGroup.map_apply_coe,
    ModularGroup.coe_T_zpow (N * n)]
  simp

theorem T_zpow_width_invariant (N : ℕ) (k n : ℤ) (f : SlashInvariantForm (Gamma N) k) (z : ℍ) :
    f (((ModularGroup.T ^ (N * n))) • z) = f z := by
  rw [modular_T_zpow_smul z (N * n)]
  simpa only [Int.cast_mul, Int.cast_natCast] using vAdd_width_periodic N k n f z

end SlashInvariantForm
