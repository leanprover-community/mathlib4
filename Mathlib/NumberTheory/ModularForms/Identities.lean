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

open ModularForm UpperHalfPlane Matrix MatrixGroups ModularGroup

namespace SlashInvariantFormClass

variable {Γ : Subgroup SL(2, ℤ)} {F : Type*} (f : F) (k : ℤ)
  [FunLike F ℍ ℂ] [hF : SlashInvariantFormClass F Γ k] {n : ℤ}

include hF -- necessary because `k` is not inferrable from the statements

theorem vAdd_width_periodic (hn : ↑Γ.width ∣ n) (τ : ℍ) :
    f ((n : ℝ) +ᵥ τ) = f τ := by
  rw [← modular_T_zpow_smul τ, SlashInvariantForm.slash_action_eqn' (k := k) f
    (Γ.T_zpow_mem_iff.mpr hn)]
  simp [ModularGroup.coe_T_zpow]

theorem T_zpow_width_invariant (hn : ↑Γ.width ∣ n) (τ : ℍ) :
    f (ModularGroup.T ^ n • τ) = f τ := by
  simpa [-sl_moeb, modular_T_zpow_smul] using vAdd_width_periodic f k hn τ

end SlashInvariantFormClass
