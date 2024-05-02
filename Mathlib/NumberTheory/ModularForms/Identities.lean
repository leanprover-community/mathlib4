/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Indentities of ModularForms and SlahInvariantForms
Collection of useful indentities of modular forms.
-/

noncomputable section

open ModularForm UpperHalfPlane Matrix

namespace SlashInvariantForm

theorem SIF_lvl_N_periodic (N : ℕ) (k : ℤ) (f : SlashInvariantForm (Gamma N) k) :
    ∀ (z : ℍ) (n : ℤ), f (((ModularGroup.T ^ (N * n))) • z) = f z := by
  intro z n
  have Hn := (ModularGroup_T_pow_mem_Gamma N (N * n) (by simp))
  simp only [zpow_natCast, Int.natAbs_ofNat] at Hn
  convert (SlashInvariantForm.slash_action_eqn' k (Gamma N) f ⟨((ModularGroup.T ^ (N * n))), Hn⟩ z)
  unfold SpecialLinearGroup.coeToGL
  simp only [Fin.isValue, ModularGroup.coe_T_zpow (N * n), of_apply, cons_val', cons_val_zero,
    empty_val', cons_val_fin_one, cons_val_one, head_fin_const, Int.cast_zero, zero_mul, head_cons,
    Int.cast_one, zero_add, one_zpow, one_mul]
