/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Cusps

/-!
# Identities of ModularForms and SlashInvariantForms

Collection of useful identities of modular forms.
-/

noncomputable section

open ModularForm UpperHalfPlane Matrix CongruenceSubgroup Matrix.SpecialLinearGroup

namespace SlashInvariantForm

theorem vAdd_apply_of_mem_strictPeriods {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    {F : Type*} [FunLike F ℍ ℂ] [SlashInvariantFormClass F Γ k]
    (f : F) (τ : ℍ) {h : ℝ} (hH : h ∈ Γ.strictPeriods) :
    f (h +ᵥ τ) = f τ := by
  rw [Subgroup.mem_strictPeriods_iff] at hH
  have := congr_fun (slash_action_eqn f _ hH) τ
  -- maybe we need a simp lemma for `slash_upperRightHom_apply`?
  simp [slash_def, σ, denom] at this
  rw [← this]
  congr 1 with
  simp [coe_vadd, UpperHalfPlane.coe_smul, σ, GeneralLinearGroup.val_det_apply,
    num, denom, add_comm]

theorem vAdd_width_periodic (N : ℕ) (k n : ℤ) (f : SlashInvariantForm (Gamma N) k) (z : ℍ) :
    f (((N * n) : ℝ) +ᵥ z) = f z := by
  apply vAdd_apply_of_mem_strictPeriods
  simp only [Subgroup.mem_strictPeriods_iff, Subgroup.mem_map]
  refine ⟨⟨!![1, N * n; 0, 1], by simp⟩, by simp, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem T_zpow_width_invariant (N : ℕ) (k n : ℤ) (f : SlashInvariantForm (Gamma N) k) (z : ℍ) :
    f (((ModularGroup.T ^ (N * n))) • z) = f z := by
  rw [modular_T_zpow_smul z (N * n)]
  simpa only [Int.cast_mul, Int.cast_natCast] using vAdd_width_periodic N k n f z

end SlashInvariantForm
