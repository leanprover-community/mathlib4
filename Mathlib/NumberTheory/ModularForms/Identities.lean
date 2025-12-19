/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.Cusps

/-!
# Identities of ModularForms and SlashInvariantForms

Collection of useful identities of modular forms.
-/

@[expose] public section

noncomputable section

open ModularForm UpperHalfPlane Matrix CongruenceSubgroup Matrix.SpecialLinearGroup

namespace SlashInvariantForm

theorem vAdd_apply_of_mem_strictPeriods {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    {F : Type*} [FunLike F ℍ ℂ] [SlashInvariantFormClass F Γ k]
    (f : F) (τ : ℍ) {h : ℝ} (hH : h ∈ Γ.strictPeriods) :
    f (h +ᵥ τ) = f τ := by
  rw [← congr_fun (slash_action_eqn f _ <| Γ.mem_strictPeriods_iff.mp hH) τ]
  suffices GeneralLinearGroup.upperRightHom h • τ = h +ᵥ τ by
    simp_rw [slash_def, this]
    simp [σ, denom, GeneralLinearGroup.val_det_apply, denom]
  ext
  simp [σ, num, denom, coe_vadd, UpperHalfPlane.coe_smul, num, add_comm]

theorem vAdd_width_periodic (N : ℕ) (k n : ℤ) (f : SlashInvariantForm (Gamma N) k) (z : ℍ) :
    f ((N * n : ℝ) +ᵥ z) = f z := by
  apply vAdd_apply_of_mem_strictPeriods
  simp [strictPeriods_Gamma, AddSubgroup.mem_zmultiples_iff, mul_comm]

theorem T_zpow_width_invariant (N : ℕ) (k n : ℤ) (f : SlashInvariantForm (Gamma N) k) (z : ℍ) :
    f (((ModularGroup.T ^ (N * n))) • z) = f z := by
  rw [modular_T_zpow_smul z (N * n)]
  simpa only [Int.cast_mul, Int.cast_natCast] using vAdd_width_periodic N k n f z

end SlashInvariantForm
