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

public section

noncomputable section

open ModularForm UpperHalfPlane Matrix CongruenceSubgroup Matrix.SpecialLinearGroup MatrixGroups

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

lemma slash_S_apply (f : ℍ → ℂ) (k : ℤ) (z : ℍ) :
    (f ∣[k] ModularGroup.S) z = f (.mk _ z.im_inv_neg_coe_pos) * z ^ (-k) := by
  rw [SL_slash_apply, modular_S_smul]
  simp [ModularGroup.S, denom]

/-- The action of `T^j` on a function `g : ℍ → ℂ` via the slash action of weight `k` is the
shift `g((j : ℝ) +ᵥ τ)`. -/
lemma slash_T_zpow_apply_general (k : ℤ) (j : ℤ) (g : ℍ → ℂ) (τ : ℍ) :
    (g ∣[k] ((ModularGroup.T : SL(2, ℤ))^j : GL (Fin 2) ℝ)) τ =
      g ((j : ℝ) +ᵥ τ) := by
  have hgl : ((ModularGroup.T : SL(2, ℤ))^j : GL (Fin 2) ℝ) =
      Matrix.SpecialLinearGroup.mapGL ℝ ((ModularGroup.T)^j : SL(2, ℤ)) := by
    change (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T)^j = _
    rw [← map_zpow]
  rw [hgl]
  change (g ∣[k] ((ModularGroup.T)^j : SL(2, ℤ))) τ = _
  rw [SL_slash_apply, modular_T_zpow_smul]
  have hdenom : denom (((ModularGroup.T)^j : SL(2, ℤ)) : GL (Fin 2) ℝ) (τ : ℂ) = 1 := by
    have hcoe : (((((ModularGroup.T)^j : SL(2, ℤ)) : GL (Fin 2) ℝ)) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        ((((ModularGroup.T)^j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.castRingHom ℝ) :=
      rfl
    change ((((((ModularGroup.T)^j : SL(2, ℤ)) : GL (Fin 2) ℝ)) :
        Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) * τ +
        ((((((ModularGroup.T)^j : SL(2, ℤ)) : GL (Fin 2) ℝ)) :
          Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) = 1
    rw [hcoe, ModularGroup.coe_T_zpow]
    simp
  rw [hdenom, one_zpow, mul_one]

section Generators

theorem slash_action_generators {f : ℍ → ℂ} {Γ : Subgroup (GL (Fin 2) ℝ)}
    {s : Set (GL (Fin 2) ℝ)} (hΓ : Γ = Subgroup.closure s) {k : ℤ} :
    (∀ γ ∈ Γ, f ∣[k] γ = f) ↔ (∀ γ ∈ s, f ∣[k] γ = f) := by
  constructor <;> intro h γ hγ
  · exact h γ (hΓ ▸ Subgroup.mem_closure_of_mem hγ)
  · apply Subgroup.closure_induction (p := fun γ _ ↦ f ∣[k] γ = f) h (by simp)
    · simp +contextual [SlashAction.slash_mul]
    · intro x hx hf
      rw [← hf, ← SlashAction.slash_mul]
      simp [hf]
    · simpa [← hΓ]

end Generators

end SlashInvariantForm
