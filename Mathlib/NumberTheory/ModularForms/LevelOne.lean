/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Level one modular forms

This file contains results specific to modular forms of level one, ie. modular forms for `SL(2, ℤ)`.

TODO: Add finite dimisionality of these spaces of modular forms.

-/

open UpperHalfPlane ModularGroup SlashInvariantForm
local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R
local notation  "Γ(" n ")"  => CongruenceSubgroup.Gamma n

/--The map from `SL(2, ℤ)` to `Γ(1)`. Its preferable to work with this, since levels of modular
forms are terms of type Subgroup `SL(2, ℤ)`. -/
def coe1 : SL(2, ℤ) → Γ(1) :=
  fun g => ⟨↑g, by simp [CongruenceSubgroup.Gamma_one_top]⟩

instance : Coe SL(2, ℤ) Γ(1) := ⟨coe1⟩

lemma coe_smul_eq_smul {g : SL(2, ℤ)} {τ : ℍ} : (g : Γ(1)) • τ = (g • τ) := by
  simp only [coe1, Subgroup.mk_smul, ModularGroup.sl_moeb]

@[simp]
lemma denom_coe1_eq_denom {g : SL(2, ℤ)} {τ : ℍ} : denom (g : Γ(1)) τ = denom g τ := by
  simp only [denom, coe1, Fin.isValue, ModularGroup.coe'_apply_complex]

lemma modform_exists_norm_le {k : ℤ} (hk : k ≤ 0) {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ(1) k] (f : F) (τ : ℍ) :
    ∃ ξ : ℍ, 1/2 ≤ ξ.im ∧ ‖f τ‖ ≤ ‖f ξ‖ := by
  obtain ⟨γ, hγ, hdenom⟩ := exists_translate' τ
  use γ • τ
  refine ⟨hγ, ?_⟩
  have := slash_action_eqn'' k Γ(1) f γ τ
  rw [coe_smul_eq_smul, denom_coe1_eq_denom] at this
  rw [this,norm_mul, norm_zpow]
  have h2 : 0 ≤ ‖f τ‖ := norm_nonneg (f τ)
  have h3 : 1 ≤ ‖denom (γ : SL(2, ℤ)) τ‖ ^ k := by
    apply one_le_zpow_of_nonpos₀ _ hdenom hk
    exact norm_pos_iff.2 (denom_ne_zero _ _)
  nlinarith

open ModularForm CongruenceSubgroup
