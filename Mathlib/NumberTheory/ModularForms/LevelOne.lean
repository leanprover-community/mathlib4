/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Level one modular forms

This file contains results specific to modular forms of level one, ie. modular forms for `SL(2, ℤ)`.

TODO: Add finite dimisionality of these spaces of modular forms.

-/

open UpperHalfPlane ModularGroup SlashInvariantForm ModularForm CongruenceSubgroup Complex
local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R
local notation  "Γ(" n ")"  => CongruenceSubgroup.Gamma n

/--The map from `SL(2, ℤ)` to `Γ(1)`. Its preferable to work with this, since levels of modular
forms are terms of type Subgroup `SL(2, ℤ)`. -/
@[coe]def CongruenceSubgroup.coe1 : SL(2, ℤ) → Γ(1) :=
  fun g => ⟨↑g, by simp [CongruenceSubgroup.Gamma_one_top]⟩

instance : Coe SL(2, ℤ) Γ(1) := ⟨coe1⟩

lemma CongruenceSubgroup.coe_smul_eq_smul {g : SL(2, ℤ)} {τ : ℍ} : (g : Γ(1)) • τ = (g • τ) := by
  simp only [coe1, Subgroup.mk_smul, ModularGroup.sl_moeb]

@[simp]
lemma CongruenceSubgroup.denom_coe1_eq_denom {g : SL(2, ℤ)} {τ : ℍ} :
    denom (g : Γ(1)) τ = denom g τ := by
  simp only [denom, coe1, Fin.isValue, ModularGroup.coe'_apply_complex]

lemma SlashInvariantForm.exists_norm_le {k : ℤ} (hk : k ≤ 0) {F : Type*} [FunLike F ℍ ℂ]
    [SlashInvariantFormClass F Γ(1) k] (f : F) (τ : ℍ) :
    ∃ ξ : ℍ, 1/2 ≤ ξ.im ∧ ‖f τ‖ ≤ ‖f ξ‖ := by
  obtain ⟨γ, hγ, hdenom⟩ := exists_translate' τ
  refine ⟨γ • τ, hγ, ?_⟩
  have := slash_action_eqn'' k Γ(1) f γ τ
  rw [coe_smul_eq_smul, denom_coe1_eq_denom] at this
  rw [this, norm_mul, norm_zpow]
  have h3 : 1 ≤ ‖denom (γ : SL(2, ℤ)) τ‖ ^ k := by
    apply one_le_zpow_of_nonpos₀ _ hdenom hk
    exact norm_pos_iff.2 (denom_ne_zero _ _)
  exact le_mul_of_one_le_left (norm_nonneg (f τ)) h3

-- find_home suggests Mathlib.Topology.ContinuousMap.StarOrdered which seems wrong..
lemma Complex.zpow_eq_one (k : ℤ) {n : ℝ} (hn : 1 < n) (h : (n : ℂ) ^ k = 1) : k = 0 := by
  have : (n : ℂ)^k = (n : ℝ)^k := by simp only [ofReal_natCast]
  rw [this] at h
  norm_cast at h
  replace h : (n : ℝ) ^ k = (n : ℝ) ^ (0 : ℤ) := by simp only [zpow_zero, ← h]
  exact zpow_right_injective₀ (a := (n : ℝ)) (by norm_cast at *; linarith) (by aesop) h

lemma SlashInvariantForm.neg_wt_const_eq_zero {F : Type*} [FunLike F ℍ ℂ] (k : ℤ) (f : F) (c : ℂ)
    [SlashInvariantFormClass F Γ(1) k] (hf : ⇑f = (fun _ => c)) : k = 0 ∨ c = 0 := by
  have hI := (slash_action_eqn'' k Γ(1) f ModularGroup.S) I
  have h2I2 := (slash_action_eqn'' k Γ(1) f ModularGroup.S) ⟨2 * Complex.I, by simp⟩
  simp only [hf, subgroup_to_sl_moeb, sl_moeb, denom_coe1_eq_denom, denom_S] at *
  nth_rw 1 [h2I2] at hI
  simp only [mul_eq_mul_right_iff] at hI
  rcases hI with H | H
  · left
    rw [UpperHalfPlane.I, mul_zpow, mul_left_eq_self₀] at H
    rcases H with H | H
    · apply Complex.zpow_eq_one k (one_lt_two) H
    · exact False.elim (zpow_ne_zero k I_ne_zero H)
  · exact Or.inr H
