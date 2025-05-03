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

variable {Γ : Subgroup SL(2, ℤ)}

namespace Subgroup

variable (Γ)

/-- The width of the cusp `∞` for a subgroup of `SL(2, ℤ)`, i.e. the least `n > 0` such that
`[1, n; 0, 1] ∈ Γ`. -/
protected def width : ℕ := relindex Γ (.zpowers ModularGroup.T)

lemma width_ne_zero [Γ.FiniteIndex] : Γ.width ≠ 0 :=
  FiniteIndex.index_ne_zero

lemma T_zpow_width_mem :
    ModularGroup.T ^ Γ.width ∈ Γ :=
  (Γ.subgroupOf <| .zpowers ModularGroup.T).pow_index_mem ⟨_, mem_zpowers _⟩

/-- The integers `n` such that `[1, n; 0, 1] ∈ Γ` are precisely the multiples of `Γ.width`. -/
lemma T_zpow_mem_iff {n : ℤ} : ModularGroup.T ^ n ∈ Γ ↔ ↑Γ.width ∣ n := by
  let A : AddSubgroup ℤ := Subgroup.toAddSubgroup' <| Γ.comap (zpowersHom _ T)
  have hA : Γ.width = A.index := by
    have h := A.index_toSubgroup
    have h' := Γ.index_comap (zpowersHom _ T)
    rw [range_zpowersHom, ← Subgroup.width] at h'
    simp only [A, OrderIso.apply_symm_apply, h'] at h
    exact h
  rw [hA, (by rfl : T ^ n ∈ Γ ↔ n ∈ A)]
  obtain ⟨m, hm⟩ := Int.subgroup_cyclic A
  simp [hm, ← AddSubgroup.zmultiples_eq_closure, Int.mem_zmultiples_iff]

end Subgroup

namespace SlashInvariantFormClass

variable {F : Type*} (f : F) (k : ℤ) [FunLike F ℍ ℂ] [hF : SlashInvariantFormClass F Γ k]
   {n : ℤ}

include hF -- necessary because `k` is not inferrable from the statements

theorem vAdd_width_periodic (hn : ↑Γ.width ∣ n) (τ : ℍ) :
    f ((n : ℝ) +ᵥ τ) = f τ := by
  rw [← modular_T_zpow_smul τ, SlashInvariantForm.slash_action_eqn' (k := k) f
    (Γ.T_zpow_mem_iff.mpr hn)]
  simp [← zpow_natCast, ← zpow_mul, ModularGroup.coe_T_zpow]

theorem T_zpow_width_invariant (hn : ↑Γ.width ∣ n) (τ : ℍ) :
    f (ModularGroup.T ^ n • τ) = f τ := by
  simpa [-sl_moeb, modular_T_zpow_smul] using vAdd_width_periodic f k hn τ

end SlashInvariantFormClass
