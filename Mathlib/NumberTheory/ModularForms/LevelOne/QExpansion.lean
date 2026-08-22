/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
public import Mathlib.NumberTheory.ModularForms.QExpansionInjective

/-!
# Injectivity of the `q`-expansion on the graded ring of level one modular forms

## Main results

* `ModularForm.levelOne_gradedCoe_injective`: level one modular forms of distinct weights are
  linearly independent.
* `ModularForm.levelOne_qExpansionAlgHom_injective`: the `q`-expansion map
  `ModularForm.qExpansionAlgHom` is injective on the graded ring `⨁ k, ModularForm 𝒮ℒ k`.

Both are special cases of `ModularForm.gradedCoe_injective` and
`ModularForm.qExpansionAlgHom_injective`: the group `𝒮ℒ` has `1` as a strict period, and it does
not fix the cusp `∞` since `S = !![0, -1; 1, 0]` sends it to `0`.
-/

@[expose] public section

open Function Matrix.SpecialLinearGroup ModularGroup OnePoint UpperHalfPlane

open scoped DirectSum MatrixGroups

namespace ModularForm

/-- The level one modular group does not fix the cusp `∞`, as witnessed by `S = !![0, -1; 1, 0]`. -/
theorem exists_mem_SL_smul_infty_ne_infty : ∃ γ ∈ 𝒮ℒ, γ • (∞ : OnePoint ℝ) ≠ ∞ :=
  ⟨mapGL ℝ S, ⟨S, rfl⟩, by simp [smul_infty_eq_self_iff]⟩

/-- **Level one modular forms of distinct weights are linearly independent**: the map sending
`F : ⨁ k, ModularForm 𝒮ℒ k` to the function `∑ k, F k : ℍ → ℂ` is injective. -/
theorem levelOne_gradedCoe_injective : Injective (gradedCoe 𝒮ℒ) :=
  gradedCoe_injective one_pos one_mem_strictPeriods_SL exists_mem_SL_smul_infty_ne_infty

/-- **The `q`-expansion homomorphism on the graded ring of level one modular forms is
injective**. -/
theorem levelOne_qExpansionAlgHom_injective :
    Injective (qExpansionAlgHom 1 one_pos one_mem_strictPeriods_SL) :=
  qExpansionAlgHom_injective one_pos one_mem_strictPeriods_SL exists_mem_SL_smul_infty_ne_infty

end ModularForm
