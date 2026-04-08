/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# Cusp form submodule and IsCuspForm predicate

This file defines the inclusion of cusp forms into modular forms as a linear map, the cusp form
submodule of modular forms, and the `IsCuspForm` predicate. It also provides a direct constructor
`ModularForm.toCuspForm` for building cusp forms from modular forms with vanishing constant
q-expansion coefficient (for `𝒮ℒ`).

## Main definitions

* `CuspForm.toModularFormₗ`: the inclusion `CuspForm Γ k →ₗ[ℂ] ModularForm Γ k`.
* `ModularForm.cuspFormSubmodule`: the submodule of `ModularForm Γ k` consisting of cusp forms.
* `ModularForm.IsCuspForm`: predicate that a modular form lies in the cusp form submodule.
* `ModularForm.toCuspForm`: builds a `CuspForm 𝒮ℒ k` from a `ModularForm` whose q-expansion
  has vanishing constant term.

## Main results

* `CuspForm.toModularFormₗ_injective`: the inclusion is injective.
* `CuspForm.equivCuspFormSubmodule`: `CuspForm Γ k ≃ₗ[ℂ] cuspFormSubmodule Γ k`.
* `ModularForm.isCuspForm_iff_coeffZero_eq_zero`: for `𝒮ℒ`, `IsCuspForm` is equivalent to the
  q-expansion having vanishing constant term.
-/

open UpperHalfPlane ModularForm Complex SlashInvariantForm SlashInvariantFormClass
  ModularFormClass MatrixGroups OnePoint Filter Topology

noncomputable section

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

namespace CuspForm

/-- The inclusion of cusp forms into modular forms, as a ℂ-linear map. -/
def toModularFormₗ [Γ.HasDetOne] : CuspForm Γ k →ₗ[ℂ] ModularForm Γ k where
  toFun f :=
    { toSlashInvariantForm := f.toSlashInvariantForm
      holo' := f.holo'
      bdd_at_cusps' := fun hc g hg ↦ (f.zero_at_cusps' hc g hg).boundedAtFilter }
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

@[simp]
lemma toModularFormₗ_apply [Γ.HasDetOne] (f : CuspForm Γ k) (z : ℍ) :
    (toModularFormₗ f) z = f z := rfl

lemma toModularFormₗ_injective [Γ.HasDetOne] :
    Function.Injective (toModularFormₗ : CuspForm Γ k → ModularForm Γ k) :=
  fun _ _ h ↦ DFunLike.ext _ _ fun z ↦ congr_fun (congr_arg DFunLike.coe h) z

end CuspForm

namespace ModularForm

/-- The submodule of `ModularForm Γ k` consisting of cusp forms, defined as the range of
the inclusion `CuspForm.toModularFormₗ`. -/
def cuspFormSubmodule [Γ.HasDetOne] : Submodule ℂ (ModularForm Γ k) :=
  LinearMap.range (CuspForm.toModularFormₗ)

/-- A modular form is a cusp form if it lies in the cusp form submodule. -/
def IsCuspForm [Γ.HasDetOne] (f : ModularForm Γ k) : Prop :=
  f ∈ cuspFormSubmodule (Γ := Γ) (k := k)

/-- The cusp form submodule is linearly equivalent to the type of cusp forms. -/
def CuspForm.equivCuspFormSubmodule [Γ.HasDetOne] :
    CuspForm Γ k ≃ₗ[ℂ] cuspFormSubmodule (Γ := Γ) (k := k) :=
  LinearEquiv.ofInjective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective

/-- A modular form is a cusp form if and only if it vanishes at every cusp. This is the
general characterization valid for any subgroup. -/
lemma isCuspForm_iff [Γ.HasDetOne] (f : ModularForm Γ k) :
    IsCuspForm f ↔ ∀ {c : OnePoint ℝ}, IsCusp c Γ → c.IsZeroAt f k := by
  constructor
  · rintro ⟨g, hg⟩ c hc
    have : (f : ℍ → ℂ) = (g : ℍ → ℂ) := congr_arg DFunLike.coe hg.symm
    simpa [this] using g.zero_at_cusps' hc
  · intro h
    exact ⟨⟨f.toSlashInvariantForm, f.holo', h⟩, by ext; rfl⟩

section SL2Z

open EisensteinSeries

variable {k : ℤ}

lemma one_mem_strictPeriods_SL : (1 : ℝ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods :=
  CongruenceSubgroup.Gamma_one_coe_eq_SL ▸ one_mem_strictPeriods_SL2Z

/-- If an `𝒮ℒ` modular form has `valueAtInfty f = 0`, then it is zero at infinity. -/
lemma isZeroAtImInfty_of_valueAtInfty_eq_zero
    (f : ModularForm 𝒮ℒ k) (h : valueAtInfty f = 0) : IsZeroAtImInfty f := by
  change Filter.Tendsto f atImInfty (𝓝 0)
  rw [show (0 : ℂ) = cuspFunction 1 f 0 from by
    rw [cuspFunction_apply_zero f one_pos one_mem_strictPeriods_SL]; exact h.symm]
  exact ((analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_SL).continuousAt.tendsto.comp
    (qParam_tendsto_atImInfty one_pos)).congr
    (fun τ ↦ eq_cuspFunction f τ one_mem_strictPeriods_SL one_ne_zero)

/-- An `𝒮ℒ` modular form with vanishing q-expansion constant term vanishes at every cusp. -/
private lemma isZeroAt_of_coeffZero_eq_zero (f : ModularForm 𝒮ℒ k)
    (h : (qExpansion 1 f).coeff 0 = 0) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    c.IsZeroAt f k := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [isZeroAt_iff_forall_SL2Z hc]
  intro γ _
  rw [show (⇑f ∣[k] γ) = ⇑f from f.slash_action_eq' _ (MonoidHom.mem_range.mpr ⟨γ, rfl⟩)]
  exact isZeroAtImInfty_of_valueAtInfty_eq_zero f <| by
    rwa [← qExpansion_coeff_zero f one_pos one_mem_strictPeriods_SL]

/-- Build a `CuspForm 𝒮ℒ k` from a `ModularForm 𝒮ℒ k` whose q-expansion has vanishing
constant term. The resulting cusp form has the same underlying function. -/
def toCuspForm (f : ModularForm 𝒮ℒ k) (h : (qExpansion 1 f).coeff 0 = 0) : CuspForm 𝒮ℒ k where
  toSlashInvariantForm := f.toSlashInvariantForm
  holo' := f.holo'
  zero_at_cusps' := isZeroAt_of_coeffZero_eq_zero f h

@[simp]
lemma toCuspForm_apply (f : ModularForm 𝒮ℒ k) (h : (qExpansion 1 f).coeff 0 = 0)
    (z : ℍ) : (toCuspForm f h) z = f z := rfl

/-- For `𝒮ℒ` modular forms, `IsCuspForm` is equivalent to the q-expansion having vanishing
constant term. -/
lemma isCuspForm_iff_coeffZero_eq_zero (f : ModularForm 𝒮ℒ k) :
    IsCuspForm f ↔ (qExpansion 1 f).coeff 0 = 0 := by
  constructor
  · intro ⟨g, hg⟩
    rw [qExpansion_coeff_zero f one_pos one_mem_strictPeriods_SL]
    exact congr_arg valueAtInfty (congr_arg DFunLike.coe hg.symm) ▸
      (CuspFormClass.zero_at_infty g).valueAtInfty_eq_zero
  · exact fun h ↦ (isCuspForm_iff f).mpr (isZeroAt_of_coeffZero_eq_zero f h)

end SL2Z

end ModularForm
