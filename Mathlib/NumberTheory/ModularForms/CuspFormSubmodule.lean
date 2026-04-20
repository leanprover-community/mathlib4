/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.ModularForms.LevelOne
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

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

@[expose] public noncomputable section

open UpperHalfPlane ModularForm Complex SlashInvariantForm SlashInvariantFormClass
  ModularFormClass MatrixGroups OnePoint Filter Topology

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

namespace CuspForm

/-- The inclusion of cusp forms into modular forms, as a ℂ-linear map. -/
def toModularFormₗ [Γ.HasDetOne] : CuspForm Γ k →ₗ[ℂ] ModularForm Γ k where
  toFun := ModularFormClass.modularForm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma toModularFormₗ_apply [Γ.HasDetOne] (f : CuspForm Γ k) (z : ℍ) :
    (toModularFormₗ f) z = f z := rfl

lemma toModularFormₗ_eq_coe [Γ.HasDetOne] (f : CuspForm Γ k) :
    toModularFormₗ f = (f : ModularForm Γ k) := rfl

lemma toModularFormₗ_injective [Γ.HasDetOne] :
    Function.Injective (toModularFormₗ : CuspForm Γ k → ModularForm Γ k) :=
  fun _ _ h ↦ DFunLike.ext _ _ fun z ↦ DFunLike.congr_fun h z

end CuspForm

namespace ModularForm

/-- The submodule of `ModularForm Γ k` consisting of cusp forms, defined as the range of
the inclusion `CuspForm.toModularFormₗ`. -/
def cuspFormSubmodule (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) [Γ.HasDetOne] :
    Submodule ℂ (ModularForm Γ k) :=
  LinearMap.range CuspForm.toModularFormₗ

/-- A modular form is a cusp form if it lies in the cusp form submodule. -/
def IsCuspForm [Γ.HasDetOne] (f : ModularForm Γ k) : Prop :=
  f ∈ cuspFormSubmodule Γ k

@[simp]
lemma mem_cuspFormSubmodule_iff [Γ.HasDetOne] {f : ModularForm Γ k} :
    f ∈ cuspFormSubmodule Γ k ↔ IsCuspForm f := Iff.rfl

/-- The cusp form submodule is linearly equivalent to the type of cusp forms. -/
def CuspForm.equivCuspFormSubmodule (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) [Γ.HasDetOne] :
    CuspForm Γ k ≃ₗ[ℂ] cuspFormSubmodule Γ k :=
  LinearEquiv.ofInjective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective

/-- A modular form is a cusp form if and only if it vanishes at every cusp. This is the
general characterization valid for any subgroup. -/
lemma isCuspForm_iff [Γ.HasDetOne] (f : ModularForm Γ k) :
    IsCuspForm f ↔ ∀ {c}, IsCusp c Γ → c.IsZeroAt f k :=
  ⟨fun ⟨g, hg⟩ _ ↦ hg ▸ g.zero_at_cusps', fun h ↦ ⟨⟨f, f.holo', h⟩, rfl⟩⟩

/-- A modular form with `valueAtInfty f = 0` is zero at infinity. -/
lemma isZeroAtImInfty_of_valueAtInfty_eq_zero {F : Type*} [FunLike F ℍ ℂ]
    [DiscreteTopology Γ] [Γ.HasDetPlusMinusOne] [Fact (IsCusp ∞ Γ)] [ModularFormClass F Γ k]
    (f : F) (h : valueAtInfty f = 0) : IsZeroAtImInfty f := by
  have hh : 0 < Γ.strictWidthInfty := Γ.strictWidthInfty_pos_iff.mpr Fact.out
  have hΓ : Γ.strictWidthInfty ∈ Γ.strictPeriods := Γ.strictWidthInfty_mem_strictPeriods
  simp_rw [IsZeroAtImInfty, ZeroAtFilter, ← h, ← cuspFunction_apply_zero f hh hΓ]
  exact ((analyticAt_cuspFunction_zero f hh hΓ).continuousAt.tendsto.comp
    (qParam_tendsto_atImInfty hh)).congr (fun τ ↦ eq_cuspFunction f τ hΓ hh.ne')

section SL2Z

open EisensteinSeries

variable {k : ℤ}

/-- An `𝒮ℒ` modular form with vanishing q-expansion constant term vanishes at every cusp. -/
lemma isZeroAt_of_coeffZero_eq_zero (f : ModularForm 𝒮ℒ k)
    (h : (qExpansion 1 f).coeff 0 = 0) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    c.IsZeroAt f k := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [isZeroAt_iff_forall_SL2Z hc]
  intro γ _
  rw [show (⇑f ∣[k] γ) = ⇑f from f.slash_action_eq' _ ⟨γ, rfl⟩]
  exact isZeroAtImInfty_of_valueAtInfty_eq_zero f <| by
    rwa [← qExpansion_coeff_zero f one_pos one_mem_strictPeriods_SL]

/-- Build a `CuspForm 𝒮ℒ k` from a `ModularForm 𝒮ℒ k` whose q-expansion has vanishing
constant term. The resulting cusp form has the same underlying function. -/
def toCuspForm (f : ModularForm 𝒮ℒ k) (h : (qExpansion 1 f).coeff 0 = 0) : CuspForm 𝒮ℒ k :=
  { f with zero_at_cusps' := isZeroAt_of_coeffZero_eq_zero f h }

@[simp]
lemma toCuspForm_apply (f : ModularForm 𝒮ℒ k) (h : (qExpansion 1 f).coeff 0 = 0)
    (z : ℍ) : (toCuspForm f h) z = f z := rfl

/-- For `𝒮ℒ` modular forms, `IsCuspForm` is equivalent to the q-expansion having vanishing
constant term. -/
lemma isCuspForm_iff_coeffZero_eq_zero (f : ModularForm 𝒮ℒ k) :
    IsCuspForm f ↔ (qExpansion 1 f).coeff 0 = 0 := by
  refine ⟨fun ⟨g, hg⟩ ↦ ?_, fun h ↦ (isCuspForm_iff f).mpr (isZeroAt_of_coeffZero_eq_zero f h)⟩
  rw [← hg, qExpansion_coeff_zero _ one_pos one_mem_strictPeriods_SL]
  exact (CuspFormClass.zero_at_infty g).valueAtInfty_eq_zero

end SL2Z

end ModularForm
