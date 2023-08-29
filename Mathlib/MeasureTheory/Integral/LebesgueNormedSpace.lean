/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.Analysis.NormedSpace.Basic

#align_import measure_theory.integral.lebesgue_normed_space from "leanprover-community/mathlib"@"bf6a01357ff5684b1ebcd0f1a13be314fc82c0bf"

/-! # A lemma about measurability with density under scalar multiplication in normed spaces -/


open MeasureTheory Filter ENNReal Set

open NNReal ENNReal

variable {α β γ δ : Type*} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}

theorem aemeasurable_withDensity_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace.SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] {f : α → ℝ≥0}
    (hf : Measurable f) {g : α → E} :
    AEMeasurable g (μ.withDensity fun x => (f x : ℝ≥0∞)) ↔
      AEMeasurable (fun x => (f x : ℝ) • g x) μ := by
  constructor
  -- ⊢ AEMeasurable g → AEMeasurable fun x => ↑(f x) • g x
  · rintro ⟨g', g'meas, hg'⟩
    -- ⊢ AEMeasurable fun x => ↑(f x) • g x
    have A : MeasurableSet { x : α | f x ≠ 0 } := (hf (measurableSet_singleton 0)).compl
    -- ⊢ AEMeasurable fun x => ↑(f x) • g x
    refine' ⟨fun x => (f x : ℝ) • g' x, hf.coe_nnreal_real.smul g'meas, _⟩
    -- ⊢ (fun x => ↑(f x) • g x) =ᵐ[μ] fun x => ↑(f x) • g' x
    apply @ae_of_ae_restrict_of_ae_restrict_compl _ _ _ { x | f x ≠ 0 }
    -- ⊢ ∀ᵐ (x : α) ∂Measure.restrict μ {x | f x ≠ 0}, (fun x => ↑(f x) • g x) x = (f …
    · rw [EventuallyEq, ae_withDensity_iff hf.coe_nnreal_ennreal] at hg'
      -- ⊢ ∀ᵐ (x : α) ∂Measure.restrict μ {x | f x ≠ 0}, (fun x => ↑(f x) • g x) x = (f …
      rw [ae_restrict_iff' A]
      -- ⊢ ∀ᵐ (x : α) ∂μ, x ∈ {x | f x ≠ 0} → (fun x => ↑(f x) • g x) x = (fun x => ↑(f …
      filter_upwards [hg']
      -- ⊢ ∀ (a : α), (↑(f a) ≠ 0 → g a = g' a) → f a ≠ 0 → ↑(f a) • g a = ↑(f a) • g' a
      intro a ha h'a
      -- ⊢ ↑(f a) • g a = ↑(f a) • g' a
      have : (f a : ℝ≥0∞) ≠ 0 := by simpa only [Ne.def, coe_eq_zero] using h'a
      -- ⊢ ↑(f a) • g a = ↑(f a) • g' a
      rw [ha this]
      -- 🎉 no goals
    · filter_upwards [ae_restrict_mem A.compl]
      -- ⊢ ∀ (a : α), a ∈ {x | f x ≠ 0}ᶜ → ↑(f a) • g a = ↑(f a) • g' a
      intro x hx
      -- ⊢ ↑(f x) • g x = ↑(f x) • g' x
      simp only [Classical.not_not, mem_setOf_eq, mem_compl_iff] at hx
      -- ⊢ ↑(f x) • g x = ↑(f x) • g' x
      simp [hx]
      -- 🎉 no goals
  · rintro ⟨g', g'meas, hg'⟩
    -- ⊢ AEMeasurable g
    refine' ⟨fun x => (f x : ℝ)⁻¹ • g' x, hf.coe_nnreal_real.inv.smul g'meas, _⟩
    -- ⊢ g =ᵐ[Measure.withDensity μ fun x => ↑(f x)] fun x => (↑(f x))⁻¹ • g' x
    rw [EventuallyEq, ae_withDensity_iff hf.coe_nnreal_ennreal]
    -- ⊢ ∀ᵐ (x : α) ∂μ, ↑(f x) ≠ 0 → g x = (↑(f x))⁻¹ • g' x
    filter_upwards [hg']
    -- ⊢ ∀ (a : α), ↑(f a) • g a = g' a → ↑(f a) ≠ 0 → g a = (↑(f a))⁻¹ • g' a
    intro x hx h'x
    -- ⊢ g x = (↑(f x))⁻¹ • g' x
    rw [← hx, smul_smul, _root_.inv_mul_cancel, one_smul]
    -- ⊢ ↑(f x) ≠ 0
    simp only [Ne.def, coe_eq_zero] at h'x
    -- ⊢ ↑(f x) ≠ 0
    simpa only [NNReal.coe_eq_zero, Ne.def] using h'x
    -- 🎉 no goals
#align ae_measurable_with_density_iff aemeasurable_withDensity_iff
