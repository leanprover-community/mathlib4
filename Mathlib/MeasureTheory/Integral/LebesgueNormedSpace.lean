/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.NormedSpace.Basic

#align_import measure_theory.integral.lebesgue_normed_space from "leanprover-community/mathlib"@"bf6a01357ff5684b1ebcd0f1a13be314fc82c0bf"

/-! # A lemma about measurability with density under scalar multiplication in normed spaces -/


open MeasureTheory Filter ENNReal Set

open NNReal ENNReal

variable {α β γ δ : Type*} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}

theorem aemeasurable_withDensity_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] {f : α → ℝ≥0}
    (hf : Measurable f) {g : α → E} :
    AEMeasurable g (μ.withDensity fun x => (f x : ℝ≥0∞)) ↔
      AEMeasurable (fun x => (f x : ℝ) • g x) μ := by
  constructor
  · rintro ⟨g', g'meas, hg'⟩
    have A : MeasurableSet { x : α | f x ≠ 0 } := (hf (measurableSet_singleton 0)).compl
    refine ⟨fun x => (f x : ℝ) • g' x, hf.coe_nnreal_real.smul g'meas, ?_⟩
    apply @ae_of_ae_restrict_of_ae_restrict_compl _ _ _ { x | f x ≠ 0 }
    · rw [EventuallyEq, ae_withDensity_iff hf.coe_nnreal_ennreal] at hg'
      rw [ae_restrict_iff' A]
      filter_upwards [hg']
      intro a ha h'a
      have : (f a : ℝ≥0∞) ≠ 0 := by simpa only [Ne, ENNReal.coe_eq_zero] using h'a
      rw [ha this]
    · filter_upwards [ae_restrict_mem A.compl]
      intro x hx
      simp only [Classical.not_not, mem_setOf_eq, mem_compl_iff] at hx
      simp [hx]
  · rintro ⟨g', g'meas, hg'⟩
    refine ⟨fun x => (f x : ℝ)⁻¹ • g' x, hf.coe_nnreal_real.inv.smul g'meas, ?_⟩
    rw [EventuallyEq, ae_withDensity_iff hf.coe_nnreal_ennreal]
    filter_upwards [hg']
    intro x hx h'x
    rw [← hx, smul_smul, _root_.inv_mul_cancel, one_smul]
    simp only [Ne, ENNReal.coe_eq_zero] at h'x
    simpa only [NNReal.coe_eq_zero, Ne] using h'x
#align ae_measurable_with_density_iff aemeasurable_withDensity_iff
