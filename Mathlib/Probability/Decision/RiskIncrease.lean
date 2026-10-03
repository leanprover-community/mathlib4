/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Probability.Decision.Risk.Defs
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.WithDensity

import Mathlib.Probability.Decision.Risk.Basic

/-!
# Risk increase (or statistical information)

A way to quantify the information obtained by an experiment is to look at the increase in risk that
results from discarding the observation of that experiment.
We call that quantity the **risk increase**. It was called **information** by DeGroot
in [degroot1962uncertainty], but we opt for a more descriptive name to avoid confusion with other
notions of information in statistics and information theory.
See also [duchi2018multiclass] for properties of the risk increase and relations to statistical
divergences.

## Main definitions

* `riskIncrease ℓ P π`: the increase in risk that results from discarding the observation in
  a Bayesian estimation problem.
  `bayesRisk ℓ (Kernel.discard 𝓧 ∘ₖ P) π - bayesRisk ℓ P π`

## Main statements

* `riskIncrease_comp_le`: the data-processing inequality for the risk increase, which states that
  the risk increase cannot be increased by post-processing the observation (composing the
  kernel `P` with a Markov kernel): `riskIncrease ℓ (η ∘ₖ P) π ≤ riskIncrease ℓ P π`.
* `riskIncrease_map_le`: version of the data-processing inequality for a measurable function instead
  of a Markov kernel. `riskIncrease ℓ (P.map f) π ≤ riskIncrease ℓ P π`.

-/

@[expose] public section

open MeasureTheory Set Function

open scoped ENNReal NNReal

namespace ProbabilityTheory

lemma Kernel.withDensity_comp {α β γ : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    {_ : MeasurableSpace γ} {κ : Kernel α β} [IsSFiniteKernel κ]
    {η : Kernel β γ} [IsSFiniteKernel η] {f : α → ℝ≥0∞} (hf : Measurable f) :
    (η ∘ₖ κ).withDensity (fun a _ ↦ f a) = η ∘ₖ (κ.withDensity (fun a _ ↦ f a)) := by
  ext a s hs
  rw [Kernel.withDensity_apply _ (by fun_prop), Kernel.comp_apply, Kernel.comp_apply]
  conv_rhs => rw [Measure.bind_apply hs (by fun_prop)]
  simp only [withDensity_const, Measure.smul_apply, smul_eq_mul]
  rw [lintegral_withDensity _ (by fun_prop), Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_const_mul]
  all_goals exact η.measurable_coe hs

variable {Θ 𝓧 𝓧' 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧}
  {m𝓧' : MeasurableSpace 𝓧'} [MeasurableSpace 𝓨]
  {π : Measure Θ} {P : Kernel Θ 𝓧} {ℓ : Θ → 𝓨 → ℝ≥0∞}

/-- The increase in risk that results from discarding the observation
in a Bayesian estimation problem. -/
noncomputable
def riskIncrease (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (π : Measure Θ) : ℝ≥0∞ :=
  bayesRisk ℓ (Kernel.discard 𝓧 ∘ₖ P : Kernel Θ Unit) π - bayesRisk ℓ P π

lemma riskIncrease_eq_iInf_sub' [Nonempty 𝓨] (hl : Measurable (uncurry ℓ)) (P : Kernel Θ 𝓧)
    (π : Measure Θ) [SFinite π] :
    riskIncrease ℓ P π = (⨅ z : 𝓨, ∫⁻ θ, P θ univ * ℓ θ z ∂π) - bayesRisk ℓ P π := by
  simp_rw [riskIncrease]
  simp [bayesRisk_of_subsingleton' hl, mul_comm, Kernel.comp_discard']

lemma riskIncrease_eq_iInf_sub (hl : Measurable (uncurry ℓ)) (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (π : Measure Θ) [SFinite π] :
    riskIncrease ℓ P π = (⨅ z : 𝓨, ∫⁻ θ, ℓ θ z ∂π) - bayesRisk ℓ P π := by
  simp_rw [riskIncrease, Kernel.comp_discard, bayesRisk_discard hl]

@[simp] lemma riskIncrease_of_isEmpty_of_isEmpty [IsEmpty 𝓧] [IsEmpty 𝓨] :
    riskIncrease ℓ P π = ∞ := by
  simp [riskIncrease]

@[simp] lemma riskIncrease_of_nonempty_of_isEmpty [Nonempty 𝓧] [IsEmpty 𝓨] :
    riskIncrease ℓ P π = 0 := by
  simp [riskIncrease]

@[simp] lemma riskIncrease_zero_left [Nonempty 𝓨] : riskIncrease ℓ (0 : Kernel Θ 𝓧) π = 0 := by
  simp [riskIncrease]

@[simp] lemma riskIncrease_zero_right [Nonempty 𝓨] : riskIncrease ℓ P (0 : Measure Θ) = 0 := by
  simp [riskIncrease]

@[simp] lemma riskIncrease_const (hl : Measurable (uncurry ℓ))
    [SFinite π] {μ : Measure 𝓧} [IsProbabilityMeasure μ] :
    riskIncrease ℓ (Kernel.const Θ μ) π = 0 := by
  simp [riskIncrease, bayesRisk_const hl]

lemma riskIncrease_le_iInf' [Nonempty 𝓨] (hl : Measurable (uncurry ℓ)) [SFinite π] :
    riskIncrease ℓ P π ≤ ⨅ z : 𝓨, ∫⁻ θ, P θ univ * ℓ θ z ∂π :=
  riskIncrease_eq_iInf_sub' hl P π ▸ tsub_le_self

lemma riskIncrease_le_iInf (hl : Measurable (uncurry ℓ)) [IsMarkovKernel P] [SFinite π] :
    riskIncrease ℓ P π ≤ ⨅ z : 𝓨, ∫⁻ θ, ℓ θ z ∂π :=
  riskIncrease_eq_iInf_sub hl P π ▸ tsub_le_self

lemma riskIncrease_lt_top' [Nonempty 𝓨] (hl : Measurable (uncurry ℓ))
    [IsFiniteMeasure π] {y : 𝓨} (h_finite : ∫⁻ θ, P θ univ * ℓ θ y ∂π ≠ ⊤) :
    riskIncrease ℓ P π < ⊤ :=
  (riskIncrease_le_iInf' hl).trans_lt (iInf_lt_top.mpr ⟨y, h_finite.lt_top⟩)

lemma riskIncrease_lt_top (hl : Measurable (uncurry ℓ)) [IsMarkovKernel P] [IsFiniteMeasure π]
    {y : 𝓨} (h_finite : ∫⁻ θ, ℓ θ y ∂π ≠ ⊤) :
    riskIncrease ℓ P π < ⊤ :=
  (riskIncrease_le_iInf hl).trans_lt (iInf_lt_top.mpr ⟨y, h_finite.lt_top⟩)

/-- **Data processing inequality** for the risk increase. -/
lemma riskIncrease_comp_le (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (π : Measure Θ)
    (η : Kernel 𝓧 𝓧') [IsMarkovKernel η] :
    riskIncrease ℓ (η ∘ₖ P) π ≤ riskIncrease ℓ P π := by
  refine tsub_le_tsub ?_ (bayesRisk_le_bayesRisk_comp _ _ _ _)
  rw [← Kernel.comp_assoc]
  simp

/-- **Data processing inequality** for the risk increase. -/
lemma riskIncrease_map_le (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (π : Measure Θ)
    {f : 𝓧 → 𝓧'} (hf : Measurable f) :
    riskIncrease ℓ (P.map f) π ≤ riskIncrease ℓ P π := by
  rw [← Kernel.deterministic_comp_eq_map hf]
  exact riskIncrease_comp_le ℓ P π (Kernel.deterministic f hf)

lemma riskIncrease_withDensity (hl : Measurable (uncurry ℓ))
    (P : Kernel Θ 𝓧) [IsSFiniteKernel P] (π : Measure Θ)
    {f : Θ → ℝ≥0∞} (hf : Measurable f) :
    riskIncrease ℓ (P.withDensity (fun θ _ ↦ f θ)) π = riskIncrease ℓ P (π.withDensity f) := by
  rw [riskIncrease, ← Kernel.withDensity_comp hf, bayesRisk_withDensity hl _ π hf,
    bayesRisk_withDensity hl _ π hf, riskIncrease]

end ProbabilityTheory
