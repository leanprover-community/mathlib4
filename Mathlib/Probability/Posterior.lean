/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Disintegration.Unique
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!

# Posterior kernel

## Main definitions

* `posterior κ μ`: Bayesian inverse of a kernel `κ` for a prior measure `μ`.

## Main statements

*

## Notation

`κ†μ` denotes the posterior of `κ` with respect to `μ`, `posterior κ μ`.

## Implementation details

-/

open scoped ENNReal

open MeasureTheory

namespace ProbabilityTheory

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}
    {κ : Kernel α β} {μ : Measure α} [IsFiniteMeasure μ] [IsFiniteKernel κ]

variable [StandardBorelSpace α] [Nonempty α]

/-- Bayesian inverse of the kernel `κ` with respect to the measure `μ`. -/
noncomputable
def posterior (κ : Kernel α β) (μ : Measure α) [IsFiniteMeasure μ] [IsFiniteKernel κ] :
    Kernel β α :=
  ((μ ⊗ₘ κ).map Prod.swap).condKernel

@[inherit_doc]
scoped[ProbabilityTheory] notation κ "†" μ => ProbabilityTheory.posterior κ μ

/-- The Bayesian inverse is a Markov kernel. -/
instance : IsMarkovKernel (κ†μ) := by rw [posterior]; infer_instance

/-- The main property of the Bayesian inverse. -/
lemma compProd_posterior (κ : Kernel α β) (μ : Measure α) [IsFiniteMeasure μ] [IsFiniteKernel κ] :
    (κ ∘ₘ μ) ⊗ₘ (κ†μ) = (μ ⊗ₘ κ).map Prod.swap := by
  have h := ((μ ⊗ₘ κ).map Prod.swap).disintegrate ((μ ⊗ₘ κ).map Prod.swap).condKernel
  rwa [Measure.fst_swap_compProd] at h

lemma compProd_posterior' (κ : Kernel α β) (μ : Measure α) [IsFiniteMeasure μ] [IsFiniteKernel κ] :
    (Kernel.id ×ₖ (κ†μ)) ∘ₘ (κ ∘ₘ μ) = ((Kernel.id ×ₖ κ) ∘ₘ μ).map Prod.swap := by
  simp_rw [← Measure.compProd_eq_comp_prod]
  exact compProd_posterior κ μ

lemma compProd_posterior'' (κ : Kernel α β) (μ : Measure α) [IsFiniteMeasure μ] [IsFiniteKernel κ] :
    (Kernel.id ∥ₖ (κ†μ)) ∘ₘ (Kernel.copy β ∘ₘ (κ ∘ₘ μ))
      = (κ ∥ₖ Kernel.id) ∘ₘ (Kernel.copy α ∘ₘ μ) := by
  have h := compProd_posterior' κ μ
  rw [← Kernel.parallelComp_comp_copy, ← Measure.comp_assoc] at h
  rw [h, ← Measure.comp_deterministic_eq_map measurable_swap, ← Kernel.parallelComp_comp_copy,
    ← Measure.comp_assoc, Measure.comp_assoc, ← Kernel.swap, Kernel.swap_parallelComp,
    ← Measure.comp_assoc]
  suffices (Kernel.swap α α) ∘ₘ (Kernel.copy α ∘ₘ μ) = (Kernel.copy α) ∘ₘ μ  by rw [this]
  rw [Measure.comp_assoc, Kernel.swap_copy]

lemma compProd_posterior''' (κ : Kernel α β) (μ : Measure α)
    [IsFiniteMeasure μ] [IsFiniteKernel κ] :
    (κ ∘ₘ μ) ⊗ₘ (κ†μ) = (Kernel.swap α β) ∘ₘ (μ ⊗ₘ κ) := by
  rw [compProd_posterior, Measure.compProd_eq_comp_prod, Measure.map_comp _ _ measurable_swap,
    Measure.comp_assoc, ← Kernel.deterministic_comp_eq_map]
  rfl

lemma posterior_prod_id_comp (κ : Kernel α β) (μ : Measure α)
    [IsFiniteMeasure μ] [IsFiniteKernel κ] :
    ((κ†μ) ×ₖ Kernel.id) ∘ₘ κ ∘ₘ μ = μ ⊗ₘ κ := by
  rw [← Kernel.swap_prod, ← Measure.comp_assoc, ← Measure.compProd_eq_comp_prod,
    compProd_posterior''', Measure.comp_assoc, Kernel.swap_swap, Measure.comp_id]

/-- The Bayesian inverse is unique up to a `μ ∘ₘ κ`-null set. -/
lemma eq_posterior_of_compProd_eq (η : Kernel β α) [IsFiniteKernel η]
    (h : ((κ ∘ₘ μ) ⊗ₘ η) = (μ ⊗ₘ κ).map Prod.swap) :
    ∀ᵐ a ∂(κ ∘ₘ μ), η a = (κ†μ) a := by
  rw [← Measure.fst_swap_compProd] at h
  convert eq_condKernel_of_measure_eq_compProd η h.symm
  rw [Measure.fst_swap_compProd]

@[simp]
lemma posterior_comp_self [IsMarkovKernel κ] : (κ†μ) ∘ₘ (κ ∘ₘ μ) = μ := by
  rw [← Measure.snd_compProd, compProd_posterior, Measure.snd_map_swap, Measure.fst_compProd]

/-- The Bayesian inverse is involutive (up to `μ`-a.e. equality). -/
lemma posterior_posterior [StandardBorelSpace β] [Nonempty β] [IsMarkovKernel κ] :
    ∀ᵐ a ∂μ, ((κ†μ)†(κ ∘ₘ μ)) a = κ a := by
  suffices ∀ᵐ a ∂((κ†μ) ∘ₘ (κ ∘ₘ μ)), κ a = ((κ†μ)†(κ ∘ₘ μ)) a by
    rw [posterior_comp_self] at this
    filter_upwards [this] with a h using h.symm
  refine eq_posterior_of_compProd_eq κ ?_
  rw [posterior_comp_self, compProd_posterior κ μ, Measure.map_map measurable_swap measurable_swap]
  simp

/-- The Bayesian inverse of the identity kernel is the identity kernel. -/
lemma posterior_id : ∀ᵐ a ∂μ, (Kernel.id†μ) a = Kernel.id a := by
  suffices ∀ᵐ a ∂(Kernel.id ∘ₘ μ), Kernel.id a = ((Kernel.id : Kernel α α)†μ) a by
    rw [Measure.comp_id] at this
    filter_upwards [this] with a ha using ha.symm
  refine eq_posterior_of_compProd_eq Kernel.id ?_
  rw [Measure.comp_id, Measure.compProd_id, Measure.map_map measurable_swap]
  · congr
  · exact measurable_id.prod_mk measurable_id

/-- The Bayesian inverse is contravariant. -/
lemma posterior_comp [StandardBorelSpace β] [Nonempty β] {η : Kernel β γ} [IsFiniteKernel η] :
    ∀ᵐ c ∂(η ∘ₘ (κ ∘ₘ μ)), ((η ∘ₖ κ)†μ) c = ((κ†μ) ∘ₖ η†(κ ∘ₘ μ)) c := by
  suffices ∀ᵐ c ∂(η ∘ₘ (κ ∘ₘ μ)), ((κ†μ) ∘ₖ η†(κ ∘ₘ μ)) c = ((η ∘ₖ κ)†μ) c by
    filter_upwards [this] with _ h using h.symm
  rw [Measure.comp_assoc]
  refine eq_posterior_of_compProd_eq ((κ†μ) ∘ₖ η†(κ ∘ₘ μ)) ?_
  simp_rw [Measure.compProd_eq_comp_prod, ← Kernel.parallelComp_comp_copy,
    Kernel.parallelComp_comp_right,
    ← Measure.comp_deterministic_eq_map measurable_swap, ← Measure.comp_assoc]
  calc (Kernel.id ∥ₖ κ†μ) ∘ₘ ((Kernel.id ∥ₖ η†(κ ∘ₘ μ)) ∘ₘ ((Kernel.copy γ) ∘ₘ (η ∘ₘ (κ ∘ₘ μ))))
  _ = (Kernel.id ∥ₖ κ†μ) ∘ₘ ((η ∥ₖ Kernel.id) ∘ₘ (Kernel.copy β ∘ₘ (κ ∘ₘ μ))) := by
    rw [compProd_posterior'']
  _ = (η ∥ₖ Kernel.id) ∘ₘ ((Kernel.id ∥ₖ κ†μ) ∘ₘ (Kernel.copy β ∘ₘ (κ ∘ₘ μ))) := by
    rw [Measure.comp_assoc, Kernel.parallelComp_comm, ← Measure.comp_assoc]
  _ = (η ∥ₖ Kernel.id) ∘ₘ ((κ ∥ₖ Kernel.id) ∘ₘ (Kernel.copy α ∘ₘ μ)) := by
    rw [compProd_posterior'']
  _ = (Kernel.swap _ _)∘ₘ ((Kernel.id ∥ₖ η) ∘ₘ ((Kernel.id ∥ₖ κ) ∘ₘ (Kernel.copy α ∘ₘ μ))) := by
    simp_rw [Measure.comp_assoc]
    conv_rhs => rw [← Kernel.comp_assoc]
    rw [Kernel.swap_parallelComp, Kernel.comp_assoc]
    suffices κ ∥ₖ Kernel.id ∘ₖ Kernel.copy α
        = (Kernel.swap α β) ∘ₖ (Kernel.id ∥ₖ κ ∘ₖ Kernel.copy α) by
      rw [this]
    rw [← Kernel.comp_assoc, Kernel.swap_parallelComp, Kernel.comp_assoc, Kernel.swap_copy]

end ProbabilityTheory
