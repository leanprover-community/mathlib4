/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Disintegration.Unique

/-!

# Posterior kernel

For `μ : Measure α` (called prior measure), seen as a measure on a parameter, and a kernel
`κ : Kernel α β` that gives the conditional distribution of "data" in `β` given the prior parameter,
we can get the distribution of the data with `κ ∘ₘ μ`, and the joint distribution of parameter and
data `μ ⊗ₘ κ : Measure (α × β)`.

The posterior distribution of the parameter given the data is a Markov kernel `κ†μ : Kernel β α`
such that `(κ ∘ₘ μ) ⊗ₘ κ†μ = (μ ⊗ₘ κ).map Prod.swap`. That is, the joint distribution of parameter
and data can be recovered from the distribution of the data and the posterior.

## Main definitions

* `posterior κ μ`: posterior of a kernel `κ` for a prior measure `μ`.

## Main statements

* `compProd_posterior_eq_map_swap`: the main property of the posterior,
  `(κ ∘ₘ μ) ⊗ₘ κ†μ = (μ ⊗ₘ κ).map Prod.swap`.
* `ae_eq_posterior_of_compProd_eq`
* `posterior_comp_self`: `(κ†μ) ∘ₘ κ ∘ₘ μ = μ`
* `posterior_posterior`: `(κ†μ)†(κ ∘ₘ μ) =ᵐ[μ] κ`
* `posterior_comp`: `(η ∘ₖ κ)†μ =ᵐ[η ∘ₘ κ ∘ₘ μ] (κ†μ) ∘ₖ η†(κ ∘ₘ μ)`

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

/-- Posterior of the kernel `κ` with respect to the measure `μ`. -/
noncomputable
def posterior (κ : Kernel α β) (μ : Measure α) [IsFiniteMeasure μ] [IsFiniteKernel κ] :
    Kernel β α :=
  ((μ ⊗ₘ κ).map Prod.swap).condKernel

/-- Posterior of the kernel `κ` with respect to the measure `μ`. -/
scoped[ProbabilityTheory] notation3 κ "†" μ:100 => ProbabilityTheory.posterior κ μ

/-- The posterior is a Markov kernel. -/
instance : IsMarkovKernel (κ†μ) := by rw [posterior]; infer_instance

/-- The main property of the posterior. -/
lemma compProd_posterior_eq_map_swap (κ : Kernel α β) (μ : Measure α)
    [IsFiniteMeasure μ] [IsFiniteKernel κ] :
    (κ ∘ₘ μ) ⊗ₘ κ†μ = (μ ⊗ₘ κ).map Prod.swap := by
  have h := ((μ ⊗ₘ κ).map Prod.swap).disintegrate ((μ ⊗ₘ κ).map Prod.swap).condKernel
  simp only [Measure.fst_map_swap, Measure.snd_compProd] at h
  exact h

lemma compProd_posterior_eq_swap_comp (κ : Kernel α β) (μ : Measure α)
    [IsFiniteMeasure μ] [IsFiniteKernel κ] :
    (κ ∘ₘ μ) ⊗ₘ κ†μ = Kernel.swap α β ∘ₘ μ ⊗ₘ κ := by
  rw [compProd_posterior_eq_map_swap, Measure.comp_swap]

lemma swap_compProd_posterior (κ : Kernel α β) (μ : Measure α)
    [IsFiniteMeasure μ] [IsFiniteKernel κ] :
    Kernel.swap β α ∘ₘ (κ ∘ₘ μ) ⊗ₘ κ†μ = μ ⊗ₘ κ := by
  rw [compProd_posterior_eq_swap_comp, Measure.comp_assoc, Kernel.swap_swap, Measure.comp_id]

/--
The main property of the posterior, as equality of the following diagrams:
         -- id          -- κ
μ -- κ -|        =  μ -|
         -- κ†μ         -- id
-/
lemma parallelProd_posterior_comp_copy_comp (κ : Kernel α β) (μ : Measure α)
    [IsFiniteMeasure μ] [IsFiniteKernel κ] :
    (Kernel.id ∥ₖ κ†μ) ∘ₘ Kernel.copy β ∘ₘ κ ∘ₘ μ
      = (κ ∥ₖ Kernel.id) ∘ₘ Kernel.copy α ∘ₘ μ := by
  calc (Kernel.id ∥ₖ κ†μ) ∘ₘ Kernel.copy β ∘ₘ κ ∘ₘ μ
  _ = (κ ∘ₘ μ) ⊗ₘ κ†μ := by rw [← Measure.compProd_eq_parallelComp_comp_copy_comp]
  _ = Kernel.swap _ _ ∘ₘ (μ ⊗ₘ κ) := by rw [compProd_posterior_eq_swap_comp κ μ]
  _ = Kernel.swap _ _ ∘ₘ (Kernel.id ∥ₖ κ) ∘ₘ Kernel.copy α ∘ₘ μ := by
    rw [Measure.compProd_eq_parallelComp_comp_copy_comp]
  _ = (κ ∥ₖ Kernel.id) ∘ₘ Kernel.copy α ∘ₘ μ := by
    rw [Measure.comp_assoc, Kernel.swap_parallelComp, Measure.comp_assoc, Kernel.comp_assoc,
      Kernel.swap_copy, Measure.comp_assoc]

lemma posterior_prod_id_comp (κ : Kernel α β) (μ : Measure α)
    [IsFiniteMeasure μ] [IsFiniteKernel κ] :
    ((κ†μ) ×ₖ Kernel.id) ∘ₘ κ ∘ₘ μ = μ ⊗ₘ κ := by
  rw [← Kernel.swap_prod, ← Measure.comp_assoc, ← Measure.compProd_eq_comp_prod,
    compProd_posterior_eq_swap_comp, Measure.comp_assoc, Kernel.swap_swap, Measure.comp_id]

/-- The posterior is unique up to a `κ ∘ₘ μ`-null set. -/
lemma ae_eq_posterior_of_compProd_eq (η : Kernel β α) [IsFiniteKernel η]
    (h : (κ ∘ₘ μ) ⊗ₘ η = (μ ⊗ₘ κ).map Prod.swap) :
    η =ᵐ[κ ∘ₘ μ] κ†μ :=
  (Kernel.ae_eq_of_compProd_eq ((compProd_posterior_eq_map_swap _ _).trans h.symm)).symm

/-- The posterior is unique up to a `κ ∘ₘ μ`-null set. -/
lemma ae_eq_posterior_of_compProd_eq_swap_comp (η : Kernel β α) [IsFiniteKernel η]
    (h : ((κ ∘ₘ μ) ⊗ₘ η) = Kernel.swap α β ∘ₘ μ ⊗ₘ κ) :
    η =ᵐ[κ ∘ₘ μ] κ†μ :=
  ae_eq_posterior_of_compProd_eq η <| by rw [h, Measure.comp_swap]

@[simp]
lemma posterior_comp_self [IsMarkovKernel κ] : (κ†μ) ∘ₘ κ ∘ₘ μ = μ := by
  rw [← Measure.snd_compProd, compProd_posterior_eq_map_swap, Measure.snd_map_swap,
    Measure.fst_compProd]

/-- The posterior is involutive (up to `μ`-a.e. equality). -/
lemma posterior_posterior [StandardBorelSpace β] [Nonempty β] [IsMarkovKernel κ] :
    (κ†μ)†(κ ∘ₘ μ) =ᵐ[μ] κ := by
  suffices κ =ᵐ[(κ†μ) ∘ₘ κ ∘ₘ μ] (κ†μ)†(κ ∘ₘ μ) by
    rw [posterior_comp_self] at this
    filter_upwards [this] with a h using h.symm
  refine ae_eq_posterior_of_compProd_eq_swap_comp κ ?_
  rw [posterior_comp_self, compProd_posterior_eq_swap_comp κ μ, Measure.comp_assoc,
    Kernel.swap_swap, Measure.comp_id]

/-- The posterior of the identity kernel is the identity kernel. -/
lemma posterior_id (μ : Measure α) [IsFiniteMeasure μ] : Kernel.id†μ =ᵐ[μ] Kernel.id := by
  suffices Kernel.id =ᵐ[Kernel.id ∘ₘ μ] (Kernel.id : Kernel α α)†μ by
    rw [Measure.comp_id] at this
    filter_upwards [this] with a ha using ha.symm
  refine ae_eq_posterior_of_compProd_eq_swap_comp Kernel.id ?_
  rw [Measure.comp_id, Measure.compProd_id_eq_copy_comp, Measure.comp_assoc, Kernel.swap_copy]

/-- The posterior is contravariant. -/
lemma posterior_comp [StandardBorelSpace β] [Nonempty β] {η : Kernel β γ} [IsFiniteKernel η] :
    (η ∘ₖ κ)†μ =ᵐ[η ∘ₘ κ ∘ₘ μ] (κ†μ) ∘ₖ η†(κ ∘ₘ μ) := by
  rw [Measure.comp_assoc]
  refine (ae_eq_posterior_of_compProd_eq_swap_comp ((κ†μ) ∘ₖ η†(κ ∘ₘ μ)) ?_).symm
  simp_rw [Measure.compProd_eq_comp_prod, ← Kernel.parallelComp_comp_copy,
    Kernel.parallelComp_comp_right, ← Measure.comp_assoc]
  calc (Kernel.id ∥ₖ κ†μ) ∘ₘ (Kernel.id ∥ₖ η†(κ ∘ₘ μ)) ∘ₘ (Kernel.copy γ) ∘ₘ η ∘ₘ κ ∘ₘ μ
  _ = (Kernel.id ∥ₖ κ†μ) ∘ₘ (η ∥ₖ Kernel.id) ∘ₘ Kernel.copy β ∘ₘ κ ∘ₘ μ := by
    rw [parallelProd_posterior_comp_copy_comp]
  _ = (η ∥ₖ Kernel.id) ∘ₘ (Kernel.id ∥ₖ κ†μ) ∘ₘ Kernel.copy β ∘ₘ κ ∘ₘ μ := by
    rw [Measure.comp_assoc, Kernel.parallelComp_comm, ← Measure.comp_assoc]
  _ = (η ∥ₖ Kernel.id) ∘ₘ (κ ∥ₖ Kernel.id) ∘ₘ Kernel.copy α ∘ₘ μ := by
    rw [parallelProd_posterior_comp_copy_comp]
  _ = (Kernel.swap _ _) ∘ₘ (Kernel.id ∥ₖ η) ∘ₘ (Kernel.id ∥ₖ κ) ∘ₘ Kernel.copy α ∘ₘ μ := by
    simp_rw [Measure.comp_assoc]
    conv_rhs => rw [← Kernel.comp_assoc]
    rw [Kernel.swap_parallelComp, Kernel.comp_assoc, ← Kernel.comp_assoc (Kernel.swap α β),
      Kernel.swap_parallelComp, Kernel.comp_assoc, Kernel.swap_copy]

/-- For a deterministic kernel `κ`, `κ ∘ₖ (κ†μ)` is `μ.map f`-a.e. equal to the identity kernel. -/
lemma deterministic_comp_posterior [StandardBorelSpace β] [Nonempty β]
    {f : α → β} (hf : Measurable f) :
    Kernel.deterministic f hf ∘ₖ ((Kernel.deterministic f hf)†μ) =ᵐ[μ.map f] Kernel.id := by
  refine Kernel.ae_eq_of_compProd_eq ?_
  calc μ.map f ⊗ₘ (Kernel.deterministic f hf ∘ₖ Kernel.deterministic f hf†μ)
  _ = (Kernel.deterministic f hf ∘ₘ μ)
      ⊗ₘ (Kernel.deterministic f hf ∘ₖ Kernel.deterministic f hf†μ) := by
    rw [← Measure.comp_deterministic_eq_map hf]
  _ = (Kernel.id ∥ₖ Kernel.deterministic f hf) ∘ₘ (Kernel.id ∥ₖ Kernel.deterministic f hf†μ) ∘ₘ
      Kernel.copy β ∘ₘ Kernel.deterministic f hf ∘ₘ μ := by
    rw [Measure.compProd_eq_parallelComp_comp_copy_comp, Kernel.parallelComp_comp_right,
      ← Measure.comp_assoc]
  _ = (Kernel.id ∥ₖ Kernel.deterministic f hf) ∘ₘ (Kernel.deterministic f hf ∥ₖ Kernel.id) ∘ₘ
      Kernel.copy α ∘ₘ μ := by rw [parallelProd_posterior_comp_copy_comp]
  _ = (Kernel.deterministic f hf ∥ₖ Kernel.deterministic f hf) ∘ₘ Kernel.copy α ∘ₘ μ := by
    rw [Measure.comp_assoc, Kernel.parallelComp_comp_id_left_right]
  _ = (Kernel.copy β ∘ₖ Kernel.deterministic f hf) ∘ₘ μ := by -- `deterministic` is used here
    rw [Measure.comp_assoc, Kernel.deterministic_comp_copy]
  _ = μ.map f ⊗ₘ Kernel.id := by
    rw [Measure.compProd_id_eq_copy_comp, ← Measure.comp_assoc,
      Measure.comp_deterministic_eq_map hf]

end ProbabilityTheory
