/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Probability.Kernel.Composition.Basic

/-!

# Parallel composition of kernels

Two kernels `κ : Kernel α β` and `η : Kernel γ δ` can be applied in parallel to give a kernel
`κ ∥ₖ η` from `α × γ` to `β × δ`: `(κ ∥ₖ η) (a, c) = (κ a).prod (η c)`.

## Main definitions

* `parallelComp (κ : Kernel α β) (η : Kernel γ δ) : Kernel (α × γ) (β × δ)`: parallel composition
  of two s-finite kernels. We define a notation `κ ∥ₖ η = parallelComp κ η`.
  `∫⁻ bd, g bd ∂(κ ∥ₖ η) ac = ∫⁻ b, ∫⁻ d, g (b, d) ∂η ac.2 ∂κ ac.1`

## Main statements

* `parallelComp_comp_copy`: `(κ ∥ₖ η) ∘ₖ (copy α) = κ ×ₖ η`
* `deterministic_comp_copy`: for a deterministic kernel, copying then applying the kernel to
  the two copies is the same as first applying the kernel then copying. That is, if `κ` is
  a deterministic kernel, `(κ ∥ₖ κ) ∘ₖ copy α = copy β ∘ₖ κ`.

## Notations

* `κ ∥ₖ η = ProbabilityTheory.Kernel.parallelComp κ η`

## Implementation notes

Our formalization of kernels is centered around the composition-product: the product and then the
parallel composition are defined as special cases of the composition-product.
We could have alternatively used the building blocks of kernels seen as a Markov category:
composition, parallel composition (or tensor product) and the deterministic kernels `id`, `copy`,
`swap` and `discard`. The product and composition-product could then be built from these.

-/

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}

section ParallelComp

/-- Parallel product of two kernels. -/
noncomputable
def parallelComp (κ : Kernel α β) (η : Kernel γ δ) : Kernel (α × γ) (β × δ) :=
  (prodMkRight γ κ) ×ₖ (prodMkLeft α η)

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " ∥ₖ " => ProbabilityTheory.Kernel.parallelComp

lemma parallelComp_apply (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel γ δ) [IsSFiniteKernel η] (x : α × γ) :
    (κ ∥ₖ η) x = (κ x.1).prod (η x.2) := by
  rw [parallelComp, prod_apply, prodMkRight_apply, prodMkLeft_apply]

lemma lintegral_parallelComp (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel γ δ) [IsSFiniteKernel η]
    (ac : α × γ) {g : β × δ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ bd, g bd ∂(κ ∥ₖ η) ac = ∫⁻ b, ∫⁻ d, g (b, d) ∂η ac.2 ∂κ ac.1 := by
  rw [parallelComp, lintegral_prod _ _ _ hg]
  simp

instance (κ : Kernel α β) (η : Kernel γ δ) : IsSFiniteKernel (κ ∥ₖ η) := by
  rw [parallelComp]; infer_instance

instance (κ : Kernel α β) [IsFiniteKernel κ] (η : Kernel γ δ) [IsFiniteKernel η] :
    IsFiniteKernel (κ ∥ₖ η) := by
  rw [parallelComp]; infer_instance

instance (κ : Kernel α β) [IsMarkovKernel κ] (η : Kernel γ δ) [IsMarkovKernel η] :
    IsMarkovKernel (κ ∥ₖ η) := by
  rw [parallelComp]; infer_instance

instance (κ : Kernel α β) [IsZeroOrMarkovKernel κ] (η : Kernel γ δ) [IsZeroOrMarkovKernel η] :
    IsZeroOrMarkovKernel (κ ∥ₖ η) := by
  rw [parallelComp]; infer_instance

lemma parallelComp_comp_copy (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel α γ) [IsSFiniteKernel η] :
    (κ ∥ₖ η) ∘ₖ (copy α) = κ ×ₖ η := by
  ext a s hs
  simp_rw [prod_apply, comp_apply, copy_apply, Measure.bind_apply hs (Kernel.measurable _)]
  rw [lintegral_dirac']
  swap; · exact Kernel.measurable_coe _ hs
  rw [parallelComp_apply]

lemma swap_parallelComp {κ : Kernel α β} [IsSFiniteKernel κ]
    {η : Kernel γ δ} [IsSFiniteKernel η] :
    (swap β δ) ∘ₖ (κ ∥ₖ η) = (η ∥ₖ κ) ∘ₖ (swap α γ) := by
  rw [parallelComp, swap_prod, parallelComp]
  ext ac s hs
  rw [comp_apply, swap_apply, Measure.bind_apply hs (Kernel.measurable _),
    lintegral_dirac' _ (Kernel.measurable_coe _ hs), prod_apply, prod_apply, prodMkLeft_apply,
    prodMkLeft_apply, prodMkRight_apply, prodMkRight_apply, Prod.fst_swap, Prod.snd_swap]

/-- For a deterministic kernel, copying then applying the kernel to the two copies is the same
as first applying the kernel then copying. -/
lemma deterministic_comp_copy {f : α → β} (hf : Measurable f) :
    (Kernel.deterministic f hf ∥ₖ Kernel.deterministic f hf) ∘ₖ Kernel.copy α
      = Kernel.copy β ∘ₖ Kernel.deterministic f hf := by
  simp_rw [Kernel.parallelComp_comp_copy, Kernel.deterministic_prod_deterministic,
    Kernel.copy, Kernel.deterministic_comp_deterministic, Function.comp_def]

end ParallelComp

end ProbabilityTheory.Kernel
