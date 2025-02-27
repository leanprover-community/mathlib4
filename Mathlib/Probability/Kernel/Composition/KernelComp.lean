/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Composition.ParallelComp
import Mathlib.MeasureTheory.MeasurableSpace.Coherence

/-!
# Monoidal composition `⊗≫` (composition up to associators)
We provide `f ⊗≫ g`, the `monoidalComp` operation,
which automatically inserts associators and unitors as needed
to make the target of `f` match the source of `g`.
## Example
Suppose we have a braiding morphism `R X Y : X ⊗ Y ⟶ Y ⊗ X` in a monoidal category, and that we
want to define the morphism with the type `V₁ ⊗ V₂ ⊗ V₃ ⊗ V₄ ⊗ V₅ ⟶ V₁ ⊗ V₃ ⊗ V₂ ⊗ V₄ ⊗ V₅` that
transposes the second and third components by `R V₂ V₃`. How to do this? The first guess would be
to use the whiskering operators `◁` and `▷`, and define the morphism as `V₁ ◁ R V₂ V₃ ▷ V₄ ▷ V₅`.
However, this morphism has the type `V₁ ⊗ ((V₂ ⊗ V₃) ⊗ V₄) ⊗ V₅ ⟶ V₁ ⊗ ((V₃ ⊗ V₂) ⊗ V₄) ⊗ V₅`,
which is not what we need. We should insert suitable associators. The desired associators can,
in principle, be defined by using the primitive three-components associator
`α_ X Y Z : (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)` as a building block, but writing down actual definitions
are quite tedious, and we usually don't want to see them.
The monoidal composition `⊗≫` is designed to solve such a problem. In this case, we can define the
desired morphism as `𝟙 _ ⊗≫ V₁ ◁ R V₂ V₃ ▷ V₄ ▷ V₅ ⊗≫ 𝟙 _`, where the first and the second `𝟙 _`
are completed as `𝟙 (V₁ ⊗ V₂ ⊗ V₃ ⊗ V₄ ⊗ V₅)` and `𝟙 (V₁ ⊗ V₃ ⊗ V₂ ⊗ V₄ ⊗ V₅)`, respectively.
-/

open MeasureTheory

namespace ProbabilityTheory

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}

@[simp]
lemma deterministic_measurableEquiv_refl [MeasurableSpace α] :
    Kernel.deterministic (MeasurableEquiv.refl α) (mβ := inferInstance) measurable_id
      = Kernel.id := rfl

/-- Compose two morphisms in a monoidal category,
inserting unitors and associators between as necessary. -/
noncomputable
def kernelComp [MeasurableCoherence β γ] (g : Kernel γ δ) (f : Kernel α β) : Kernel α δ :=
  g ∘ₖ (Kernel.deterministic ⊗𝟙ₘ (MeasurableEquiv.measurable _)) ∘ₖ f

@[inherit_doc kernelComp]
scoped[ProbabilityTheory] infixr:80 " ∘𝟙ₖ " => ProbabilityTheory.kernelComp

@[simp] lemma kernelComp_refl (f : Kernel α β) (g : Kernel β γ) :
    g ∘𝟙ₖ f = g ∘ₖ f := by simp [kernelComp]

noncomputable
example (κ : Kernel α (α × β × γ)) (η : Kernel ((α × Unit × β) × γ) δ) : Kernel α δ := η ∘𝟙ₖ κ

end ProbabilityTheory
