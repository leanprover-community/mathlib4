/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

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

namespace MeasureTheory

section Move

def Equiv.prodUnit_right (α : Type*) : α × Unit ≃ α where
  toFun := Prod.fst
  invFun := fun a ↦ (a, ())
  left_inv _ := rfl
  right_inv _ := rfl

def Equiv.prodUnit_left (α : Type*) : Unit × α ≃ α where
  toFun := Prod.snd
  invFun := fun a ↦ ((), a)
  left_inv _ := rfl
  right_inv _ := rfl

def MeasurableEquiv.prodUnit_right (α : Type*) [MeasurableSpace α] : α × Unit ≃ᵐ α where
  toEquiv := Equiv.prodUnit_right α
  measurable_toFun := measurable_fst
  measurable_invFun := measurable_prod_mk_right

def MeasurableEquiv.prodUnit_left (α : Type*) [MeasurableSpace α] : Unit × α ≃ᵐ α where
  toEquiv := Equiv.prodUnit_left α
  measurable_toFun := measurable_snd
  measurable_invFun := measurable_prod_mk_left

end Move

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}

/-- A typeclass carrying a choice of monoidal structural isomorphism between two objects.
Used by the `⊗≫` monoidal composition operator, and the `coherence` tactic. -/
class MeasurableCoherence (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] where
  /-- A monoidal structural isomorphism between two objects. -/
  measurableEquiv : α ≃ᵐ β

/-- Notation for identities up to unitors and associators. -/
scoped[MeasureTheory] notation " ⊗𝟙ₘ " => MeasureTheory.MeasurableCoherence.measurableEquiv

/-- Construct an isomorphism between two objects in a monoidal category
out of unitors and associators. -/
abbrev measurableEquiv (α β : Type*) [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableCoherence α β] :
    α ≃ᵐ β := MeasurableCoherence.measurableEquiv

/-- Compose two isomorphisms in a monoidal category,
inserting unitors and associators between as necessary. -/
def measurableEquivComp [MeasurableCoherence β γ] (f : α ≃ᵐ β) (g : γ ≃ᵐ δ) : α ≃ᵐ δ :=
  f.trans (⊗𝟙ₘ.trans g)

@[inherit_doc measurableEquivComp]
scoped[MeasureTheory] infixr:80 " ⊗≃ᵐ " => MeasureTheory.measurableEquivComp

namespace MeasurableCoherence

@[simps]
instance refl (α : Type*) [MeasurableSpace α] : MeasurableCoherence α α := ⟨MeasurableEquiv.refl _⟩

@[simps]
instance whiskerLeft (α β γ : Type*) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableCoherence β γ] :
    MeasurableCoherence (α × β) (α × γ) :=
  ⟨MeasurableEquiv.prodCongr (MeasurableEquiv.refl α) ⊗𝟙ₘ⟩

@[simps]
instance whiskerRight (α β γ : Type*) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableCoherence α β] :
    MeasurableCoherence (α × γ) (β × γ) :=
  ⟨MeasurableEquiv.prodCongr ⊗𝟙ₘ (MeasurableEquiv.refl γ)⟩

@[simps]
instance tensor_right (α β : Type*) [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableCoherence Unit β] :
    MeasurableCoherence α (α × β) :=
  ⟨(MeasurableEquiv.prodUnit_right α).symm.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl α) ⊗𝟙ₘ)⟩

@[simps]
instance tensor_right' (α β : Type*) [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableCoherence β Unit] :
    MeasurableCoherence (α × β) α :=
  ⟨(MeasurableEquiv.prodCongr (MeasurableEquiv.refl α) ⊗𝟙ₘ).trans
    (MeasurableEquiv.prodUnit_right α)⟩

@[simps]
instance left (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] [MeasurableCoherence α β] :
    MeasurableCoherence (Unit × α) β :=
  ⟨(MeasurableEquiv.prodUnit_left α).trans ⊗𝟙ₘ⟩

@[simps]
instance left' (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] [MeasurableCoherence α β] :
    MeasurableCoherence α (Unit × β) :=
  ⟨⊗𝟙ₘ.trans (MeasurableEquiv.prodUnit_left β).symm⟩

@[simps]
instance right (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] [MeasurableCoherence α β] :
    MeasurableCoherence (α × Unit) β :=
  ⟨(MeasurableEquiv.prodUnit_right α).trans ⊗𝟙ₘ⟩

@[simps]
instance right' (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] [MeasurableCoherence α β] :
    MeasurableCoherence α (β × Unit) :=
  ⟨⊗𝟙ₘ.trans (MeasurableEquiv.prodUnit_right β).symm⟩

@[simps]
instance assoc (α β γ δ : Type*) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] [MeasurableCoherence (α × (β × γ)) δ] :
    MeasurableCoherence ((α × β) × γ) δ :=
  ⟨MeasurableEquiv.prodAssoc.trans ⊗𝟙ₘ⟩

@[simps]
instance assoc' (α β γ δ : Type*) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] [MeasurableCoherence δ (α × (β × γ))] :
    MeasurableCoherence δ ((α × β) × γ) :=
  ⟨⊗𝟙ₘ.trans MeasurableEquiv.prodAssoc.symm⟩

end MeasurableCoherence

end MeasureTheory
