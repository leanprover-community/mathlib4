/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Yuma Mizuno, Oleksandr Manzyuk
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Util.CompileInductive

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

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

open scoped MonoidalCategory

/--
A typeclass carrying a choice of monoidal structural isomorphism between two objects.
Used by the `⊗≫` monoidal composition operator, and the `coherence` tactic.
-/
-- We could likely turn this into a `Prop`-valued existential if that proves useful.
class MonoidalCoherence (X Y : C) where
  /-- A monoidal structural isomorphism between two objects. -/
  iso : X ≅ Y

/-- Notation for identities up to unitors and associators. -/
scoped[CategoryTheory.MonoidalCategory] notation " ⊗𝟙 " =>
  MonoidalCoherence.iso -- type as \ot 𝟙

/-- Construct an isomorphism between two objects in a monoidal category
out of unitors and associators. -/
abbrev monoidalIso (X Y : C) [MonoidalCoherence X Y] : X ≅ Y := MonoidalCoherence.iso

/-- Compose two morphisms in a monoidal category,
inserting unitors and associators between as necessary. -/
def monoidalComp {W X Y Z : C} [MonoidalCoherence X Y] (f : W ⟶ X) (g : Y ⟶ Z) : W ⟶ Z :=
  f ≫ ⊗𝟙.hom ≫ g

@[inherit_doc monoidalComp]
scoped[CategoryTheory.MonoidalCategory] infixr:80 " ⊗≫ " =>
  monoidalComp -- type as \ot \gg

/-- Compose two isomorphisms in a monoidal category,
inserting unitors and associators between as necessary. -/
def monoidalIsoComp {W X Y Z : C} [MonoidalCoherence X Y] (f : W ≅ X) (g : Y ≅ Z) : W ≅ Z :=
  f ≪≫ ⊗𝟙 ≪≫ g

@[inherit_doc monoidalIsoComp]
scoped[CategoryTheory.MonoidalCategory] infixr:80 " ≪⊗≫ " =>
  monoidalIsoComp -- type as \ll \ot \gg

namespace MonoidalCoherence

variable [MonoidalCategory C]

@[simps]
instance refl (X : C) : MonoidalCoherence X X := ⟨Iso.refl _⟩

@[simps]
instance whiskerLeft (X Y Z : C) [MonoidalCoherence Y Z] :
    MonoidalCoherence (X ⊗ Y) (X ⊗ Z) :=
  ⟨whiskerLeftIso X ⊗𝟙⟩

@[simps]
instance whiskerRight (X Y Z : C) [MonoidalCoherence X Y] :
    MonoidalCoherence (X ⊗ Z) (Y ⊗ Z) :=
  ⟨whiskerRightIso ⊗𝟙 Z⟩

@[simps]
instance tensor_right (X Y : C) [MonoidalCoherence (𝟙_ C) Y] :
    MonoidalCoherence X (X ⊗ Y) :=
  ⟨(ρ_ X).symm ≪≫ (whiskerLeftIso X ⊗𝟙)⟩

@[simps]
instance tensor_right' (X Y : C) [MonoidalCoherence Y (𝟙_ C)] :
    MonoidalCoherence (X ⊗ Y) X :=
  ⟨whiskerLeftIso X ⊗𝟙 ≪≫ (ρ_ X)⟩

@[simps]
instance left (X Y : C) [MonoidalCoherence X Y] :
    MonoidalCoherence (𝟙_ C ⊗ X) Y :=
  ⟨λ_ X ≪≫ ⊗𝟙⟩

@[simps]
instance left' (X Y : C) [MonoidalCoherence X Y] :
    MonoidalCoherence X (𝟙_ C ⊗ Y) :=
  ⟨⊗𝟙 ≪≫ (λ_ Y).symm⟩

@[simps]
instance right (X Y : C) [MonoidalCoherence X Y] :
    MonoidalCoherence (X ⊗ 𝟙_ C) Y :=
  ⟨ρ_ X ≪≫ ⊗𝟙⟩

@[simps]
instance right' (X Y : C) [MonoidalCoherence X Y] :
    MonoidalCoherence X (Y ⊗ 𝟙_ C) :=
  ⟨⊗𝟙 ≪≫ (ρ_ Y).symm⟩

@[simps]
instance assoc (X Y Z W : C) [MonoidalCoherence (X ⊗ (Y ⊗ Z)) W] :
    MonoidalCoherence ((X ⊗ Y) ⊗ Z) W :=
  ⟨α_ X Y Z ≪≫ ⊗𝟙⟩

@[simps]
instance assoc' (W X Y Z : C) [MonoidalCoherence W (X ⊗ (Y ⊗ Z))] :
    MonoidalCoherence W ((X ⊗ Y) ⊗ Z) :=
  ⟨⊗𝟙 ≪≫ (α_ X Y Z).symm⟩

end MonoidalCoherence

@[simp] lemma monoidalComp_refl {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ⊗≫ g = f ≫ g := by
  simp [monoidalComp]

end CategoryTheory
