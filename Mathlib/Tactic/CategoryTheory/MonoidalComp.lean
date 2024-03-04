/-
Copyright (c) 2022. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Yuma Mizuno, Oleksandr Manzyuk
-/
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Monoidal composition `⊗≫` (composition up to associators)

We provide `f ⊗≫ g`, the `monoidal_comp` operation,
which automatically inserts associators and unitors as needed
to make the target of `f` match the source of `g`.
-/

universe v u

open CategoryTheory MonoidalCategory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

open scoped MonoidalCategory

/--
A typeclass carrying a choice of monoidal structural isomorphism between two objects.
Used by the `⊗≫` monoidal composition operator, and the `coherence` tactic.
-/
-- We could likely turn this into a `Prop` valued existential if that proves useful.
class MonoidalCoherence (X Y : C) where
  hom : X ⟶ Y
  [isIso : IsIso hom]

attribute [instance] MonoidalCoherence.isIso

namespace MonoidalCoherence

@[simps]
instance refl (X : C) : MonoidalCoherence X X := ⟨𝟙 _⟩

@[simps]
instance whiskerLeft (X Y Z : C) [MonoidalCoherence Y Z] :
    MonoidalCoherence (X ⊗ Y) (X ⊗ Z) :=
  ⟨𝟙 X ⊗ MonoidalCoherence.hom⟩

@[simps]
instance whiskerRight (X Y Z : C) [MonoidalCoherence X Y] :
    MonoidalCoherence (X ⊗ Z) (Y ⊗ Z) :=
  ⟨MonoidalCoherence.hom ⊗ 𝟙 Z⟩

@[simps]
instance tensor_right (X Y : C) [MonoidalCoherence (𝟙_ C) Y] :
    MonoidalCoherence X (X ⊗ Y) :=
  ⟨(ρ_ X).inv ≫ (𝟙 X ⊗  MonoidalCoherence.hom)⟩

@[simps]
instance tensor_right' (X Y : C) [MonoidalCoherence Y (𝟙_ C)] :
    MonoidalCoherence (X ⊗ Y) X :=
  ⟨(𝟙 X ⊗ MonoidalCoherence.hom) ≫ (ρ_ X).hom⟩

@[simps]
instance left (X Y : C) [MonoidalCoherence X Y] :
    MonoidalCoherence (𝟙_ C ⊗ X) Y :=
  ⟨(λ_ X).hom ≫ MonoidalCoherence.hom⟩

@[simps]
instance left' (X Y : C) [MonoidalCoherence X Y] :
    MonoidalCoherence X (𝟙_ C ⊗ Y) :=
  ⟨MonoidalCoherence.hom ≫ (λ_ Y).inv⟩

@[simps]
instance right (X Y : C) [MonoidalCoherence X Y] :
    MonoidalCoherence (X ⊗ 𝟙_ C) Y :=
  ⟨(ρ_ X).hom ≫ MonoidalCoherence.hom⟩

@[simps]
instance right' (X Y : C) [MonoidalCoherence X Y] :
    MonoidalCoherence X (Y ⊗ 𝟙_ C) :=
  ⟨MonoidalCoherence.hom ≫ (ρ_ Y).inv⟩

@[simps]
instance assoc (X Y Z W : C) [MonoidalCoherence (X ⊗ (Y ⊗ Z)) W] :
    MonoidalCoherence ((X ⊗ Y) ⊗ Z) W :=
  ⟨(α_ X Y Z).hom ≫ MonoidalCoherence.hom⟩

@[simps]
instance assoc' (W X Y Z : C) [MonoidalCoherence W (X ⊗ (Y ⊗ Z))] :
    MonoidalCoherence W ((X ⊗ Y) ⊗ Z) :=
  ⟨MonoidalCoherence.hom ≫ (α_ X Y Z).inv⟩

end MonoidalCoherence

noncomputable section

/-- Construct an isomorphism between two objects in a monoidal category
out of unitors and associators. -/
def monoidalIso (X Y : C) [MonoidalCoherence X Y] : X ≅ Y :=
  asIso MonoidalCoherence.hom

/-- Notation for identities up to unitors and associators. -/
scoped[CategoryTheory.MonoidalCategory] notation " ⊗𝟙 " =>
  MonoidalCoherence.hom -- type as \ot 𝟙

/-- Compose two morphisms in a monoidal category,
inserting unitors and associators between as necessary. -/
def monoidalComp {W X Y Z : C} [MonoidalCoherence X Y] (f : W ⟶ X) (g : Y ⟶ Z) : W ⟶ Z :=
  f ≫ ⊗𝟙 ≫ g

@[inherit_doc monoidalComp]
scoped[CategoryTheory.MonoidalCategory] infixr:80 " ⊗≫ " =>
  monoidalComp -- type as \ot \gg

@[simp] lemma monoidalComp_refl {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ⊗≫ g = f ≫ g := by
  simp [monoidalComp]

/-- Compose two isomorphisms in a monoidal category,
inserting unitors and associators between as necessary. -/
def monoidalIsoComp {W X Y Z : C} [MonoidalCoherence X Y] (f : W ≅ X) (g : Y ≅ Z) : W ≅ Z :=
  f ≪≫ asIso MonoidalCoherence.hom ≪≫ g

@[inherit_doc monoidalIsoComp]
scoped[CategoryTheory.MonoidalCategory] infixr:80 " ≪⊗≫ " =>
  monoidalIsoComp -- type as \ll \ot \gg
