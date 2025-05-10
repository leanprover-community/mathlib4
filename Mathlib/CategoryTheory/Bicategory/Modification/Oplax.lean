/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Oplax

/-!
# Modifications between oplax transformations

A modification `Γ` between oplax transformations `η` and `θ` consists of a family of 2-morphisms
`Γ.app a : η.app a ⟶ θ.app a`, which for all 1-morphisms `f : a ⟶ b` satisfies the equation
`(F.map f ◁ app b) ≫ θ.naturality f = η.naturality f ≫ app a ▷ G.map f`.

## Main definitions

* `Modification η θ` : modifications between oplax transformations `η` and `θ`.
* `Oplax.homcategory F G` : the category structure on oplax transformations
  between `F` and `G`, where the morphisms are modifications, and composition is given by vertical
  composition of modifications.

-/

namespace CategoryTheory.Oplax

open Category Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
  {F G : OplaxFunctor B C} (η θ : F ⟶ G)

variable {F G : OplaxFunctor B C}

/-- A modification `Γ` between oplax natural transformations `η` and `θ` consists of a family of
2-morphisms `Γ.app a : η.app a ⟶ θ.app a`, which satisfies the equation
`(F.map f ◁ app b) ≫ θ.naturality f = η.naturality f ≫ (app a ▷ G.map f)`
for each 1-morphism `f : a ⟶ b`.
-/
@[ext]
structure Modification (η θ : F ⟶ G) where
  /-- The underlying family of 2-morphisms. -/
  app (a : B) : η.app a ⟶ θ.app a
  /-- The naturality condition. -/
  naturality :
    ∀ {a b : B} (f : a ⟶ b),
      F.map f ◁ app b ≫ θ.naturality f = η.naturality f ≫ app a ▷ G.map f := by aesop_cat

attribute [reassoc (attr := simp)] Modification.naturality

variable {η θ ι : F ⟶ G}

namespace Modification

section

variable (Γ : Modification η θ) {a b c : B} {a' : C}

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality (f : a' ⟶ F.obj b) (g : b ⟶ c) :
    f ◁ F.map g ◁ Γ.app c ≫ f ◁ θ.naturality g = f ◁ η.naturality g ≫ f ◁ Γ.app b ▷ G.map g := by
  simp_rw [← Bicategory.whiskerLeft_comp, naturality]

@[reassoc (attr := simp)]
theorem whiskerRight_naturality (f : a ⟶ b) (g : G.obj b ⟶ a') :
    F.map f ◁ Γ.app b ▷ g ≫ (α_ _ _ _).inv ≫ θ.naturality f ▷ g =
      (α_ _ _ _).inv ≫ η.naturality f ▷ g ≫ Γ.app a ▷ G.map f ▷ g := by
  simp_rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight, naturality]

end

end Modification

/-- Category structure on the oplax natural transformations between OplaxFunctors. -/
@[simps]
instance homcategory (F G : OplaxFunctor B C) : Category (F ⟶ G) where
  Hom := Modification
  id η := { app := fun a ↦ 𝟙 (η.app a) }
  comp Γ Δ := { app := fun a => Γ.app a ≫ Δ.app a }

instance : Inhabited (Modification η η) :=
  ⟨𝟙 η⟩

@[ext]
lemma homcategory.ext {F G : OplaxFunctor B C} {α β : F ⟶ G} {m n : α ⟶ β}
    (w : ∀ b, m.app b = n.app b) : m = n :=
  Modification.ext (funext w)

/-- Construct a modification isomorphism between oplax natural transformations
by giving object level isomorphisms, and checking naturality only in the forward direction.
-/
@[simps]
def ModificationIso.ofComponents (app : ∀ a, η.app a ≅ θ.app a)
    (naturality :
      ∀ {a b} (f : a ⟶ b),
        F.map f ◁ (app b).hom ≫ θ.naturality f = η.naturality f ≫ (app a).hom ▷ G.map f) :
    η ≅ θ where
  hom := { app := fun a => (app a).hom }
  inv :=
    { app := fun a => (app a).inv
      naturality := fun {a b} f => by
        simpa using congr_arg (fun f => _ ◁ (app b).inv ≫ f ≫ (app a).inv ▷ _) (naturality f).symm }

end CategoryTheory.Oplax
