/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
import Mathlib.CategoryTheory.Bicategory.Modification.Oplax


/-!
# Modifications between strong transformations of pseudofunctors

A modification `Γ` between strong transformations `η` and `θ` consists of a family of
2-morphisms `Γ.app a : η.app a ⟶ θ.app a`, which satisfies the equation
`(F.map f ◁ app b) ≫ θ.naturality f = η.naturality f ≫ (app a ▷ G.map f)`
for each 1-morphism `f : a ⟶ b`.

## Main definitions

* `Modification η θ` : modifications between strong transformations `η` and `θ`
* `Modification.vcomp η θ` : the vertical composition of strong transformations `η`
  and `θ`
* `Pseudofunctor.category F G` : the category structure on the strong transformations
  between `F` and `G`

-/

namespace CategoryTheory.Pseudofunctor

open Category Bicategory

open scoped Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
  {F G : Pseudofunctor B C} (η θ : F ⟶ G)

/-- A modification `Γ` between strong transformations `η` and `θ` consists of a family of
2-morphisms `Γ.app a : η.app a ⟶ θ.app a`, which satisfies the equation
`(F.map f ◁ app b) ≫ θ.naturality f = η.naturality f ≫ (app a ▷ G.map f)`
for each 1-morphism `f : a ⟶ b`.
-/
@[ext]
structure Modification where
  /-- The underlying family of 2-morphism. -/
  app (a : B) : η.app a ⟶ θ.app a
  /-- The naturality condition. -/
  naturality :
    ∀ {a b : B} (f : a ⟶ b),
      F.map f ◁ app b ≫ (θ.naturality f).hom =
        (η.naturality f).hom ≫ app a ▷ G.map f := by aesop_cat

attribute [reassoc (attr := simp)] Modification.naturality

namespace Modification

/-- The identity modification. -/
@[simps]
def id : Modification η η where app a := 𝟙 (η.app a)

instance : Inhabited (Modification η η) :=
  ⟨Modification.id η⟩

variable {η θ} {ι : F ⟶ G}
variable (Γ : Modification η θ)

-- TODO: add coercion for strong transformations? (or is it not infered here?)
/-- The modification between the underlying oplax transformations of oplax functors -/
@[simps]
def toOplax : Oplax.Modification η.toOplax θ.toOplax where
  app a := Γ.app a

instance hasCoeToOplax : Coe (Modification η θ) (Oplax.Modification η.toOplax θ.toOplax) :=
  ⟨toOplax⟩

/-- The modification between strong transformations of pseudofunctors associated to a modification
between the underlying oplax transformations of oplax functors. -/
@[simps]
def mkOfOplax (Γ : Oplax.Modification η.toOplax θ.toOplax) : Modification η θ where
  app a := Γ.app a
  naturality f := by simpa using Γ.naturality f

section

variable {a b c : B} {a' : C}

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality (f : a' ⟶ F.obj b) (g : b ⟶ c) :
    f ◁ F.map g ◁ Γ.app c ≫ f ◁ (θ.naturality g).hom =
      f ◁ (η.naturality g).hom ≫ f ◁ Γ.app b ▷ G.map g := by
  simp_rw [← whiskerLeft_comp, naturality]

@[reassoc (attr := simp)]
theorem whiskerRight_naturality (f : a ⟶ b) (g : G.obj b ⟶ a') :
    F.map f ◁ Γ.app b ▷ g ≫ (α_ _ _ _).inv ≫ (θ.naturality f).hom ▷ g =
      (α_ _ _ _).inv ≫ (η.naturality f).hom ▷ g ≫ Γ.app a ▷ G.map f ▷ g := by
  simp_rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight, naturality]

end

/-- Vertical composition of modifications. -/
@[simps]
def vcomp (Δ : Modification θ ι) : Modification η ι where
  app a := Γ.app a ≫ Δ.app a

end Modification

/-- Category structure on the strong transformations between pseudofunctors. -/
@[simps]
instance homcategory (F G : Pseudofunctor B C) : Category (F ⟶ G) where
  Hom := Modification
  id := Modification.id
  comp := Modification.vcomp

@[ext]
lemma homcategory.ext {F G : Pseudofunctor B C} {α β : F ⟶ G} {m n : α ⟶ β}
    (w : ∀ b, m.app b = n.app b) : m = n := by
  apply Modification.ext
  ext
  apply w

@[simp]
lemma Modification.id_app' {X : B} {F G : Pseudofunctor B C} (α : F ⟶ G) :
    Modification.app (𝟙 α) X = 𝟙 (α.app X) :=
  rfl

@[simp]
lemma Modification.comp_app' {X : B} {F G : Pseudofunctor B C} {α β γ : F ⟶ G}
    (m : α ⟶ β) (n : β ⟶ γ) : (m ≫ n).app X = m.app X ≫ n.app X :=
  rfl

variable {η θ}

/-- Construct a modification isomorphism between strong transformations
by giving object level isomorphisms, and checking naturality only in the forward direction.
-/
@[simps]
def ModificationIso.ofComponents (app : ∀ a, η.app a ≅ θ.app a)
    (naturality : ∀ {a b} (f : a ⟶ b),
      F.map f ◁ (app b).hom ≫ (θ.naturality f).hom =
        (η.naturality f).hom ≫ (app a).hom ▷ G.map f) :
    η ≅ θ where
  hom := { app := fun a => (app a).hom }
  inv :=
    { app := fun a => (app a).inv
      naturality := fun {a b} f => by
        simpa using
          congr_arg (fun f => _ ◁ (app b).inv ≫ f ≫ (app a).inv ▷ _) (naturality f).symm }

-- open Oplax in
-- def ModificationIso.ofOplax (Γ : η.toOplax ≅ θ.toOplax) : η ≅ θ :=
--   ModificationIso.ofComponents (fun a => Γ.app a) Γ.naturality

end CategoryTheory.Pseudofunctor
