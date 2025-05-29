/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Oplax

/-!
# Modifications between transformations of oplax functors

In this file we define modifications of oplax and strong transformations of oplax functors.

A modification `Γ` between oplax transformations `η` and `θ` (of oplax functors) consists of a
family of 2-morphisms `Γ.app a : η.app a ⟶ θ.app a`, which for all 1-morphisms `f : a ⟶ b`
satisfies the equation `(F.map f ◁ app b) ≫ θ.naturality f = η.naturality f ≫ app a ▷ G.map f`.

Modifications between strong transformations are defined similarly.

## Main definitions

Given two oplax functors `F` and `G`, we define:

* `OplaxTrans.Modification η θ`: modifications between oplax transformations `η` and `θ` between
  `F` and `G`.
* `OplaxTrans.homCategory F G`: the category structure on the oplax transformations
  between `F` and `G`, where composition is given by vertical composition.

* `StrongTrans.Modification η θ`: modifications between oplax transformations `η` and `θ` between
  `F` and `G`.
* `StrongTrans.homCategory F G`: the category structure on the strong transformations
  between `F` and `G`, where composition is given by vertical composition.

## TODO
* Once lax transformations between oplax functors are defined, we should also define
  modifications between lax transformations.

-/

namespace CategoryTheory.Oplax

open Category Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
  {F G : OplaxFunctor B C}

namespace OplaxTrans

variable (η θ : F ⟶ G)

/-- A modification `Γ` between oplax natural transformations `η` and `θ` consists of a family of
2-morphisms `Γ.app a : η.app a ⟶ θ.app a`, which satisfies the equation
`(F.map f ◁ app b) ≫ θ.naturality f = η.naturality f ≫ (app a ▷ G.map f)`
for each 1-morphism `f : a ⟶ b`.
-/
@[ext]
structure Modification where
  /-- The underlying family of 2-morphisms. -/
  app (a : B) : η.app a ⟶ θ.app a
  /-- The naturality condition. -/
  naturality {a b : B} (f : a ⟶ b) :
    F.map f ◁ app b ≫ θ.naturality f = η.naturality f ≫ app a ▷ G.map f := by aesop_cat

attribute [reassoc (attr := simp)] Modification.naturality

variable {η θ}

namespace Modification

section

variable (Γ : Modification η θ) {a b c : B} {a' : C}

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality (f : a' ⟶ F.obj b) (g : b ⟶ c) :
    f ◁ F.map g ◁ Γ.app c ≫ f ◁ θ.naturality g =
      f ◁ η.naturality g ≫ f ◁ Γ.app b ▷ G.map g := by
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
instance homCategory (F G : OplaxFunctor B C) : Category (OplaxTrans F G) where
  Hom := Modification
  id η := { app := fun a ↦ 𝟙 (η.app a) }
  comp Γ Δ := { app := fun a => Γ.app a ≫ Δ.app a }

-- TODO: FIX
variable {η θ : OplaxTrans F G}

instance : Inhabited (Modification η η) :=
  ⟨𝟙 η⟩

@[ext]
lemma homCategory.ext {α β : OplaxTrans F G} {m n : α ⟶ β} (w : ∀ b, m.app b = n.app b) : m = n :=
  Modification.ext (funext w)

/-- Construct a modification isomorphism between oplax natural transformations
by giving object level isomorphisms, and checking naturality only in the forward direction.
-/
@[simps]
def ModificationIso.ofComponents (app : ∀ a, η.app a ≅ θ.app a)
    (naturality : ∀ {a b} (f : a ⟶ b),
      F.map f ◁ (app b).hom ≫ θ.naturality f =
        η.naturality f ≫ (app a).hom ▷ G.map f := by aesop_cat) : η ≅ θ where
  hom := { app := fun a => (app a).hom }
  inv :=
    { app := fun a => (app a).inv
      naturality := fun {a b} f => by
        simpa using congr_arg (fun f => _ ◁ (app b).inv ≫ f ≫ (app a).inv ▷ _)
          (naturality f).symm }

end OplaxTrans

namespace StrongTrans

variable (η θ : F ⟶ G)

/-- A modification `Γ` between strong natural transformations `η` and `θ` (between oplax functors)
consists of a family of 2-morphisms `Γ.app a : η.app a ⟶ θ.app a`, which satisfies the equation
`(F.map f ◁ app b) ≫ (θ.naturality f).hom = (η.naturality f).hom ≫ (app a ▷ G.map f)`
for each 1-morphism `f : a ⟶ b`.
-/
@[ext]
structure Modification where
  /-- The underlying family of 2-morphisms. -/
  app (a : B) : η.app a ⟶ θ.app a
  /-- The naturality condition. -/
  naturality {a b : B} (f : a ⟶ b) :
    F.map f ◁ app b ≫ (θ.naturality f).hom =
      (η.naturality f).hom ≫ app a ▷ G.map f := by aesop_cat

attribute [reassoc (attr := simp)] Modification.naturality

variable {η θ}

namespace Modification

variable (Γ : Modification η θ)

/-- The modification between the underlying strong transformations of oplax functors -/
@[simps]
def toOplax : OplaxTrans.Modification η.toOplax θ.toOplax where
  app a := Γ.app a

instance hasCoeToOplax :
    Coe (Modification η θ) (OplaxTrans.Modification η.toOplax θ.toOplax) :=
  ⟨toOplax⟩

/-- The modification between strong transformations of oplax functors associated to a modification
between the underlying oplax transformations. -/
@[simps]
def mkOfOplax (Γ : OplaxTrans.Modification η.toOplax θ.toOplax) : Modification η θ where
  app a := Γ.app a
  naturality f := by simpa using Γ.naturality f

section

variable (Γ : Modification η θ) {a b c : B} {a' : C}

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality (f : a' ⟶ F.obj b) (g : b ⟶ c) :
    f ◁ F.map g ◁ Γ.app c ≫ f ◁ (θ.naturality g).hom =
      f ◁ (η.naturality g).hom ≫ f ◁ Γ.app b ▷ G.map g :=
  OplaxTrans.Modification.whiskerLeft_naturality Γ.toOplax _ _

@[reassoc (attr := simp)]
theorem whiskerRight_naturality (f : a ⟶ b) (g : G.obj b ⟶ a') :
    F.map f ◁ Γ.app b ▷ g ≫ (α_ _ _ _).inv ≫ (θ.naturality f).hom ▷ g =
      (α_ _ _ _).inv ≫ (η.naturality f).hom ▷ g ≫ Γ.app a ▷ G.map f ▷ g :=
  OplaxTrans.Modification.whiskerRight_naturality Γ.toOplax _ _

end

end Modification

/-- Category structure on the oplax natural transformations between oplax functors. -/
@[simps]
instance homCategory : Category (F ⟶ G) where
  Hom := Modification
  id η := { app := fun a ↦ 𝟙 (η.app a) }
  comp Γ Δ := { app := fun a => Γ.app a ≫ Δ.app a }

instance : Inhabited (Modification η η) :=
  ⟨𝟙 η⟩

@[ext]
lemma homCategory.ext {m n : η ⟶ θ} (w : ∀ b, m.app b = n.app b) : m = n :=
  Modification.ext (funext w)

/-- Construct a modification isomorphism between strong natural transformations (of oplax functors)
by giving object level isomorphisms, and checking naturality only in the forward direction.
-/
@[simps]
def ModificationIso.ofComponents (app : ∀ a, η.app a ≅ θ.app a)
    (naturality :
      ∀ {a b} (f : a ⟶ b),
        F.map f ◁ (app b).hom ≫ (θ.naturality f).hom =
          (η.naturality f).hom ≫ (app a).hom ▷ G.map f) : η ≅ θ where
  hom := { app := fun a => (app a).hom }
  inv :=
    { app := fun a => (app a).inv
      naturality := fun {a b} f => by
        simpa using congr_arg (fun f => _ ◁ (app b).inv ≫ f ≫ (app a).inv ▷ _)
          (naturality f).symm }

def ModificationIso.mkOfOplax (Φ : η.toOplax ≅ θ.toOplax) : η ≅ θ where
  hom := Modification.mkOfOplax Φ.hom
  inv := Modification.mkOfOplax Φ.inv
  hom_inv_id := by simp [Modificatin.mkOfOplax, Φ.hom_inv_id]

end StrongTrans

end CategoryTheory.Oplax
