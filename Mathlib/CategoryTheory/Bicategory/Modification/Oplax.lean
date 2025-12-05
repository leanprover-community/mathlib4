/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Oplax

/-!
# Modifications between transformations of oplax functors

In this file we define modifications of oplax and strong transformations of oplax functors.

A modification `Γ` between oplax transformations `η` and `θ` (of oplax functors) consists of a
family of 2-morphisms `Γ.app a : η.app a ⟶ θ.app a`, which for all 1-morphisms `f : a ⟶ b`
satisfies the equation `(F.map f ◁ app b) ≫ θ.naturality f = η.naturality f ≫ (app a ▷ G.map f)`.

Modifications between strong transformations are defined similarly.

## Main definitions

Given two oplax functors `F` and `G`, we define:

* `OplaxTrans.Modification η θ`: modifications between oplax transformations `η` and `θ` between
  `F` and `G`.
* `OplaxTrans.homCategory F G`: the category structure on the oplax transformations
  between `F` and `G`, where composition is given by vertical composition. Note that this a scoped
  instance in the `Oplax.OplaxTrans` namespace, so you need to run `open scoped Oplax.OplaxTrans`
  to access it.

* `StrongTrans.Modification η θ`: modifications between strong transformations `η` and `θ` between
  `F` and `G`.
* `StrongTrans.homCategory F G`: the category structure on the strong transformations
  between `F` and `G`, where composition is given by vertical composition. Note that this a scoped
  instance in the `Oplax.StrongTrans` namespace, so you need to run `open scoped Oplax.StrongTrans`
  to access it.

-/

@[expose] public section

namespace CategoryTheory.Oplax

open Category Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
  {F G : B ⥤ᵒᵖᴸ C}

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
  naturality :
    ∀ {a b : B} (f : a ⟶ b),
      F.map f ◁ app b ≫ θ.naturality f = η.naturality f ≫ app a ▷ G.map f := by
    cat_disch

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

variable (η) in
/-- The identity modification. -/
@[simps]
def id : Modification η η where app a := 𝟙 (η.app a)

instance : Inhabited (Modification η η) :=
  ⟨Modification.id η⟩

/-- Vertical composition of modifications. -/
@[simps]
def vcomp {ι : F ⟶ G} (Γ : Modification η θ) (Δ : Modification θ ι) : Modification η ι where
  app a := Γ.app a ≫ Δ.app a

end Modification

variable (η θ) in
/-- Type-alias for modifications between oplax transformations of oplax functors. This is the type
used for the 2-homomorphisms in the bicategory of oplax functors equipped with oplax
transformations. -/
@[ext]
structure Hom where
  of ::
  /-- The underlying modification of oplax transformations. -/
  as : Modification η θ

/-- Category structure on the oplax natural transformations between OplaxFunctors.

Note that this a scoped instance in the `Oplax.OplaxTrans` namespace. -/
@[simps!]
scoped instance homCategory : Category (F ⟶ G) where
  Hom := Hom
  id Γ := ⟨Modification.id Γ⟩
  comp Γ Δ := ⟨Modification.vcomp Γ.as Δ.as⟩

instance : Inhabited (η ⟶ η) :=
  ⟨𝟙 η⟩

@[ext]
lemma homCategory.ext {m n : η ⟶ θ} (w : ∀ b, m.as.app b = n.as.app b) : m = n :=
  Hom.ext <| Modification.ext <| funext w

/-- Construct a modification isomorphism between oplax natural transformations
by giving object level isomorphisms, and checking naturality only in the forward direction.
-/
@[simps]
def isoMk (app : ∀ a, η.app a ≅ θ.app a)
    (naturality :
      ∀ {a b} (f : a ⟶ b),
        F.map f ◁ (app b).hom ≫ θ.naturality f =
          η.naturality f ≫ (app a).hom ▷ G.map f := by cat_disch) :
    η ≅ θ where
  hom := ⟨{ app a := (app a).hom }⟩
  inv := ⟨{
      app a := (app a).inv
      naturality {a b} f := by
        simpa using _ ◁ (app b).inv ≫= (naturality f).symm =≫ (app a).inv ▷ _ }⟩

@[deprecated (since := "2025-11-11")] alias ModificationIso.ofComponents := isoMk

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
      (η.naturality f).hom ≫ app a ▷ G.map f := by cat_disch

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

/-- Modifications between strong transformations of oplax functors are equivalent to modifications
between the underlying oplax transformations. -/
@[simps]
def equivOplax : (OplaxTrans.Modification η.toOplax θ.toOplax) ≃ Modification η θ where
  toFun := mkOfOplax
  invFun := toOplax
  left_inv _ := rfl
  right_inv _ := rfl

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

variable (η) in
/-- The identity modification. -/
@[simps]
def id : Modification η η where app a := 𝟙 (η.app a)

instance : Inhabited (Modification η η) :=
  ⟨Modification.id η⟩

/-- Vertical composition of modifications. -/
@[simps]
def vcomp {ι : F ⟶ G} (Γ : Modification η θ) (Δ : Modification θ ι) : Modification η ι where
  app a := Γ.app a ≫ Δ.app a

end Modification

variable (η θ) in
/-- Type-alias for modifications between strong transformations of oplax functors. This is the type
used for the 2-homomorphisms in the bicategory of oplax functors equipped with strong
transformations. -/
@[ext]
structure Hom where
  of ::
  /-- The underlying modification of strong transformations. -/
  as : Modification η θ

/-- Category structure on the strong natural transformations between oplax functors.

Note that this a scoped instance in the `Oplax.StrongTrans` namespace. -/
@[simps!]
scoped instance homCategory : Category (F ⟶ G) where
  Hom := Hom
  id Γ := ⟨Modification.id Γ⟩
  comp Γ Δ := ⟨Modification.vcomp Γ.as Δ.as⟩

instance : Inhabited (η ⟶ η) :=
  ⟨𝟙 η⟩

@[ext]
lemma homCategory.ext {m n : η ⟶ θ} (w : ∀ b, m.as.app b = n.as.app b) : m = n :=
  Hom.ext <| Modification.ext <| funext w

/-- Construct a modification isomorphism between strong natural transformations (of oplax functors)
by giving object level isomorphisms, and checking naturality only in the forward direction.
-/
@[simps]
def isoMk (app : ∀ a, η.app a ≅ θ.app a)
    (naturality : ∀ {a b} (f : a ⟶ b),
      F.map f ◁ (app b).hom ≫ (θ.naturality f).hom =
        (η.naturality f).hom ≫ (app a).hom ▷ G.map f := by cat_disch) :
    η ≅ θ where
  hom := ⟨{ app a := (app a).hom }⟩
  inv := ⟨{
      app a := (app a).inv
      naturality {a b} f := by
        simpa using _ ◁ (app b).inv ≫= (naturality f).symm =≫ (app a).inv ▷ _ }⟩

end StrongTrans

end CategoryTheory.Oplax
