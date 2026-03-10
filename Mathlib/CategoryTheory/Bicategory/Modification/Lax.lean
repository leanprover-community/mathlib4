/- 
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Lax

/-!
# Modifications between transformations of lax functors

This file defines modifications between lax and oplax transformations of lax functors.
-/

@[expose] public section

namespace CategoryTheory.Lax

open Category Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂
variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
  {F G : LaxFunctor B C}

namespace LaxTrans

open scoped Lax.LaxTrans

variable (η θ : F ⟶ G)

/-- A modification between lax natural transformations. -/
@[ext]
structure Modification where
  /-- The underlying family of 2-morphisms. -/
  app (a : B) : η.app a ⟶ θ.app a
  /-- The naturality condition. -/
  naturality :
    ∀ {a b : B} (f : a ⟶ b),
      app a ▷ G.map f ≫ θ.naturality f = η.naturality f ≫ F.map f ◁ app b := by
    cat_disch

attribute [reassoc (attr := simp)] Modification.naturality

variable {η θ}

namespace Modification

variable (η) in
/-- The identity modification. -/
@[simps]
def id : Modification η η where
  app a := 𝟙 (η.app a)

instance : Inhabited (Modification η η) :=
  ⟨Modification.id η⟩

/-- Vertical composition of modifications. -/
@[simps]
def vcomp {ι : F ⟶ G} (Γ : Modification η θ) (Δ : Modification θ ι) : Modification η ι where
  app a := Γ.app a ≫ Δ.app a

end Modification

variable (η θ) in
/-- Type alias for modifications between lax transformations of lax functors. -/
@[ext]
structure Hom where
  of ::
  /-- The underlying modification. -/
  as : Modification η θ

/-- Category structure on lax natural transformations between lax functors. -/
@[simps!]
scoped instance homCategory : Category (F ⟶ G) where
  Hom := Hom
  id η := ⟨Modification.id η⟩
  comp Γ Δ := ⟨Modification.vcomp Γ.as Δ.as⟩

instance : Inhabited (η ⟶ η) :=
  ⟨𝟙 η⟩

@[ext]
lemma homCategory.ext {Γ Δ : η ⟶ θ} (h : ∀ a, Γ.as.app a = Δ.as.app a) : Γ = Δ :=
  Hom.ext <| Modification.ext <| funext h

/-- Construct a modification isomorphism between lax natural transformations
by giving object level isomorphisms, and checking naturality only in the forward direction.
-/
@[simps]
def isoMk (app : ∀ a, η.app a ≅ θ.app a)
    (naturality :
      ∀ {a b} (f : a ⟶ b),
        (app a).hom ▷ G.map f ≫ θ.naturality f =
          η.naturality f ≫ F.map f ◁ (app b).hom := by cat_disch) :
    η ≅ θ where
  hom := ⟨{ app a := (app a).hom }⟩
  inv := ⟨{
      app a := (app a).inv
      naturality {a b} f := by
        simpa using (app a).inv ▷ G.map f ≫= (naturality f).symm =≫ F.map f ◁ (app b).inv }⟩

end LaxTrans

namespace OplaxTrans

open scoped Lax.OplaxTrans

variable (η θ : F ⟶ G)

/-- A modification between oplax natural transformations. -/
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

variable (η) in
/-- The identity modification. -/
@[simps]
def id : Modification η η where
  app a := 𝟙 (η.app a)

instance : Inhabited (Modification η η) :=
  ⟨Modification.id η⟩

/-- Vertical composition of modifications. -/
@[simps]
def vcomp {ι : F ⟶ G} (Γ : Modification η θ) (Δ : Modification θ ι) :
    Modification η ι where
  app a := Γ.app a ≫ Δ.app a

end Modification

variable (η θ) in
/-- Type alias for modifications between oplax transformations of lax functors. -/
@[ext]
structure Hom where
  of ::
  /-- The underlying modification. -/
  as : Modification η θ

/-- Category structure on oplax natural transformations between lax functors. -/
@[simps!]
scoped instance homCategory : Category (F ⟶ G) where
  Hom := Hom
  id η := ⟨Modification.id η⟩
  comp Γ Δ := ⟨Modification.vcomp Γ.as Δ.as⟩

instance : Inhabited (η ⟶ η) :=
  ⟨𝟙 η⟩

@[ext]
lemma homCategory.ext {Γ Δ : η ⟶ θ} (h : ∀ a, Γ.as.app a = Δ.as.app a) : Γ = Δ :=
  Hom.ext <| Modification.ext <| funext h

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
        simpa using F.map f ◁ (app b).inv ≫= (naturality f).symm =≫ (app a).inv ▷ G.map f }⟩

end OplaxTrans

end CategoryTheory.Lax
