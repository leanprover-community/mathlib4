/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Lax

/-!
# Modifications between transformations of lax functors

In this file we define modifications of lax and oplax transformations of lax functors.

A modification `Γ` between lax transformations `η` and `θ` (of lax functors) consists of a family
of 2-morphisms `Γ.app a : η.app a ⟶ θ.app a`, which for all 1-morphisms `f : a ⟶ b`
satisfies the equation `app a ▷ G.map f ≫ θ.naturality f = η.naturality f ≫ F.map f ◁ app b`.

Modifications between oplax transformations are defined similarly.

## Main definitions

Given two lax functors `F` and `G`, we define:

* `LaxTrans.Modification η θ`: modifications between lax transformations `η` and `θ` between
  `F` and `G`.
* `LaxTrans.homCategory F G`: the category structure on the lax transformations
  between `F` and `G`, where composition is given by vertical composition. Note that this is a
  scoped instance in the `Lax.LaxTrans` namespace, so you need to run
  `open scoped Lax.LaxTrans` to access it.

* `OplaxTrans.Modification η θ`: modifications between oplax transformations `η` and `θ`
  between `F` and `G`.
* `OplaxTrans.homCategory F G`: the category structure on the oplax transformations
  between `F` and `G`, where composition is given by vertical composition. Note that this is a
  scoped instance in the `Lax.OplaxTrans` namespace, so you need to run
  `open scoped Lax.OplaxTrans` to access it.
-/

@[expose] public section

namespace CategoryTheory.Lax

open Category Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂
variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
  {F G : B ⥤ᴸ C}

namespace LaxTrans

open scoped Lax.LaxTrans

variable (η θ : F ⟶ G)

/-- A modification between lax natural transformations of lax functors. -/
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
/-- Type-alias for modifications between lax transformations of lax functors. This is the type
used for the 2-homomorphisms in the bicategory of lax functors equipped with lax
transformations. -/
@[ext]
structure Hom where
  of ::
  /-- The underlying modification of lax transformations. -/
  as : Modification η θ

/-- Category structure on the lax natural transformations between lax functors.

Note that this is a scoped instance in the `Lax.LaxTrans` namespace. -/
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
  hom.as.app a := (app a).hom
  inv.as.app a := (app a).inv
  inv.as.naturality {a b} f := by
    simpa using (app a).inv ▷ G.map f ≫= (naturality f).symm =≫ F.map f ◁ (app b).inv

end LaxTrans

namespace OplaxTrans

open scoped Lax.OplaxTrans

variable (η θ : F ⟶ G)

/-- A modification between oplax natural transformations of lexfunctors. -/
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
/-- Type-alias for modifications between oplax transformations of lax functors. This is the type
used for the 2-homomorphisms in the bicategory of lax functors equipped with oplax
transformations. -/
@[ext]
structure Hom where
  of ::
  /-- The underlying modification of oplax transformations. -/
  as : Modification η θ

/-- Category structure on the oplax natural transformations between lax functors.

Note that this is a scoped instance in the `Lax.OplaxTrans` namespace. -/
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
  hom.as.app a := (app a).hom
  inv.as.app a := (app a).inv
  inv.as.naturality {a b} f := by
    simpa using F.map f ◁ (app b).inv ≫= (naturality f).symm =≫ (app a).inv ▷ G.map f

end OplaxTrans

end CategoryTheory.Lax
