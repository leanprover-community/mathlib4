/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.Tactic.CategoryTheory.Reassoc

/-!
# Natural transformations

Defines natural transformations between functors.

A natural transformation `α : NatTrans F G` consists of morphisms `α.app X : F.obj X ⟶ G.obj X`,
and the naturality squares `α.naturality f : F.map f ≫ α.app Y = α.app X ≫ G.map f`,
where `f : X ⟶ Y`.

Note that we make `NatTrans.naturality` a simp lemma, with the preferred simp normal form
pushing components of natural transformations to the left.

See also `CategoryTheory.FunctorCat`, where we provide the category structure on
functors and natural transformations.

Introduces notations
* `τ.app X` for the components of natural transformations,
* `F ⟶ G` for the type of natural transformations between functors `F` and `G`
  (this and the next require `CategoryTheory.FunctorCat`),
* `σ ≫ τ` for vertical compositions, and
* `σ ◫ τ` for horizontal compositions.

-/

@[expose] public section

set_option mathlib.tactic.category.grind true

namespace CategoryTheory

-- declare the `v`'s first; see note [category theory universes].
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- `NatTrans F G` represents a natural transformation between functors `F` and `G`.

The field `app` provides the components of the natural transformation.

Naturality is expressed by `α.naturality`.
-/
@[ext, to_dual self (reorder := F G)]
structure NatTrans (F G : C ⥤ D) : Type max u₁ v₂ where
  /-- The component of a natural transformation. -/
  app (X : C) : F.obj X ⟶ G.obj X
  /-- The naturality square for a given morphism. -/
  naturality ⦃X Y : C⦄ (f : X ⟶ Y) : F.map f ≫ app Y = app X ≫ G.map f := by cat_disch

set_option linter.translateOverwrite false in
@[to_dual existing naturality]
lemma NatTrans.naturality' {F G : C ⥤ D} (self : NatTrans G F) ⦃X Y : C⦄ (f : Y ⟶ X) :
    self.app Y ≫ F.map f = G.map f ≫ self.app X := (self.naturality f).symm

set_option linter.translateOverwrite false in
/-- `NatTrans.mk'` is the dual of `NatTrans.mk`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing mk]
abbrev NatTrans.mk' {F G : C ⥤ D} (app : (X : C) → G.obj X ⟶ F.obj X)
    (naturality : ∀ ⦃X Y : C⦄ (f : Y ⟶ X), app Y ≫ F.map f = G.map f ≫ app X) : NatTrans G F where
  app

-- Rather arbitrarily, we say that the 'simpler' form is
-- components of natural transformations moving earlier.
attribute [reassoc (attr := simp)] NatTrans.naturality

attribute [grind _=_] NatTrans.naturality

@[to_dual self]
theorem congr_app {F G : C ⥤ D} {α β : NatTrans F G} (h : α = β) (X : C) : α.app X = β.app X := by
  cat_disch

namespace NatTrans

/-- `NatTrans.id F` is the identity natural transformation on a functor `F`. -/
protected def id (F : C ⥤ D) : NatTrans F F where app X := 𝟙 (F.obj X)

@[simp]
theorem id_app' (F : C ⥤ D) (X : C) : (NatTrans.id F).app X = 𝟙 (F.obj X) := rfl

instance (F : C ⥤ D) : Inhabited (NatTrans F F) := ⟨NatTrans.id F⟩

open Category

open CategoryTheory.Functor

section

variable {F G H : C ⥤ D}

/-- `vcomp α β` is the vertical compositions of natural transformations. -/
@[to_dual self (reorder := F H, α β)]
def vcomp (α : NatTrans F G) (β : NatTrans G H) : NatTrans F H where
  app X := α.app X ≫ β.app X

-- functor_category will rewrite (vcomp α β) to (α ≫ β), so this is not a
-- suitable simp lemma.  We will declare the variant vcomp_app' there.
@[to_dual self]
theorem vcomp_app (α : NatTrans F G) (β : NatTrans G H) (X : C) :
    (vcomp α β).app X = α.app X ≫ β.app X := rfl

attribute [grind =] vcomp_app

end

/-- The diagram
```
    F(f)      F(g)      F(h)
F X ----> F Y ----> F U ----> F V
 |         |         |         |
 | α(X)    | α(Y)    | α(U)    | α(V)
 v         v         v         v
G X ----> G Y ----> G U ----> G V
    G(f)      G(g)      G(h)
```
commutes.
-/
example {F G : C ⥤ D} (α : NatTrans F G) {X Y U V : C} (f : X ⟶ Y) (g : Y ⟶ U) (h : U ⟶ V) :
    α.app X ≫ G.map f ≫ G.map g ≫ G.map h = F.map f ≫ F.map g ≫ F.map h ≫ α.app V := by
  grind

end NatTrans

end CategoryTheory
