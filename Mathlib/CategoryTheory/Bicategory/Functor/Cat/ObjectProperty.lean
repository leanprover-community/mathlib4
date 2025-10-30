/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Bicategory.Functor.Cat
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# Properties of objects in target categories of a pseudofunctor to `Cat`

Given `F : Pseudofunctor B Cat`, we introduce a type `F.ObjectProperty`
which consists of properties `P` of objects for all categories `F.obj X` for `X : B`.
The typeclass `P.IsClosedUnderMapObj` expresses that this property
is preserved by the application of the functors `F.map`: this allows
to define a sub-pseudofunctor `P.fullsubcategory : Pseudofunctor B Cat`.

## TODO (@joelriou)
* Given a Grothendieck topology `J` on a category `C`, define
a type class `Pseudofunctor.ObjectProperty.IsLocal P J` extending
`IsClosedUnderMapObj` saying that if an object locally satisfied
the property, then it satisfies the property. Assuming this, show that
`P.fullsubcategory` if a stack if the original pseudofunctor was.

-/

universe w v v' u u'

namespace CategoryTheory

open Bicategory

namespace Pseudofunctor

variable {B : Type u} [Bicategory.{w, v} B] (F : Pseudofunctor B Cat.{v', u'})

/-- If `F : Pseudofunctor B Cat`, this is the data of a property of
objects in all categories `F.obj X` for `X : B`. -/
protected structure ObjectProperty where
  /-- A property of objects in the category `F.obj X` for all `X : B`. -/
  prop (X : B) : CategoryTheory.ObjectProperty (F.obj X)

namespace ObjectProperty

variable {F} (P : F.ObjectProperty)

/-- Given `F : Pseudofunctor B Cat`, `P : F.ObjectProperty` and `X : B`, this is
the fullsubcategory of `F.obj X` consisting of the objects satisfying the
property `P`. -/
abbrev Obj (X : B) := (P.prop X).FullSubcategory

/-- If `P` is a property of objects for a pseudofunctor `F` to `Cat`,
this is the condition that `P` is preserved by the application of the functors `F.obj`. -/
class IsClosedUnderMapObj (P : F.ObjectProperty) : Prop where
  map_obj (P) {X Y : B} {M : F.obj X} (hM : P.prop X M) (f : X ⟶ Y) : P.prop Y ((F.map f).obj M)
export IsClosedUnderMapObj (map_obj)

/-- If `P` is a property of objects for a pseudofunctor `F` to `Cat`, this is the
condition that all `P.prop : ObjectProprety (F.obj X)` for `X : B` are closed
under isomorphisms. -/
class IsClosedUnderIsomorphisms : Prop where
  isClosedUnderIsomorphisms (X : B) : (P.prop X).IsClosedUnderIsomorphisms

attribute [instance] IsClosedUnderIsomorphisms.isClosedUnderIsomorphisms

section

variable [P.IsClosedUnderMapObj]

/-- Given a property `P` of objects for `F : Pseudofunctor B Cat` and a morphism `f : X ⟶ Y`
in `B`, this is the functor `P.Obj X ⥤ P.Obj Y` that is induced by `F.map f`. -/
@[simps!]
def map {X Y : B} (f : X ⟶ Y) :
    P.Obj X ⥤ P.Obj Y :=
  (P.prop Y).lift (ObjectProperty.ι _ ⋙ F.map f) (fun M ↦ P.map_obj M.2 f)

/-- Given a property `P` of objects for `F : Pseudofunctor B Cat` and
a `2`-morphism in `B`, this is the induced natural transformation between
the induced functors on the fullsubcategories of objects satisfying `P`. -/
@[simps!]
def map₂ {X Y : B} {f g : X ⟶ Y} (α : f ⟶ g) :
    P.map f ⟶ P.map g :=
  ((P.prop Y).fullyFaithfulι.whiskeringRight _).preimage
    (Functor.whiskerLeft (P.prop X).ι (F.map₂ α))

/-- Auxiliary definition for `fullsubcategory`. -/
def mapId (X : B) :
    P.map (𝟙 X) ≅ 𝟭 _ :=
  ((P.prop X).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (P.prop X).ι (F.mapId X))

@[simp]
lemma mapId_hom_app {X : B} (M : P.Obj X) :
  (P.mapId X).hom.app M = (F.mapId X).hom.app M.obj := rfl

@[simp]
lemma mapId_inv_app {X : B} (M : P.Obj X) :
  (P.mapId X).inv.app M = (F.mapId X).inv.app M.obj := rfl

/-- Auxiliary definition for `fullsubcategory`. -/
def mapComp {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    P.map (f ≫ g) ≅ P.map f ⋙ P.map g :=
  ((P.prop Z).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (P.prop X).ι (F.mapComp f g))

-- better wait for #26446
/-- Given a property of objects `P` for a pseudofunctor from `B` to `Cat`, this is
the induced pseudofunctor which sends `X : B` to the full subcategory of `F.obj B`
consisting of objects satisfying `P`. -/
@[simps]
def fullsubcategory : Pseudofunctor B Cat where
  obj X := Cat.of (P.Obj X)
  map f := P.map f
  map₂ α := P.map₂ α
  mapId X := P.mapId X
  mapComp f g := P.mapComp f g
  map₂_id := sorry
  map₂_comp := sorry
  map₂_associator := sorry
  map₂_left_unitor := sorry
  map₂_right_unitor := sorry
  map₂_whisker_left := sorry
  map₂_whisker_right := sorry

attribute [local simp] Cat.leftUnitor_hom_app Cat.rightUnitor_inv_app
  Cat.associator_hom_app Cat.associator_inv_app

/-- The inclusion of `P.fullsubcategory` in `F`. -/
def ι : StrongTrans P.fullsubcategory F where
  app X := (P.prop (X := X)).ι
  naturality f := Iso.refl _

end

end ObjectProperty

end Pseudofunctor

end CategoryTheory
