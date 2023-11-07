/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.GradedObject.Bifunctor
/-!
# The action of trifunctors on graded objects

Given a trifunctor `F. C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄` and types `I₁`, `I₂` and `I₃`, we define a functor
`GradedObject I₁ C₁ ⥤ GradedObject I₂ C₂ ⥤ GradedObject I₃ C₃ ⥤ GradedObject (I₁ × I₂ × I₃) C₄`
(see `mapTrifunctor`). When we have a map `p : I₁ × I₂ × I₃ → J` and suitable coproducts
exists, we define a functor
`GradedObject I₁ C₁ ⥤ GradedObject I₂ C₂ ⥤ GradedObject I₃ C₃ ⥤ GradedObject J C₄`
(see `mapTrifunctorMap`) which sends graded objects `X₁`, `X₂`, `X₃` to the graded object
which sets `j` to the coproduct of the objects `((F.obj (X₁ i₁)).obj (X₂ i₂)).obj (X₃ i₃)`
for `p ⟨i₁, i₂, i₃⟩ = j`.

This shall be used in order to constructor the associator isomorphism for the monoidal
category structure on `GradedObject I C` induced by a monoidal structure on `C` and
an additive monoid structure on `I` (TODO @joelriou).

-/

namespace CategoryTheory

open Category Limits

variable {C₁ C₂ C₃ C₄ : Type*}
  [Category C₁] [Category C₂] [Category C₃] [Category C₄]
  (F F' : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄)

namespace GradedObject

/-- Auxiliary definition for `mapTrifunctor`. -/
@[simps]
def mapTrifunctorObj {I₁ : Type*} (X₁ : GradedObject I₁ C₁) (I₂ I₃ : Type*) :
    GradedObject I₂ C₂ ⥤ GradedObject I₃ C₃ ⥤ GradedObject (I₁ × I₂ × I₃) C₄ where
  obj X₂ :=
    { obj := fun X₃ x => ((F.obj (X₁ x.1)).obj (X₂ x.2.1)).obj (X₃ x.2.2)
      map := fun {X₃ Y₃} φ x => ((F.obj (X₁ x.1)).obj (X₂ x.2.1)).map (φ x.2.2) }
  map {X₂ Y₂} φ :=
    { app := fun X₃ x => ((F.obj (X₁ x.1)).map (φ x.2.1)).app (X₃ x.2.2) }

/-- Given a trifunctor `F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄` and types `I₁`, `I₂`, `I₃`,
this is the obvious functor
`GradedObject I₁ C₁ ⥤ GradedObject I₂ C₂ ⥤ GradedObject I₃ C₃ ⥤ GradedObject (I₁ × I₂ × I₃) C₄`.
-/
@[simps]
def mapTrifunctor (I₁ I₂ I₃ : Type*) :
    GradedObject I₁ C₁ ⥤ GradedObject I₂ C₂ ⥤ GradedObject I₃ C₃ ⥤
      GradedObject (I₁ × I₂ × I₃) C₄ where
  obj X₁ := mapTrifunctorObj F X₁ I₂ I₃
  map {X₁ Y₁} φ :=
    { app := fun X₂ =>
        { app := fun X₃ x => ((F.map (φ x.1)).app (X₂ x.2.1)).app (X₃ x.2.2) }
      naturality := fun {X₂ Y₂} ψ => by
        ext X₃ x
        dsimp
        simp only [← NatTrans.comp_app]
        congr 1
        rw [NatTrans.naturality] }

section

variable {F F'}

/-- The natural transformation `mapTrifunctor F I₁ I₂ I₃ ⟶ mapTrifunctor F' I₁ I₂ I₃`
induced by a natural transformation `F ⟶ F` of trifunctors. -/
@[simps]
def mapTrifunctorMapNatTrans (α : F ⟶ F') (I₁ I₂ I₃ : Type*) :
    mapTrifunctor F I₁ I₂ I₃ ⟶ mapTrifunctor F' I₁ I₂ I₃ where
  app X₁ :=
    { app := fun X₂ =>
        { app := fun X₃ i => ((α.app _).app _).app _ }
      naturality := fun {X₂ Y₂} φ => by
        ext X₃ ⟨i₁, i₂, i₃⟩
        dsimp
        simp only [← NatTrans.comp_app, NatTrans.naturality] }
  naturality := fun {X₁ Y₁} φ => by
    ext X₂ X₃ ⟨i₁, i₂, i₃⟩
    dsimp
    simp only [← NatTrans.comp_app, NatTrans.naturality]

/-- The natural isomorphism `mapTrifunctor F I₁ I₂ I₃ ≅ mapTrifunctor F' I₁ I₂ I₃`
induced by a natural isomorphism `F ≅ F` of trifunctors. -/
@[simps]
def mapTrifunctorMapIso (e : F ≅ F') (I₁ I₂ I₃ : Type*) :
    mapTrifunctor F I₁ I₂ I₃ ≅ mapTrifunctor F' I₁ I₂ I₃ where
  hom := mapTrifunctorMapNatTrans e.hom I₁ I₂ I₃
  inv := mapTrifunctorMapNatTrans e.inv I₁ I₂ I₃
  hom_inv_id := by
    ext X₁ X₂ X₃ ⟨i₁, i₂, i₃⟩
    dsimp
    simp only [← NatTrans.comp_app, e.hom_inv_id, NatTrans.id_app]
  inv_hom_id := by
    ext X₁ X₂ X₃ ⟨i₁, i₂, i₃⟩
    dsimp
    simp only [← NatTrans.comp_app, e.inv_hom_id, NatTrans.id_app]

end

section

variable {I₁ I₂ I₃ J : Type*} (p : I₁ × I₂ × I₃ → J)

/-- Given a trifunctor `F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₃`, graded objects `X₁ : GradedObject I₁ C₁`,
`X₂ : GradedObject I₂ C₂`, `X₃ : GradedObject I₃ C₃`, and a map `p : I₁ × I₂ × I₃ → J`,
this is the `J`-graded object sending `j` to the coproduct of
`((F.obj (X₁ i₁)).obj (X₂ i₂)).obj (X₃ i₃)` for `p ⟨i₁, i₂, i₃⟩ = k`. -/
@[simp]
noncomputable def mapTrifunctorMapObj (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂)
    (X₃ : GradedObject I₃ C₃)
    [HasMap ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) p] :
    GradedObject J C₄ :=
  ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃).mapObj p

/-- The obvious inclusion
`((F.obj (X₁ i₁)).obj (X₂ i₂)).obj (X₃ i₃) ⟶ mapTrifunctorMapObj F p X₁ X₂ X₃ j` when
`p ⟨i₁, i₂, i₃⟩ = j`. -/
noncomputable def ιMapTrifunctorMapObj (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂)
    (X₃ : GradedObject I₃ C₃) (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J) (h : p ⟨i₁, i₂, i₃⟩ = j)
    [HasMap ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) p] :
    ((F.obj (X₁ i₁)).obj (X₂ i₂)).obj (X₃ i₃) ⟶ mapTrifunctorMapObj F p X₁ X₂ X₃ j :=
  ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃).ιMapObj p ⟨i₁, i₂, i₃⟩ j h


/-- The maps `mapTrifunctorMapObj F p X₁ X₂ X₃ ⟶ mapTrifunctorMapObj F p Y₁ Y₂ Y₃` which
express the functoriality of `mapTrifunctorMapObj`, see `mapTrifunctorMap` -/
@[simp]
noncomputable def mapTrifunctorMapMap {X₁ Y₁ : GradedObject I₁ C₁} (f₁ : X₁ ⟶ Y₁)
    {X₂ Y₂ : GradedObject I₂ C₂} (f₂ : X₂ ⟶ Y₂)
    {X₃ Y₃ : GradedObject I₃ C₃} (f₃ : X₃ ⟶ Y₃)
    [HasMap ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) p]
    [HasMap ((((mapTrifunctor F I₁ I₂ I₃).obj Y₁).obj Y₂).obj Y₃) p] :
    mapTrifunctorMapObj F p X₁ X₂ X₃ ⟶ mapTrifunctorMapObj F p Y₁ Y₂ Y₃ :=
  GradedObject.mapMap ((((mapTrifunctor F I₁ I₂ I₃).map f₁).app X₂).app X₃ ≫
    (((mapTrifunctor F I₁ I₂ I₃).obj Y₁).map f₂).app X₃ ≫
    (((mapTrifunctor F I₁ I₂ I₃).obj Y₁).obj Y₂).map f₃) p

lemma ι_mapTrifunctorMapMap {X₁ Y₁ : GradedObject I₁ C₁} (f₁ : X₁ ⟶ Y₁)
    {X₂ Y₂ : GradedObject I₂ C₂} (f₂ : X₂ ⟶ Y₂)
    {X₃ Y₃ : GradedObject I₃ C₃} (f₃ : X₃ ⟶ Y₃)
    [HasMap ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) p]
    [HasMap ((((mapTrifunctor F I₁ I₂ I₃).obj Y₁).obj Y₂).obj Y₃) p]
    (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J) (h : p ⟨i₁, i₂, i₃⟩ = j) :
  ιMapTrifunctorMapObj F p X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ mapTrifunctorMapMap F p f₁ f₂ f₃ j =
    ((F.map (f₁ i₁)).app (X₂ i₂)).app (X₃ i₃) ≫
      ((F.obj (Y₁ i₁)).map (f₂ i₂)).app (X₃ i₃) ≫
      ((F.obj (Y₁ i₁)).obj (Y₂ i₂)).map (f₃ i₃) ≫
      ιMapTrifunctorMapObj F p Y₁ Y₂ Y₃ i₁ i₂ i₃ j h := by
  dsimp only [ιMapTrifunctorMapObj, mapTrifunctorMapMap]
  rw [ι_mapMap]
  dsimp
  rw [assoc, assoc]

instance (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂) (X₃ : GradedObject I₃ C₃)
  [h : HasMap ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) p] :
      HasMap (((mapTrifunctorObj F X₁ I₂ I₃).obj X₂).obj X₃) p := h

set_option maxHeartbeats 400000 in
/-- Given a trifunctor `F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄`, a map `p : I₁ × I₂ × I₃ → J`, and
graded objects `X₁ : GradedObject I₁ C₁`, `X₂ : GradedObject I₂ C₂` and `X₃ : GradedObject I₃ C₃`,
this is the `J`-graded object sending `j` to the coproduct of
`((F.obj (X₁ i₁)).obj (X₂ i₂)).obj (X₃ i₃)` for `p ⟨i₁, i₂, i₃⟩ = j`. -/
@[simps]
noncomputable def mapTrifunctorMapFunctorObj (X₁ : GradedObject I₁ C₁)
    [∀ X₂ X₃, HasMap ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) p] :
    GradedObject I₂ C₂ ⥤ GradedObject I₃ C₃ ⥤ GradedObject J C₄ where
  obj X₂ :=
    { obj := fun X₃ => mapTrifunctorMapObj F p X₁ X₂ X₃
      map := fun {X₃ Y₃} φ => mapTrifunctorMapMap F p (𝟙 X₁) (𝟙 X₂) φ }
  map {X₂ Y₂} φ :=
    { app := fun X₃ => mapTrifunctorMapMap F p (𝟙 X₁) φ (𝟙 X₃)
      naturality := fun {X₃ Y₃} φ => by
        dsimp
        simp only [Functor.map_id, mapTrifunctor_obj, NatTrans.id_app,
          Category.id_comp, Category.comp_id, ← mapMap_comp]
        apply congr_mapMap
        simp }

set_option maxHeartbeats 400000 in
/-- Given a trifunctor `F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄` and a map `p : I₁ × I₂ × I₃ → J`,
this is the functor
`GradedObject I₁ C₁ ⥤ GradedObject I₂ C₂ ⥤ GradedObject I₃ C₃ ⥤ GradedObject J C₄`
sending `X₁ : GradedObject I₁ C₁`, `X₂ : GradedObject I₂ C₂` and `X₃ : GradedObject I₃ C₃`
to the `J`-graded object sending `j` to the coproduct of
`((F.obj (X₁ i₁)).obj (X₂ i₂)).obj (X₃ i₃)` for `p ⟨i₁, i₂, i₃⟩ = j`. -/
@[simps]
noncomputable def mapTrifunctorMap
    [∀ X₁ X₂ X₃, HasMap ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) p] :
    GradedObject I₁ C₁ ⥤ GradedObject I₂ C₂ ⥤ GradedObject I₃ C₃ ⥤ GradedObject J C₄ where
  obj X₁ := mapTrifunctorMapFunctorObj F p X₁
  map := fun {X₁ Y₁} φ =>
    { app := fun X₂ =>
        { app := fun X₃ => mapTrifunctorMapMap F p φ (𝟙 X₂) (𝟙 X₃)
          naturality := fun {X₃ Y₃} φ => by
            dsimp [mapTrifunctorMapFunctorObj]
            simp only [Functor.map_id, mapTrifunctor_obj, NatTrans.id_app,
              Category.id_comp, Category.comp_id, ← mapMap_comp]
            apply congr_mapMap
            simp }
      naturality := fun {X₂ Y₂} φ => by
        ext X₃ : 2
        dsimp [mapTrifunctorMapFunctorObj]
        simp only [Functor.map_id, mapTrifunctor_obj, NatTrans.id_app,
          Category.comp_id, Category.id_comp, ← mapMap_comp]
        apply congr_mapMap
        simp only [← NatTrans.comp_app]
        congr 1
        simp }

end

end GradedObject

end CategoryTheory
