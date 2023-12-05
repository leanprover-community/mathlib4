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

This shall be used in order to construct the associator isomorphism for the monoidal
category structure on `GradedObject I C` induced by a monoidal structure on `C` and
an additive monoid structure on `I` (TODO @joelriou).

-/

namespace CategoryTheory

open Category Limits

variable {C₁ C₂ C₃ C₄ C₁₂ C₂₃ : Type*}
  [Category C₁] [Category C₂] [Category C₃] [Category C₄]
  [Category C₁₂] [Category C₂₃]
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
noncomputable def mapTrifunctorMapMap {X₁ Y₁ : GradedObject I₁ C₁} (f₁ : X₁ ⟶ Y₁)
    {X₂ Y₂ : GradedObject I₂ C₂} (f₂ : X₂ ⟶ Y₂)
    {X₃ Y₃ : GradedObject I₃ C₃} (f₃ : X₃ ⟶ Y₃)
    [HasMap ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) p]
    [HasMap ((((mapTrifunctor F I₁ I₂ I₃).obj Y₁).obj Y₂).obj Y₃) p] :
    mapTrifunctorMapObj F p X₁ X₂ X₃ ⟶ mapTrifunctorMapObj F p Y₁ Y₂ Y₃ :=
  GradedObject.mapMap ((((mapTrifunctor F I₁ I₂ I₃).map f₁).app X₂).app X₃ ≫
    (((mapTrifunctor F I₁ I₂ I₃).obj Y₁).map f₂).app X₃ ≫
    (((mapTrifunctor F I₁ I₂ I₃).obj Y₁).obj Y₂).map f₃) p

@[reassoc (attr := simp)]
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

@[ext]
lemma mapTrifunctorMapObj_ext {X₁ : GradedObject I₁ C₁} {X₂ : GradedObject I₂ C₂}
    {X₃ : GradedObject I₃ C₃} {Y : C₄} (j : J)
    [HasMap ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) p]
    {φ φ' : mapTrifunctorMapObj F p X₁ X₂ X₃ j ⟶ Y}
    (h : ∀ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (h : p ⟨i₁, i₂, i₃⟩ = j),
      ιMapTrifunctorMapObj F p X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ φ =
        ιMapTrifunctorMapObj F p X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ φ') : φ = φ' := by
  apply mapObj_ext
  rintro ⟨i₁, i₂, i₃⟩ hi
  apply h

instance (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂) (X₃ : GradedObject I₃ C₃)
  [h : HasMap ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) p] :
      HasMap (((mapTrifunctorObj F X₁ I₂ I₃).obj X₂).obj X₃) p := h

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
      map := fun {X₃ Y₃} φ => mapTrifunctorMapMap F p (𝟙 X₁) (𝟙 X₂) φ
      map_id := fun X₃ => by
        ext j i₁ i₂ i₃ h
        dsimp
        simp only [ι_mapTrifunctorMapMap, categoryOfGradedObjects_id, Functor.map_id,
          NatTrans.id_app, id_comp, comp_id]
      map_comp := fun {X₃ Y₃ Z₃} φ ψ => by
        ext j i₁ i₂ i₃ h
        dsimp
        simp only [ι_mapTrifunctorMapMap, categoryOfGradedObjects_id, Functor.map_id,
          NatTrans.id_app, categoryOfGradedObjects_comp, Functor.map_comp, assoc, id_comp,
          ι_mapTrifunctorMapMap_assoc] }
  map {X₂ Y₂} φ :=
    { app := fun X₃ => mapTrifunctorMapMap F p (𝟙 X₁) φ (𝟙 X₃)
      naturality := fun {X₃ Y₃} ψ => by
        ext j i₁ i₂ i₃ h
        dsimp
        simp only [ι_mapTrifunctorMapMap_assoc, categoryOfGradedObjects_id, Functor.map_id,
          NatTrans.id_app, ι_mapTrifunctorMapMap, id_comp, NatTrans.naturality_assoc] }
  map_id X₂ := by
    ext X₃ j i₁ i₂ i₃ h
    dsimp
    simp only [ι_mapTrifunctorMapMap, categoryOfGradedObjects_id, Functor.map_id,
      NatTrans.id_app, id_comp, comp_id]
  map_comp {X₂ Y₂ Z₂} φ ψ := by
    ext X₃ j i₁ i₂ i₃
    dsimp
    simp only [ι_mapTrifunctorMapMap, categoryOfGradedObjects_id, Functor.map_id,
      NatTrans.id_app, categoryOfGradedObjects_comp, Functor.map_comp, NatTrans.comp_app,
      id_comp, assoc, ι_mapTrifunctorMapMap_assoc]

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
            dsimp
            ext j i₁ i₂ i₃ h
            dsimp
            simp only [ι_mapTrifunctorMapMap_assoc, categoryOfGradedObjects_id, Functor.map_id,
              NatTrans.id_app, ι_mapTrifunctorMapMap, id_comp, NatTrans.naturality_assoc] }
      naturality := fun {X₂ Y₂} ψ => by
        ext X₃ j
        dsimp
        ext i₁ i₂ i₃ h
        simp only [ι_mapTrifunctorMapMap_assoc, categoryOfGradedObjects_id, Functor.map_id,
          NatTrans.id_app, ι_mapTrifunctorMapMap, id_comp,
          NatTrans.naturality_app_assoc] }

end

section

variable (F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂) (G : C₁₂ ⥤ C₃ ⥤ C₄)

@[simps]
def _root_.CategoryTheory.bifunctorComp₁₂Obj (X₁ : C₁) : C₂ ⥤ C₃ ⥤ C₄ where
  obj X₂ :=
    { obj := fun X₃ => (G.obj ((F₁₂.obj X₁).obj X₂)).obj X₃
      map := fun {X₃ Y₃} φ => (G.obj ((F₁₂.obj X₁).obj X₂)).map φ }
  map {X₂ Y₂} φ :=
    { app := fun X₃ => (G.map ((F₁₂.obj X₁).map φ)).app X₃ }

@[simps]
def _root_.CategoryTheory.bifunctorComp₁₂ : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ where
  obj X₁ := _root_.CategoryTheory.bifunctorComp₁₂Obj F₁₂ G X₁
  map {X₁ Y₁} φ :=
    { app := fun X₂ =>
        { app := fun X₃ => (G.map ((F₁₂.map φ).app X₂)).app X₃ }
      naturality := fun {X₂ Y₂} ψ => by
        ext X₃
        dsimp
        simp only [← NatTrans.comp_app, ← G.map_comp, NatTrans.naturality] }

variable
  {I₁ I₂ I₁₂ I₃ J : Type*} (p : I₁ × I₂ → I₁₂) (q : I₁₂ × I₃ → J)
    (r : I₁ × I₂ × I₃ → J) (hr : ∀ (i : I₁ × I₂ × I₃), r i = q ⟨p ⟨i.1, i.2.1⟩, i.2.2⟩)

variable (I₃)

def p' : I₁ × I₂ × I₃ → I₁₂ × I₃ := fun ⟨i₁, i₂, i₃⟩ => ⟨p ⟨i₁, i₂⟩, i₃⟩

variable (I₁ I₂)

@[simps]
def π₁₂_₃ : I₁ × I₂ × I₃ → I₁ × I₂ := fun ⟨i₁, i₂, _⟩ => ⟨i₁, i₂⟩

variable {I₁ I₂ I₃} (I₁₂)

def γ (X₃ : GradedObject I₃ C₃) : GradedObject (I₁₂ × I₃) (C₁₂ ⥤ C₄) :=
  fun ⟨_, k⟩ => G.flip.obj (X₃ k)

variable {I₁₂}

/-section

class HasGoodBifunctor₁₂BifunctorObj (hr : ∀ (i : I₁ × I₂ × I₃), r i = q ⟨p ⟨i.1, i.2.1⟩, i.2.2⟩)
  (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂) (X₃ : GradedObject I₃ C₃)
    [HasMap (((mapBifunctor F₁₂ I₁ I₂).obj X₁).obj X₂) p]
    [HasMap (((mapBifunctor G I₁₂ I₃).obj (mapBifunctorMapObj F₁₂ p X₁ X₂)).obj X₃) q] :=
  hasMap₂ : HasMap ((((mapTrifunctor (bifunctorComp₁₂ F₁₂ G) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) r
  hasMap₃ : HasMap ((((mapTrifunctor (bifunctorComp₁₂ F₁₂ G) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) (p' I₃ p)
  hasMap₄ : HasMap (((((mapTrifunctor (bifunctorComp₁₂ F₁₂ G) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃).mapObj (p' I₃ p)) q
  hasMap₅ : HasMap ((comap _ (π₁₂_₃ I₁ I₂ I₃)).obj (((mapBifunctor F₁₂ I₁ I₂).obj X₁).obj X₂)) (p' I₃ p)
  preservesMap : PreservesMap (γ G I₁₂ X₃) (p' I₃ p) ((comap _ (π₁₂_₃ I₁ I₂ I₃)).obj (((mapBifunctorFunctor F₁₂ I₁ I₂).obj X₁).obj X₂))

variable (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂) (X₃ : GradedObject I₃ C₃)
  [HasMap (((mapBifunctorFunctor F₁₂ I₁ I₂).obj X₁).obj X₂) p]
  [HasMap (((mapBifunctorFunctor G I₁₂ I₃).obj (mapBifunctorMapObj F₁₂ p X₁ X₂)).obj X₃) q]

variable [H : HasGoodBifunctor₁₂BifunctorObj F₁₂ G p q r hr X₁ X₂ X₃]

attribute [local ext] mapObj_ext

noncomputable def mapBifunctor₁₂BifunctorMapObjIso₁ :
    have := H.hasMap₂
    have := H.hasMap₃
    have := H.hasMap₄
    (((((mapTrifunctorFunctor (bifunctorComp₁₂ F₁₂ G) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃).mapObj (p' I₃ p)).mapObj q ≅
      mapTrifunctorMapObj (bifunctorComp₁₂ F₁₂ G) r X₁ X₂ X₃ :=
  have := H.hasMap₂
  have := H.hasMap₃
  have := H.hasMap₄
  ((((mapTrifunctorFunctor (bifunctorComp₁₂ F₁₂ G) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃).mapObjMapObjIso (p' I₃ p) q r hr

noncomputable def mapBifunctor₁₂BifunctorMapObjIso₂ :
    have := H.hasMap₃
    have := H.hasMap₅
    ((((mapTrifunctorFunctor
      (bifunctorComp₁₂ F₁₂ G) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃).mapObj (p' I₃ p) ≅
    (applyFunctorsObj (γ G I₁₂ X₃)).obj
      (((comap _ (π₁₂_₃ I₁ I₂ I₃)).obj (((mapBifunctorFunctor F₁₂ I₁ I₂).obj X₁).obj X₂)).mapObj (p' I₃ p)) :=
  have := H.hasMap₃
  have := H.hasMap₅
  letI := H.preservesMap
  (comapObjApplyFunctorsObjObjMapObjIso (γ G I₁₂ X₃) (p' I₃ p) ((comap _ (π₁₂_₃ I₁ I₂ I₃)).obj (((mapBifunctorFunctor F₁₂ I₁ I₂).obj X₁).obj X₂)))

noncomputable def mapBifunctor₁₂BifunctorMapObjIso₃ :
    have := H.hasMap₅
    ((mapBifunctorFunctor G I₁₂ I₃).obj (mapBifunctorMapObj F₁₂ p X₁ X₂)).obj X₃ ≅
    (applyFunctorsObj (γ G I₁₂ X₃)).obj
      (((comap _ (π₁₂_₃ I₁ I₂ I₃)).obj (((mapBifunctorFunctor F₁₂ I₁ I₂).obj X₁).obj X₂)).mapObj (p' I₃ p)) :=
  have := H.hasMap₅
  isoMk  _ _ (fun ⟨i₁₂, j⟩ => by
    refine' (G.mapIso _).app (X₃ j)
    exact
      { hom := descMapObj _ _ (fun ⟨i₁, i₂⟩ _ =>
          ((comap C₁₂ (π₁₂_₃ I₁ I₂ I₃)).obj
            (((mapBifunctorFunctor F₁₂ I₁ I₂).obj X₁).obj X₂)).ιMapObj (p' I₃ p) ⟨i₁, i₂, j⟩ ⟨i₁₂, j⟩ (by aesop))
        inv := descMapObj _ _ (fun ⟨i₁, i₂, i₃⟩ h =>
          (((mapBifunctorFunctor F₁₂ I₁ I₂).obj X₁).obj X₂).ιMapObj p ⟨i₁, i₂⟩ i₁₂ (congr_arg _root_.Prod.fst h))
        inv_hom_id := by
          ext ⟨i₁, i₂, i₃⟩ h
          obtain rfl : i₃ = j := congr_arg _root_.Prod.snd h
          simp })

noncomputable def mapBifunctor₁₂BifunctorMapObjIso :
    have := H.hasMap₂
    mapTrifunctorMapObj (bifunctorComp₁₂ F₁₂ G) r X₁ X₂ X₃ ≅
    mapBifunctorMapObj G q (mapBifunctorMapObj F₁₂ p X₁ X₂) X₃ :=
  have := H.hasMap₄
  (mapBifunctor₁₂BifunctorMapObjIso₁ F₁₂ G p q r hr X₁ X₂ X₃).symm ≪≫
    mapIso ((mapBifunctor₁₂BifunctorMapObjIso₂ F₁₂ G p q r hr X₁ X₂ X₃) ≪≫
      (mapBifunctor₁₂BifunctorMapObjIso₃ F₁₂ G p q r hr X₁ X₂ X₃).symm) q

end

end

section

variable (F : C₁ ⥤ C₂₃ ⥤ C₄) (G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃)

@[simps]
def _root_.CategoryTheory.bifunctorComp₂₃Obj (X₁ : C₁) : C₂ ⥤ C₃ ⥤ C₄ where
  obj X₂ :=
    { obj := fun X₃ => (F.obj X₁).obj ((G₂₃.obj X₂).obj X₃)
      map := fun {X₃ Y₃} φ => (F.obj X₁).map ((G₂₃.obj X₂).map φ) }
  map {X₂ Y₂} φ :=
    { app := fun X₃ => (F.obj X₁).map ((G₂₃.map φ).app X₃)
      naturality := fun {X₃ Y₃} φ => by
        dsimp
        simp only [← Functor.map_comp, NatTrans.naturality] }

@[simps]
def _root_.CategoryTheory.bifunctorComp₂₃ : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ where
  obj X₁ := bifunctorComp₂₃Obj F G₂₃ X₁
  map {X₁ Y₁} φ :=
    { app := fun X₂ =>
        { app := fun X₃ => (F.map φ).app ((G₂₃.obj X₂).obj X₃) } }

variable
  {I₁ I₂ I₃ I₂₃ J : Type*} (p : I₂ × I₃ → I₂₃) (q : I₁ × I₂₃ → J)
    (r : I₁ × I₂ × I₃ → J) (hr : ∀ (i : I₁ × I₂ × I₃), r i = q ⟨i.1, p i.2⟩)

variable (I₁)

def p'' : I₁ × I₂ × I₃ → I₁ × I₂₃ := fun ⟨i₁, i₂₃⟩ => ⟨i₁, p i₂₃⟩

variable {I₁} (I₂₃)

def γ' (X₁ : GradedObject I₁ C₁) : GradedObject (I₁ × I₂₃) (C₂₃ ⥤ C₄) :=
  fun ⟨i₁, _⟩ => F.obj (X₁ i₁)

variable {I₂₃}

section

class HasGoodBifunctorBifunctor₂₃Obj (hr : ∀ (i : I₁ × I₂ × I₃), r i = q ⟨i.1, p i.2⟩)
  (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂) (X₃ : GradedObject I₃ C₃)
    [HasMap (((mapBifunctorFunctor G₂₃ I₂ I₃).obj X₂).obj X₃) p]
    [HasMap (((mapBifunctorFunctor F I₁ I₂₃).obj X₁).obj (mapBifunctorMapObj G₂₃ p X₂ X₃)) q] :=
  hasMap₂ : HasMap ((((mapTrifunctorFunctor (bifunctorComp₂₃ F G₂₃) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) r
  hasMap₃ : HasMap ((((mapTrifunctorFunctor (bifunctorComp₂₃ F G₂₃) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) (p'' I₁ p)
  hasMap₄ : HasMap (((((mapTrifunctorFunctor (bifunctorComp₂₃ F G₂₃) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃).mapObj (p'' I₁ p)) q
  hasMap₅ : HasMap ((comap C₂₃ _root_.Prod.snd).obj (((mapBifunctorFunctor G₂₃ I₂ I₃).obj X₂).obj X₃)) (p'' I₁ p)
  preservesMap : PreservesMap (γ' F I₂₃ X₁) (p'' I₁ p) ((comap C₂₃ _root_.Prod.snd).obj (((mapBifunctorFunctor G₂₃ I₂ I₃).obj X₂).obj X₃))

variable (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂) (X₃ : GradedObject I₃ C₃)
  [HasMap (((mapBifunctorFunctor G₂₃ I₂ I₃).obj X₂).obj X₃) p]
  [HasMap (((mapBifunctorFunctor F I₁ I₂₃).obj X₁).obj (mapBifunctorMapObj G₂₃ p X₂ X₃)) q]
  [H : HasGoodBifunctorBifunctor₂₃Obj F G₂₃ p q r hr X₁ X₂ X₃]

attribute [local ext] mapObj_ext

noncomputable def mapBifunctorBifunctor₂₃MapObjIso₁ :
    have := H.hasMap₂
    have := H.hasMap₃
    have := H.hasMap₄
    (((((mapTrifunctorFunctor (bifunctorComp₂₃ F G₂₃) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃).mapObj (p'' I₁ p)).mapObj q ≅
      mapTrifunctorMapObj (bifunctorComp₂₃ F G₂₃) r X₁ X₂ X₃ :=
  have := H.hasMap₂
  have := H.hasMap₃
  have := H.hasMap₄
  ((((mapTrifunctorFunctor (bifunctorComp₂₃ F G₂₃) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃).mapObjMapObjIso (p'' I₁ p) q r hr

noncomputable def mapBifunctorBifunctor₂₃MapObjIso₂ :
    have := H.hasMap₃
    have := H.hasMap₅
    (((((mapTrifunctorFunctor (bifunctorComp₂₃ F G₂₃) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃).mapObj (p'' I₁ p)) ≅
      (applyFunctorsObj (γ' F I₂₃ X₁)).obj (((comap _ _root_.Prod.snd).obj (((mapBifunctorFunctor G₂₃ I₂ I₃).obj X₂).obj X₃)).mapObj (p'' I₁ p)) :=
  have := H.hasMap₃
  have := H.hasMap₅
  have := H.preservesMap
  comapObjApplyFunctorsObjObjMapObjIso (γ' F I₂₃ X₁) (p'' I₁ p) ((comap _ _root_.Prod.snd).obj (((mapBifunctorFunctor G₂₃ I₂ I₃).obj X₂).obj X₃))

noncomputable def mapBifunctorBifunctor₂₃MapObjIso₃ :
    have := H.hasMap₅
    ((mapBifunctorFunctor F I₁ I₂₃).obj X₁).obj (mapBifunctorMapObj G₂₃ p X₂ X₃) ≅
      (applyFunctorsObj (γ' F I₂₃ X₁)).obj (((comap _ _root_.Prod.snd).obj (((mapBifunctorFunctor G₂₃ I₂ I₃).obj X₂).obj X₃)).mapObj (p'' I₁ p)) :=
  have := H.hasMap₅
  isoMk _ _ (fun ⟨i₁, i₂₃⟩ => (F.obj (X₁ i₁)).mapIso
    { hom := descMapObj _ _ (fun ⟨i₂, i₃⟩ _ =>
        ((comap C₂₃ _root_.Prod.snd).obj (((mapBifunctorFunctor G₂₃ I₂ I₃).obj X₂).obj X₃)).ιMapObj (p'' I₁ p) ⟨i₁, i₂, i₃⟩ ⟨i₁, i₂₃⟩ (by aesop))
      inv := descMapObj _ _ (fun ⟨i₁', i₂, i₃⟩ h =>
        (((mapBifunctorFunctor G₂₃ I₂ I₃).obj X₂).obj X₃).ιMapObj p ⟨i₂, i₃⟩ i₂₃ (congr_arg _root_.Prod.snd h))
      inv_hom_id := by
        ext ⟨i₁', i₂, i₃⟩ h
        obtain rfl : i₁' = i₁ := (congr_arg _root_.Prod.fst h)
        simp })

noncomputable def mapBifunctorBifunctor₂₃MapObjIso :
    have := H.hasMap₂
    mapTrifunctorMapObj (bifunctorComp₂₃ F G₂₃) r X₁ X₂ X₃ ≅
      mapBifunctorMapObj F q X₁ (mapBifunctorMapObj G₂₃ p X₂ X₃) :=
  have := H.hasMap₄
  (mapBifunctorBifunctor₂₃MapObjIso₁ F G₂₃ p q r hr X₁ X₂ X₃).symm ≪≫
    mapIso (mapBifunctorBifunctor₂₃MapObjIso₂ F G₂₃ p q r hr X₁ X₂ X₃ ≪≫
      (mapBifunctorBifunctor₂₃MapObjIso₃ F G₂₃ p q r hr X₁ X₂ X₃).symm) q

end

end

section

variable
  {F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂} {G : C₁₂ ⥤ C₃ ⥤ C₄}
  {F : C₁ ⥤ C₂₃ ⥤ C₄} {G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃}
  (associator : bifunctorComp₁₂ F₁₂ G ≅ bifunctorComp₂₃ F G₂₃)
  {I₁ I₂ I₃ I₁₂ I₂₃ J : Type*} (p₁₂ : I₁ × I₂ → I₁₂) (q₁₂ : I₁₂ × I₃ → J)
    (p₂₃ : I₂ × I₃ → I₂₃) (q₂₃ : I₁ × I₂₃ → J)
    (r : I₁ × I₂ × I₃ → J) (hr₁₂ : ∀ (i : I₁ × I₂ × I₃), r i = q₁₂ ⟨p₁₂ ⟨i.1, i.2.1⟩, i.2.2⟩)
    (hr₂₃ : ∀ (i : I₁ × I₂ × I₃), r i = q₂₃ ⟨i.1, p₂₃ i.2⟩)
  (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂) (X₃ : GradedObject I₃ C₃)
  [HasMap (((mapBifunctorFunctor F₁₂ I₁ I₂).obj X₁).obj X₂) p₁₂]
  [HasMap (((mapBifunctorFunctor G I₁₂ I₃).obj (mapBifunctorMapObj F₁₂ p₁₂ X₁ X₂)).obj X₃) q₁₂]
  [HasMap (((mapBifunctorFunctor G₂₃ I₂ I₃).obj X₂).obj X₃) p₂₃]
  [HasMap (((mapBifunctorFunctor F I₁ I₂₃).obj X₁).obj (mapBifunctorMapObj G₂₃ p₂₃ X₂ X₃)) q₂₃]

class HasGoodAssociator
  (associator : bifunctorComp₁₂ F₁₂ G ≅ bifunctorComp₂₃ F G₂₃)
  {I₁ I₂ I₃ I₁₂ I₂₃ J : Type*} (p₁₂ : I₁ × I₂ → I₁₂) (q₁₂ : I₁₂ × I₃ → J)
    (p₂₃ : I₂ × I₃ → I₂₃) (q₂₃ : I₁ × I₂₃ → J)
    (r : I₁ × I₂ × I₃ → J) (hr₁₂ : ∀ (i : I₁ × I₂ × I₃), r i = q₁₂ ⟨p₁₂ ⟨i.1, i.2.1⟩, i.2.2⟩)
    (hr₂₃ : ∀ (i : I₁ × I₂ × I₃), r i = q₂₃ ⟨i.1, p₂₃ i.2⟩)
  (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂) (X₃ : GradedObject I₃ C₃)
  [HasMap (((mapBifunctorFunctor F₁₂ I₁ I₂).obj X₁).obj X₂) p₁₂]
  [HasMap (((mapBifunctorFunctor G₂₃ I₂ I₃).obj X₂).obj X₃) p₂₃]
  [h₁₂ : HasMap (((mapBifunctorFunctor G I₁₂ I₃).obj (mapBifunctorMapObj F₁₂ p₁₂ X₁ X₂)).obj X₃) q₁₂]
  [h₂₃ : HasMap (((mapBifunctorFunctor F I₁ I₂₃).obj X₁).obj (mapBifunctorMapObj G₂₃ p₂₃ X₂ X₃)) q₂₃]
  where
  H₁₂ : HasGoodBifunctor₁₂BifunctorObj F₁₂ G p₁₂ q₁₂ r hr₁₂ X₁ X₂ X₃
  H₂₃ : HasGoodBifunctorBifunctor₂₃Obj F G₂₃ p₂₃ q₂₃ r hr₂₃ X₁ X₂ X₃

variable [H : HasGoodAssociator associator p₁₂ q₁₂ p₂₃ q₂₃ r hr₁₂ hr₂₃ X₁ X₂ X₃]

noncomputable def mapBifunctorBifunctorAssociator :
    mapBifunctorMapObj G q₁₂ (mapBifunctorMapObj F₁₂ p₁₂ X₁ X₂) X₃ ≅
      mapBifunctorMapObj F q₂₃ X₁ (mapBifunctorMapObj G₂₃ p₂₃ X₂ X₃) :=
  have := H.H₁₂.hasMap₂
  have := H.H₂₃.hasMap₂
  letI := H.H₁₂
  letI := H.H₂₃
  (mapBifunctor₁₂BifunctorMapObjIso F₁₂ G p₁₂ q₁₂ r hr₁₂ X₁ X₂ X₃).symm ≪≫
    mapIso ((((mapTrifunctorFunctorMapIso associator I₁ I₂ I₃).app X₁).app X₂).app X₃) r ≪≫
    mapBifunctorBifunctor₂₃MapObjIso F G₂₃ p₂₃ q₂₃ r hr₂₃ X₁ X₂ X₃

end-/

end

end GradedObject

end CategoryTheory
