/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.GradedObject.Bifunctor
public import Mathlib.CategoryTheory.Functor.Trifunctor
/-!
# The action of trifunctors on graded objects

Given a trifunctor `F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄` and types `I₁`, `I₂` and `I₃`, we define a functor
`GradedObject I₁ C₁ ⥤ GradedObject I₂ C₂ ⥤ GradedObject I₃ C₃ ⥤ GradedObject (I₁ × I₂ × I₃) C₄`
(see `mapTrifunctor`). When we have a map `p : I₁ × I₂ × I₃ → J` and suitable coproducts
exist, we define a functor
`GradedObject I₁ C₁ ⥤ GradedObject I₂ C₂ ⥤ GradedObject I₃ C₃ ⥤ GradedObject J C₄`
(see `mapTrifunctorMap`) which sends graded objects `X₁`, `X₂`, `X₃` to the graded object
which sets `j` to the coproduct of the objects `((F.obj (X₁ i₁)).obj (X₂ i₂)).obj (X₃ i₃)`
for `p ⟨i₁, i₂, i₃⟩ = j`.

This shall be used in order to construct the associator isomorphism for the monoidal
category structure on `GradedObject I C` induced by a monoidal structure on `C` and
an additive monoid structure on `I` (TODO @joelriou).

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

variable {C₁ C₂ C₃ C₄ C₁₂ C₂₃ : Type*}
  [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄] [Category* C₁₂] [Category* C₂₃]

namespace GradedObject

section

variable (F F' : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄)

/-- Auxiliary definition for `mapTrifunctor`. -/
@[simps]
def mapTrifunctorObj {I₁ : Type*} (X₁ : GradedObject I₁ C₁) (I₂ I₃ : Type*) :
    GradedObject I₂ C₂ ⥤ GradedObject I₃ C₃ ⥤ GradedObject (I₁ × I₂ × I₃) C₄ where
  obj X₂ :=
    { obj := fun X₃ x => ((F.obj (X₁ x.1)).obj (X₂ x.2.1)).obj (X₃ x.2.2)
      map := fun {_ _} φ x => ((F.obj (X₁ x.1)).obj (X₂ x.2.1)).map (φ x.2.2) }
  map {X₂ Y₂} φ :=
    { app := fun X₃ x => ((F.obj (X₁ x.1)).map (φ x.2.1)).app (X₃ x.2.2) }

set_option backward.defeqAttrib.useBackward true in
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
end

section

variable {F F' : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄}

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `mapTrifunctor F I₁ I₂ I₃ ⟶ mapTrifunctor F' I₁ I₂ I₃`
induced by a natural transformation `F ⟶ F'` of trifunctors. -/
@[simps]
def mapTrifunctorMapNatTrans (α : F ⟶ F') (I₁ I₂ I₃ : Type*) :
    mapTrifunctor F I₁ I₂ I₃ ⟶ mapTrifunctor F' I₁ I₂ I₃ where
  app X₁ :=
    { app := fun X₂ =>
        { app := fun _ _ => ((α.app _).app _).app _ }
      naturality := fun {X₂ Y₂} φ => by
        ext X₃ ⟨i₁, i₂, i₃⟩
        dsimp
        simp only [← NatTrans.comp_app, NatTrans.naturality] }
  naturality := fun {X₁ Y₁} φ => by
    ext X₂ X₃ ⟨i₁, i₂, i₃⟩
    dsimp
    simp only [← NatTrans.comp_app, NatTrans.naturality]

set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism `mapTrifunctor F I₁ I₂ I₃ ≅ mapTrifunctor F' I₁ I₂ I₃`
induced by a natural isomorphism `F ≅ F'` of trifunctors. -/
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

variable (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄)
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

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
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
      map := fun {_ _} φ => mapTrifunctorMapMap F p (𝟙 X₁) (𝟙 X₂) φ
      map_id := fun X₃ => by
        ext j i₁ i₂ i₃ h
        simp only [ι_mapTrifunctorMapMap, categoryOfGradedObjects_id, Functor.map_id,
          NatTrans.id_app, id_comp, comp_id]
      map_comp := fun {X₃ Y₃ Z₃} φ ψ => by
        ext j i₁ i₂ i₃ h
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
    simp only [ι_mapTrifunctorMapMap, categoryOfGradedObjects_id, Functor.map_id,
      NatTrans.id_app, id_comp, comp_id]
  map_comp {X₂ Y₂ Z₂} φ ψ := by
    ext X₃ j i₁ i₂ i₃
    simp only [ι_mapTrifunctorMapMap, categoryOfGradedObjects_id, Functor.map_id,
      NatTrans.id_app, categoryOfGradedObjects_comp, Functor.map_comp, NatTrans.comp_app,
      id_comp, assoc, ι_mapTrifunctorMapMap_assoc]

set_option backward.defeqAttrib.useBackward true in
/-- Given a trifunctor `F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄` and a map `p : I₁ × I₂ × I₃ → J`,
this is the functor
`GradedObject I₁ C₁ ⥤ GradedObject I₂ C₂ ⥤ GradedObject I₃ C₃ ⥤ GradedObject J C₄`
sending `X₁ : GradedObject I₁ C₁`, `X₂ : GradedObject I₂ C₂` and `X₃ : GradedObject I₃ C₃`
to the `J`-graded object sending `j` to the coproduct of
`((F.obj (X₁ i₁)).obj (X₂ i₂)).obj (X₃ i₃)` for `p ⟨i₁, i₂, i₃⟩ = j`. -/
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

attribute [simps] mapTrifunctorMap

end

section

variable (F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂) (G : C₁₂ ⥤ C₃ ⥤ C₄)
  {I₁ I₂ I₃ J : Type*} (r : I₁ × I₂ × I₃ → J)

/-- Given a map `r : I₁ × I₂ × I₃ → J`, a `BifunctorComp₁₂IndexData r` consists of the data
of a type `I₁₂`, maps `p : I₁ × I₂ → I₁₂` and `q : I₁₂ × I₃ → J`, such that `r` is obtained
by composition of `p` and `q`. -/
structure BifunctorComp₁₂IndexData where
  /-- an auxiliary type -/
  I₁₂ : Type*
  /-- a map `I₁ × I₂ → I₁₂` -/
  p : I₁ × I₂ → I₁₂
  /-- a map `I₁₂ × I₃ → J` -/
  q : I₁₂ × I₃ → J
  hpq (i : I₁ × I₂ × I₃) : q ⟨p ⟨i.1, i.2.1⟩, i.2.2⟩ = r i

variable {r} (ρ₁₂ : BifunctorComp₁₂IndexData r)
  (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂) (X₃ : GradedObject I₃ C₃)

/-- Given bifunctors `F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂`, `G : C₁₂ ⥤ C₃ ⥤ C₄`, graded objects
`X₁ : GradedObject I₁ C₁`, `X₂ : GradedObject I₂ C₂`, `X₃ : GradedObject I₃ C₃` and
`ρ₁₂ : BifunctorComp₁₂IndexData r`, this asserts that for all `i₁₂ : ρ₁₂.I₁₂` and `i₃ : I₃`,
the functor `G(-, X₃ i₃)` commutes with the coproducts of the `F₁₂(X₁ i₁, X₂ i₂)`
such that `ρ₁₂.p ⟨i₁, i₂⟩ = i₁₂`. -/
abbrev HasGoodTrifunctor₁₂Obj :=
  ∀ (i₁₂ : ρ₁₂.I₁₂) (i₃ : I₃), PreservesColimit
    (Discrete.functor (mapObjFun (((mapBifunctor F₁₂ I₁ I₂).obj X₁).obj X₂) ρ₁₂.p i₁₂))
      ((Functor.flip G).obj (X₃ i₃))

variable [HasMap (((mapBifunctor F₁₂ I₁ I₂).obj X₁).obj X₂) ρ₁₂.p]
  [HasMap (((mapBifunctor G ρ₁₂.I₁₂ I₃).obj (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂)).obj X₃) ρ₁₂.q]

/-- The inclusion of `(G.obj ((F₁₂.obj (X₁ i₁)).obj (X₂ i₂))).obj (X₃ i₃)` in
`mapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ j`
when `r (i₁, i₂, i₃) = j`. -/
noncomputable def ιMapBifunctor₁₂BifunctorMapObj (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
    (h : r (i₁, i₂, i₃) = j) :
    (G.obj ((F₁₂.obj (X₁ i₁)).obj (X₂ i₂))).obj (X₃ i₃) ⟶
      mapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ j :=
  (G.map (ιMapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂ i₁ i₂ _ rfl)).app (X₃ i₃) ≫
    ιMapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ (ρ₁₂.p ⟨i₁, i₂⟩) i₃ j
      (by rw [← h, ← ρ₁₂.hpq])

@[reassoc]
lemma ιMapBifunctor₁₂BifunctorMapObj_eq (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
    (h : r (i₁, i₂, i₃) = j) (i₁₂ : ρ₁₂.I₁₂) (h₁₂ : ρ₁₂.p ⟨i₁, i₂⟩ = i₁₂) :
    ιMapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j h =
      (G.map (ιMapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂ i₁ i₂ i₁₂ h₁₂)).app (X₃ i₃) ≫
      ιMapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ i₁₂ i₃ j
        (by rw [← h₁₂, ← h, ← ρ₁₂.hpq]) := by
  subst h₁₂
  rfl

/-- The cofan consisting of the inclusions given by `ιMapBifunctor₁₂BifunctorMapObj`. -/
noncomputable def cofan₃MapBifunctor₁₂BifunctorMapObj (j : J) :
    ((((mapTrifunctor (bifunctorComp₁₂ F₁₂ G) I₁ I₂ I₃).obj X₁).obj X₂).obj
      X₃).CofanMapObjFun r j :=
  Cofan.mk (mapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ j)
    (fun ⟨⟨i₁, i₂, i₃⟩, (hi : r ⟨i₁, i₂, i₃⟩ = j)⟩ =>
      ιMapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j hi)

variable [H : HasGoodTrifunctor₁₂Obj F₁₂ G ρ₁₂ X₁ X₂ X₃]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cofan `cofan₃MapBifunctor₁₂BifunctorMapObj` is a colimit, see the induced isomorphism
`mapBifunctorComp₁₂MapObjIso`. -/
noncomputable def isColimitCofan₃MapBifunctor₁₂BifunctorMapObj (j : J) :
    IsColimit (cofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j) := by
  let c₁₂ := fun i₁₂ => (((mapBifunctor F₁₂ I₁ I₂).obj X₁).obj X₂).cofanMapObj ρ₁₂.p i₁₂
  have h₁₂ : ∀ i₁₂, IsColimit (c₁₂ i₁₂) := fun i₁₂ =>
    (((mapBifunctor F₁₂ I₁ I₂).obj X₁).obj X₂).isColimitCofanMapObj ρ₁₂.p i₁₂
  let c := (((mapBifunctor G ρ₁₂.I₁₂ I₃).obj
    (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂)).obj X₃).cofanMapObj ρ₁₂.q j
  have hc : IsColimit c := (((mapBifunctor G ρ₁₂.I₁₂ I₃).obj
    (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂)).obj X₃).isColimitCofanMapObj ρ₁₂.q j
  let c₁₂' := fun (i : ρ₁₂.q ⁻¹' {j}) => (G.flip.obj (X₃ i.1.2)).mapCocone (c₁₂ i.1.1)
  have hc₁₂' : ∀ i, IsColimit (c₁₂' i) := fun i => isColimitOfPreserves _ (h₁₂ i.1.1)
  let Z := (((mapTrifunctor (bifunctorComp₁₂ F₁₂ G) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃
  let p' : I₁ × I₂ × I₃ → ρ₁₂.I₁₂ × I₃ := fun ⟨i₁, i₂, i₃⟩ => ⟨ρ₁₂.p ⟨i₁, i₂⟩, i₃⟩
  let e : ∀ (i₁₂ : ρ₁₂.I₁₂) (i₃ : I₃), p' ⁻¹' {(i₁₂, i₃)} ≃ ρ₁₂.p ⁻¹' {i₁₂} := fun i₁₂ i₃ =>
    { toFun := fun ⟨⟨i₁, i₂, i₃'⟩, hi⟩ => ⟨⟨i₁, i₂⟩, by cat_disch⟩
      invFun := fun ⟨⟨i₁, i₂⟩, hi⟩ => ⟨⟨i₁, i₂, i₃⟩, by cat_disch⟩
      left_inv := fun ⟨⟨i₁, i₂, i₃'⟩, hi⟩ => by
        obtain rfl : i₃ = i₃' := by cat_disch
        rfl }
  let c₁₂'' : ∀ (i : ρ₁₂.q ⁻¹' {j}), CofanMapObjFun Z p' (i.1.1, i.1.2) :=
    fun ⟨⟨i₁₂, i₃⟩, hi⟩ => by
      refine (Cocone.precompose (Iso.hom ?_)).obj ((Cocone.whiskeringEquivalence
        (Discrete.equivalence (e i₁₂ i₃))).functor.obj (c₁₂' ⟨⟨i₁₂, i₃⟩, hi⟩))
      refine (Discrete.natIso (fun ⟨⟨i₁, i₂, i₃'⟩, hi⟩ =>
        (G.obj ((F₁₂.obj (X₁ i₁)).obj (X₂ i₂))).mapIso (eqToIso ?_)))
      obtain rfl : i₃' = i₃ := congr_arg _root_.Prod.snd hi
      rfl
  have h₁₂'' : ∀ i, IsColimit (c₁₂'' i) := fun _ =>
    (IsColimit.precomposeHomEquiv _ _).symm (IsColimit.whiskerEquivalenceEquiv _ (hc₁₂' _))
  refine IsColimit.ofIsoColimit (isColimitCofanMapObjComp Z p' ρ₁₂.q r ρ₁₂.hpq j
    (fun ⟨i₁₂, i₃⟩ h => c₁₂'' ⟨⟨i₁₂, i₃⟩, h⟩) (fun ⟨i₁₂, i₃⟩ h => h₁₂'' ⟨⟨i₁₂, i₃⟩, h⟩) c hc)
    (Cocone.ext (Iso.refl _) (fun ⟨⟨i₁, i₂, i₃⟩, h⟩ => ?_))
  dsimp [Cofan.inj, c₁₂'', Z, p']
  rw [comp_id, Functor.map_id, id_comp]
  rfl

variable {F₁₂ G ρ₁₂ X₁ X₂ X₃}

include ρ₁₂ in
lemma HasGoodTrifunctor₁₂Obj.hasMap :
    HasMap ((((mapTrifunctor (bifunctorComp₁₂ F₁₂ G) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) r :=
  fun j => ⟨_, isColimitCofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j⟩

variable (F₁₂ G ρ₁₂ X₁ X₂ X₃)

section
variable [HasMap ((((mapTrifunctor (bifunctorComp₁₂ F₁₂ G) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) r]

/-- The action on graded objects of a trifunctor obtained by composition of two
bifunctors can be computed as a composition of the actions of these two bifunctors. -/
noncomputable def mapBifunctorComp₁₂MapObjIso :
    mapTrifunctorMapObj (bifunctorComp₁₂ F₁₂ G) r X₁ X₂ X₃ ≅
    mapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ :=
  isoMk _ _ (fun j => (CofanMapObjFun.iso
    (isColimitCofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j)).symm)

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma ι_mapBifunctorComp₁₂MapObjIso_hom (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
    (h : r (i₁, i₂, i₃) = j) :
    ιMapTrifunctorMapObj (bifunctorComp₁₂ F₁₂ G) r X₁ X₂ X₃ i₁ i₂ i₃ j h ≫
      (mapBifunctorComp₁₂MapObjIso F₁₂ G ρ₁₂ X₁ X₂ X₃).hom j =
      ιMapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j h := by
  dsimp [mapBifunctorComp₁₂MapObjIso]
  apply CofanMapObjFun.ιMapObj_iso_inv

@[reassoc (attr := simp)]
lemma ι_mapBifunctorComp₁₂MapObjIso_inv (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
    (h : r (i₁, i₂, i₃) = j) :
    ιMapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫
      (mapBifunctorComp₁₂MapObjIso F₁₂ G ρ₁₂ X₁ X₂ X₃).inv j =
      ιMapTrifunctorMapObj (bifunctorComp₁₂ F₁₂ G) r X₁ X₂ X₃ i₁ i₂ i₃ j h :=
  CofanMapObjFun.inj_iso_hom
    (isColimitCofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j) _ h

end

variable {X₁ X₂ X₃ F₁₂ G ρ₁₂}
variable {j : J} {A : C₄}

@[ext]
lemma mapBifunctor₁₂BifunctorMapObj_ext {A : C₄}
    {f g : mapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ j ⟶ A}
    (h : ∀ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (h : r ⟨i₁, i₂, i₃⟩ = j),
      ιMapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ f =
        ιMapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ g) : f = g := by
  apply Cofan.IsColimit.hom_ext (isColimitCofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j)
  rintro ⟨i, hi⟩
  exact h _ _ _ hi

section

variable (f : ∀ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (_ : r ⟨i₁, i₂, i₃⟩ = j),
  (G.obj ((F₁₂.obj (X₁ i₁)).obj (X₂ i₂))).obj (X₃ i₃) ⟶ A)

/-- Constructor for morphisms from
`mapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ j`. -/
noncomputable def mapBifunctor₁₂BifunctorDesc :
    mapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ j ⟶ A :=
  Cofan.IsColimit.desc (isColimitCofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j)
    (fun i ↦ f i.1.1 i.1.2.1 i.1.2.2 i.2)

@[reassoc (attr := simp)]
lemma ι_mapBifunctor₁₂BifunctorDesc
    (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (h : r ⟨i₁, i₂, i₃⟩ = j) :
    ιMapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫
      mapBifunctor₁₂BifunctorDesc f = f i₁ i₂ i₃ h :=
  Cofan.IsColimit.fac
    (isColimitCofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j) _ ⟨_, h⟩

end

end

section

variable (F : C₁ ⥤ C₂₃ ⥤ C₄) (G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃)
  {I₁ I₂ I₃ J : Type*} (r : I₁ × I₂ × I₃ → J)

/-- Given a map `r : I₁ × I₂ × I₃ → J`, a `BifunctorComp₂₃IndexData r` consists of the data
of a type `I₂₃`, maps `p : I₂ × I₃ → I₂₃` and `q : I₁ × I₂₃ → J`, such that `r` is obtained
by composition of `p` and `q`. -/
structure BifunctorComp₂₃IndexData where
  /-- an auxiliary type -/
  I₂₃ : Type*
  /-- a map `I₂ × I₃ → I₂₃` -/
  p : I₂ × I₃ → I₂₃
  /-- a map `I₁ × I₂₃ → J` -/
  q : I₁ × I₂₃ → J
  hpq (i : I₁ × I₂ × I₃) : q ⟨i.1, p i.2⟩ = r i

variable {r} (ρ₂₃ : BifunctorComp₂₃IndexData r)
  (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂) (X₃ : GradedObject I₃ C₃)

/-- Given bifunctors `F : C₁ ⥤ C₂₃ ⥤ C₄`, `G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃`, graded objects
`X₁ : GradedObject I₁ C₁`, `X₂ : GradedObject I₂ C₂`, `X₃ : GradedObject I₃ C₃` and
`ρ₂₃ : BifunctorComp₂₃IndexData r`, this asserts that for all `i₁ : I₁` and `i₂₃ : ρ₂₃.I₂₃`,
the functor `F(X₁ i₁, _)` commutes with the coproducts of the `G₂₃(X₂ i₂, X₃ i₃)`
such that `ρ₂₃.p ⟨i₂, i₃⟩ = i₂₃`. -/
abbrev HasGoodTrifunctor₂₃Obj :=
  ∀ (i₁ : I₁) (i₂₃ : ρ₂₃.I₂₃), PreservesColimit (Discrete.functor
    (mapObjFun (((mapBifunctor G₂₃ I₂ I₃).obj X₂).obj X₃) ρ₂₃.p i₂₃)) (F.obj (X₁ i₁))

variable [HasMap (((mapBifunctor G₂₃ I₂ I₃).obj X₂).obj X₃) ρ₂₃.p]
  [HasMap (((mapBifunctor F I₁ ρ₂₃.I₂₃).obj X₁).obj (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃)) ρ₂₃.q]

/-- The inclusion of `(F.obj (X₁ i₁)).obj ((G₂₃.obj (X₂ i₂)).obj (X₃ i₃))` in
`mapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) j`
when `r (i₁, i₂, i₃) = j`. -/
noncomputable def ιMapBifunctorBifunctor₂₃MapObj (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
    (h : r (i₁, i₂, i₃) = j) :
    (F.obj (X₁ i₁)).obj ((G₂₃.obj (X₂ i₂)).obj (X₃ i₃)) ⟶
      mapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) j :=
  (F.obj (X₁ i₁)).map (ιMapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃ i₂ i₃ _ rfl) ≫
    ιMapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) i₁ (ρ₂₃.p ⟨i₂, i₃⟩) j
      (by rw [← h, ← ρ₂₃.hpq])

@[reassoc]
lemma ιMapBifunctorBifunctor₂₃MapObj_eq (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
    (h : r (i₁, i₂, i₃) = j) (i₂₃ : ρ₂₃.I₂₃) (h₂₃ : ρ₂₃.p ⟨i₂, i₃⟩ = i₂₃) :
    ιMapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h =
    (F.obj (X₁ i₁)).map (ιMapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃ i₂ i₃ i₂₃ h₂₃) ≫
      ιMapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) i₁ i₂₃ j
        (by rw [← h, ← h₂₃, ← ρ₂₃.hpq]) := by
  subst h₂₃
  rfl

/-- The cofan consisting of the inclusions given by `ιMapBifunctorBifunctor₂₃MapObj`. -/
noncomputable def cofan₃MapBifunctorBifunctor₂₃MapObj (j : J) :
    ((((mapTrifunctor (bifunctorComp₂₃ F G₂₃) I₁ I₂ I₃).obj X₁).obj X₂).obj
      X₃).CofanMapObjFun r j :=
  Cofan.mk (mapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) j)
    (fun ⟨⟨i₁, i₂, i₃⟩, (hi : r ⟨i₁, i₂, i₃⟩ = j)⟩ =>
      ιMapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j hi)

variable [H : HasGoodTrifunctor₂₃Obj F G₂₃ ρ₂₃ X₁ X₂ X₃]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cofan `cofan₃MapBifunctorBifunctor₂₃MapObj` is a colimit, see the induced isomorphism
`mapBifunctorComp₁₂MapObjIso`. -/
noncomputable def isColimitCofan₃MapBifunctorBifunctor₂₃MapObj (j : J) :
    IsColimit (cofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j) := by
  let c₂₃ := fun i₂₃ => (((mapBifunctor G₂₃ I₂ I₃).obj X₂).obj X₃).cofanMapObj ρ₂₃.p i₂₃
  have h₂₃ : ∀ i₂₃, IsColimit (c₂₃ i₂₃) := fun i₂₃ =>
    (((mapBifunctor G₂₃ I₂ I₃).obj X₂).obj X₃).isColimitCofanMapObj ρ₂₃.p i₂₃
  let c := (((mapBifunctor F I₁ ρ₂₃.I₂₃).obj X₁).obj
    (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃)).cofanMapObj ρ₂₃.q j
  have hc : IsColimit c := (((mapBifunctor F I₁ ρ₂₃.I₂₃).obj X₁).obj
    (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃)).isColimitCofanMapObj ρ₂₃.q j
  let c₂₃' := fun (i : ρ₂₃.q ⁻¹' {j}) => (F.obj (X₁ i.1.1)).mapCocone (c₂₃ i.1.2)
  have hc₂₃' : ∀ i, IsColimit (c₂₃' i) := fun i => isColimitOfPreserves _ (h₂₃ i.1.2)
  let Z := (((mapTrifunctor (bifunctorComp₂₃ F G₂₃) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃
  let p' : I₁ × I₂ × I₃ → I₁ × ρ₂₃.I₂₃ := fun ⟨i₁, i₂, i₃⟩ => ⟨i₁, ρ₂₃.p ⟨i₂, i₃⟩⟩
  let e : ∀ (i₁ : I₁) (i₂₃ : ρ₂₃.I₂₃), p' ⁻¹' {(i₁, i₂₃)} ≃ ρ₂₃.p ⁻¹' {i₂₃} := fun i₁ i₂₃ =>
    { toFun := fun ⟨⟨i₁', i₂, i₃⟩, hi⟩ => ⟨⟨i₂, i₃⟩, by cat_disch⟩
      invFun := fun ⟨⟨i₂, i₃⟩, hi⟩  => ⟨⟨i₁, i₂, i₃⟩, by cat_disch⟩
      left_inv := fun ⟨⟨i₁', i₂, i₃⟩, hi⟩ => by
        obtain rfl : i₁ = i₁' := by cat_disch
        rfl }
  let c₂₃'' : ∀ (i : ρ₂₃.q ⁻¹' {j}), CofanMapObjFun Z p' (i.1.1, i.1.2) :=
    fun ⟨⟨i₁, i₂₃⟩, hi⟩ => by
      refine (Cocone.precompose (Iso.hom ?_)).obj ((Cocone.whiskeringEquivalence
        (Discrete.equivalence (e i₁ i₂₃))).functor.obj (c₂₃' ⟨⟨i₁, i₂₃⟩, hi⟩))
      refine Discrete.natIso (fun ⟨⟨i₁', i₂, i₃⟩, hi⟩ => eqToIso ?_)
      obtain rfl : i₁' = i₁ := congr_arg _root_.Prod.fst hi
      rfl
  have h₂₃'' : ∀ i, IsColimit (c₂₃'' i) := fun _ =>
    (IsColimit.precomposeHomEquiv _ _).symm (IsColimit.whiskerEquivalenceEquiv _ (hc₂₃' _))
  refine IsColimit.ofIsoColimit (isColimitCofanMapObjComp Z p' ρ₂₃.q r ρ₂₃.hpq j
    (fun ⟨i₁, i₂₃⟩ h => c₂₃'' ⟨⟨i₁, i₂₃⟩, h⟩) (fun ⟨i₁, i₂₃⟩ h => h₂₃'' ⟨⟨i₁, i₂₃⟩, h⟩) c hc)
    (Cocone.ext (Iso.refl _) (fun ⟨⟨i₁, i₂, i₃⟩, h⟩ => ?_))
  dsimp [Cofan.inj, c₂₃'', Z, p', e]
  rw [comp_id, id_comp]
  rfl

variable {F₁₂ G ρ₁₂ X₁ X₂ X₃}

include ρ₂₃ in
lemma HasGoodTrifunctor₂₃Obj.hasMap :
    HasMap ((((mapTrifunctor (bifunctorComp₂₃ F G₂₃) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) r :=
  fun j => ⟨_, isColimitCofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j⟩

variable (F₁₂ G ρ₁₂ X₁ X₂ X₃)

section
variable [HasMap ((((mapTrifunctor (bifunctorComp₂₃ F G₂₃) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) r]

/-- The action on graded objects of a trifunctor obtained by composition of two
bifunctors can be computed as a composition of the actions of these two bifunctors. -/
noncomputable def mapBifunctorComp₂₃MapObjIso :
    mapTrifunctorMapObj (bifunctorComp₂₃ F G₂₃) r X₁ X₂ X₃ ≅
    mapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) :=
  isoMk _ _ (fun j => (CofanMapObjFun.iso
    (isColimitCofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j)).symm)

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma ι_mapBifunctorComp₂₃MapObjIso_hom (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
    (h : r (i₁, i₂, i₃) = j) :
    ιMapTrifunctorMapObj (bifunctorComp₂₃ F G₂₃) r X₁ X₂ X₃ i₁ i₂ i₃ j h ≫
      (mapBifunctorComp₂₃MapObjIso F G₂₃ ρ₂₃ X₁ X₂ X₃).hom j =
      ιMapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h := by
  dsimp [mapBifunctorComp₂₃MapObjIso]
  apply CofanMapObjFun.ιMapObj_iso_inv

@[reassoc (attr := simp)]
lemma ι_mapBifunctorComp₂₃MapObjIso_inv (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
    (h : r (i₁, i₂, i₃) = j) :
    ιMapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫
      (mapBifunctorComp₂₃MapObjIso F G₂₃ ρ₂₃ X₁ X₂ X₃).inv j =
      ιMapTrifunctorMapObj (bifunctorComp₂₃ F G₂₃) r X₁ X₂ X₃ i₁ i₂ i₃ j h :=
  CofanMapObjFun.inj_iso_hom
    (isColimitCofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j) _ h

end

variable {X₁ X₂ X₃ F G₂₃ ρ₂₃}
variable {j : J} {A : C₄}

@[ext]
lemma mapBifunctorBifunctor₂₃MapObj_ext
    {f g : mapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) j ⟶ A}
    (h : ∀ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (h : r ⟨i₁, i₂, i₃⟩ = j),
      ιMapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ f =
        ιMapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ g) : f = g := by
  apply Cofan.IsColimit.hom_ext (isColimitCofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j)
  rintro ⟨i, hi⟩
  exact h _ _ _ hi

section

variable
  (f : ∀ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (_ : r ⟨i₁, i₂, i₃⟩ = j),
    (F.obj (X₁ i₁)).obj ((G₂₃.obj (X₂ i₂)).obj (X₃ i₃)) ⟶ A)

/-- Constructor for morphisms from
`mapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) j`. -/
noncomputable def mapBifunctorBifunctor₂₃Desc :
    mapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) j ⟶ A :=
  Cofan.IsColimit.desc (isColimitCofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j)
    (fun i ↦ f i.1.1 i.1.2.1 i.1.2.2 i.2)

@[reassoc (attr := simp)]
lemma ι_mapBifunctorBifunctor₂₃Desc
    (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (h : r ⟨i₁, i₂, i₃⟩ = j) :
    ιMapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫
      mapBifunctorBifunctor₂₃Desc f = f i₁ i₂ i₃ h :=
  Cofan.IsColimit.fac
    (isColimitCofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j) _ ⟨_, h⟩

end


end

end GradedObject

end CategoryTheory
