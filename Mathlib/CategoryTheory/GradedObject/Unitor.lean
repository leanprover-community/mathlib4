/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.GradedObject.Bifunctor
import Mathlib.CategoryTheory.GradedObject.Single
/-!
# The left and right unitors

Given a bifunctor `F : C ⥤ D ⥤ D`, an object `X : C` such that `F.obj X ≅ 𝟭 D` and a
map `p : I × J → J` such that `hp : ∀ (j : J), p ⟨0, j⟩ = j`,
we define an isomorphism of `J`-graded objects for any `Y : GradedObject J D`.
`mapBifunctorLeftUnitor F X e p hp Y : mapBifunctorMapObj F p ((single₀ I).obj X) Y ≅ Y`.
Under similar assumptions, we also obtain a right unitor isomorphism
`mapBifunctorMapObj F p X ((single₀ I).obj Y) ≅ X`.

TODO (@joelriou): get the triangle identity.

-/

namespace CategoryTheory

open Category Limits

namespace GradedObject

section LeftUnitor

variable {C D I J : Type*} [Category C] [Category D]
  [Zero I] [DecidableEq I] [HasInitial C]
  (F : C ⥤ D ⥤ D) (X : C) (e : F.obj X ≅ 𝟭 D)
  [∀ (Y : D), PreservesColimit (Functor.empty.{0} C) (F.flip.obj Y)]
  (p : I × J → J) (hp : ∀ (j : J), p ⟨0, j⟩ = j)
  (Y Y' : GradedObject J D) (φ : Y ⟶ Y')

/-- Given `F : C ⥤ D ⥤ D`, `X : C`, `e : F.obj X ≅ 𝟭 D` and `Y : GradedObject J D`,
this is the isomorphism `((mapBifunctor F I J).obj ((single₀ I).obj X)).obj Y a ≅ Y a.2`
when `a : I × J` is such that `a.1 = 0`. -/
@[simps!]
noncomputable def mapBifunctorObjSingle₀ObjIso (a : I × J) (ha : a.1 = 0) :
    ((mapBifunctor F I J).obj ((single₀ I).obj X)).obj Y a ≅ Y a.2 :=
  (F.mapIso (singleObjApplyIsoOfEq _ X _ ha)).app _ ≪≫ e.app (Y a.2)

/-- Given `F : C ⥤ D ⥤ D`, `X : C` and `Y : GradedObject J D`,
`((mapBifunctor F I J).obj ((single₀ I).obj X)).obj Y a` is an initial when `a : I × J`
is such that `a.1 ≠ 0`. -/
noncomputable def mapBifunctorObjSingle₀ObjIsInitial (a : I × J) (ha : a.1 ≠ 0) :
    IsInitial (((mapBifunctor F I J).obj ((single₀ I).obj X)).obj Y a) :=
  IsInitial.isInitialObj (F.flip.obj (Y a.2)) _ (isInitialSingleObjApply _ _ _ ha)

/-- Given `F : C ⥤ D ⥤ D`, `X : C`, `e : F.obj X ≅ 𝟭 D`, `Y : GradedObject J D` and
`p : I × J → J` such that `p ⟨0, j⟩ = j` for all `j`,
this is the (colimit) cofan which shall be used to construct the isomorphism
`mapBifunctorMapObj F p ((single₀ I).obj X) Y ≅ Y`, see `mapBifunctorLeftUnitor`. -/
noncomputable def mapBifunctorLeftUnitorCofan (j : J) :
    (((mapBifunctor F I J).obj ((single₀ I).obj X)).obj Y).CofanMapObjFun p j :=
  CofanMapObjFun.mk _ _ _ (Y j) (fun a ha =>
    if ha : a.1 = 0 then
      (mapBifunctorObjSingle₀ObjIso F X e Y a ha).hom ≫ eqToHom (by aesop)
    else
      (mapBifunctorObjSingle₀ObjIsInitial F X Y a ha).to _)

@[simp, reassoc]
lemma mapBifunctorLeftUnitorCofan_inj (j : J) :
    (mapBifunctorLeftUnitorCofan F X e p hp Y j).inj ⟨⟨0, j⟩, hp j⟩ =
      (F.map (singleObjApplyIso (0 : I) X).hom).app (Y j) ≫ e.hom.app (Y j) := by
  simp [mapBifunctorLeftUnitorCofan]

/-- The cofan `mapBifunctorLeftUnitorCofan F X e p hp Y j` is a colimit. -/
noncomputable def mapBifunctorLeftUnitorCofanIsColimit (j : J) :
    IsColimit (mapBifunctorLeftUnitorCofan F X e p hp Y j) :=
  mkCofanColimit _
    (fun s => e.inv.app (Y j) ≫
      (F.map (singleObjApplyIso (0 : I) X).inv).app (Y j) ≫ s.inj ⟨⟨0, j⟩, hp j⟩)
    (fun s => by
      rintro ⟨⟨i, j'⟩, h⟩
      by_cases hi : i = 0
      · subst hi
        simp only [Set.mem_preimage, hp, Set.mem_singleton_iff] at h
        subst h
        simp
      · apply IsInitial.hom_ext
        exact mapBifunctorObjSingle₀ObjIsInitial _ _ _ _ hi)
    (fun s m hm => by simp [← hm ⟨⟨0, j⟩, hp j⟩])

lemma mapBifunctorLeftUnitor_hasMap :
    HasMap (((mapBifunctor F I J).obj ((single₀ I).obj X)).obj Y) p :=
  CofanMapObjFun.hasMap _ _ _ (mapBifunctorLeftUnitorCofanIsColimit F X e p hp Y)

variable [HasMap (((mapBifunctor F I J).obj ((single₀ I).obj X)).obj Y) p]
  [HasMap (((mapBifunctor F I J).obj ((single₀ I).obj X)).obj Y') p]

/-- Given `F : C ⥤ D ⥤ D`, `X : C`, `e : F.obj X ≅ 𝟭 D`, `Y : GradedObject J D` and
`p : I × J → J` such that `p ⟨0, j⟩ = j` for all `j`,
this is the left unitor isomorphism `mapBifunctorMapObj F p ((single₀ I).obj X) Y ≅ Y`. -/
noncomputable def mapBifunctorLeftUnitor : mapBifunctorMapObj F p ((single₀ I).obj X) Y ≅ Y :=
  isoMk _ _ (fun j => (CofanMapObjFun.iso
    (mapBifunctorLeftUnitorCofanIsColimit F X e p hp Y j)).symm)

@[reassoc (attr := simp)]
lemma ι_mapBifunctorLeftUnitor_hom_apply (j : J) :
    ιMapBifunctorMapObj F p ((single₀ I).obj X) Y 0 j j (hp j) ≫
      (mapBifunctorLeftUnitor F X e p hp Y).hom j =
      (F.map (singleObjApplyIso (0 : I) X).hom).app _ ≫ e.hom.app (Y j) := by
  dsimp [mapBifunctorLeftUnitor]
  erw [CofanMapObjFun.ιMapObj_iso_inv]
  rw [mapBifunctorLeftUnitorCofan_inj]

lemma mapBifunctorLeftUnitor_inv_apply (j : J) :
    (mapBifunctorLeftUnitor F X e p hp Y).inv j =
      e.inv.app (Y j) ≫ (F.map (singleObjApplyIso (0 : I) X).inv).app (Y j) ≫
      ιMapBifunctorMapObj F p ((single₀ I).obj X) Y 0 j j (hp j) := rfl

variable {Y Y'}

@[reassoc]
lemma mapBifunctorLeftUnitor_inv_naturality :
    φ ≫ (mapBifunctorLeftUnitor F X e p hp Y').inv =
      (mapBifunctorLeftUnitor F X e p hp Y).inv ≫ mapBifunctorMapMap F p (𝟙 _) φ := by
  ext j
  dsimp
  rw [mapBifunctorLeftUnitor_inv_apply, mapBifunctorLeftUnitor_inv_apply, assoc, assoc,
    ι_mapBifunctorMapMap]
  dsimp
  rw [Functor.map_id, NatTrans.id_app, id_comp]
  erw [← NatTrans.naturality_assoc, ← NatTrans.naturality_assoc]
  rfl

@[reassoc]
lemma mapBifunctorLeftUnitor_naturality :
    mapBifunctorMapMap F p (𝟙 _) φ ≫ (mapBifunctorLeftUnitor F X e p hp Y').hom =
      (mapBifunctorLeftUnitor F X e p hp Y).hom ≫ φ := by
  rw [← cancel_mono (mapBifunctorLeftUnitor F X e p hp Y').inv, assoc, assoc, Iso.hom_inv_id,
    comp_id, mapBifunctorLeftUnitor_inv_naturality, Iso.hom_inv_id_assoc]

end LeftUnitor

section RightUnitor

variable {C D I J : Type*} [Category C] [Category D]
  [Zero I] [DecidableEq I] [HasInitial C]
  (F : D ⥤ C ⥤ D) (Y : C) (e : F.flip.obj Y ≅ 𝟭 D)
  [∀ (X : D), PreservesColimit (Functor.empty.{0} C) (F.obj X)]
  (p : J × I → J)
  (hp : ∀ (j : J), p ⟨j, 0⟩ = j) (X X' : GradedObject J D) (φ : X ⟶ X')

/-- Given `F : D ⥤ C ⥤ D`, `Y : C`, `e : F.flip.obj X ≅ 𝟭 D` and `X : GradedObject J D`,
this is the isomorphism `((mapBifunctor F J I).obj X).obj ((single₀ I).obj Y) a ≅ Y a.2`
when `a : J × I` is such that `a.2 = 0`. -/
@[simps!]
noncomputable def mapBifunctorObjObjSingle₀Iso (a : J × I) (ha : a.2 = 0) :
    ((mapBifunctor F J I).obj X).obj ((single₀ I).obj Y) a ≅ X a.1 :=
  Functor.mapIso _ (singleObjApplyIsoOfEq _ Y _ ha) ≪≫ e.app (X a.1)

/-- Given `F : D ⥤ C ⥤ D`, `Y : C` and `X : GradedObject J D`,
`((mapBifunctor F J I).obj X).obj ((single₀ I).obj X) a` is an initial when `a : J × I`
is such that `a.2 ≠ 0`. -/
noncomputable def mapBifunctorObjObjSingle₀IsInitial (a : J × I) (ha : a.2 ≠ 0) :
    IsInitial (((mapBifunctor F J I).obj X).obj ((single₀ I).obj Y) a) :=
  IsInitial.isInitialObj (F.obj (X a.1)) _ (isInitialSingleObjApply _ _ _ ha)

/-- Given `F : D ⥤ C ⥤ D`, `Y : C`, `e : F.flip.obj Y ≅ 𝟭 D`, `X : GradedObject J D` and
`p : J × I → J` such that `p ⟨j, 0⟩ = j` for all `j`,
this is the (colimit) cofan which shall be used to construct the isomorphism
`mapBifunctorMapObj F p X ((single₀ I).obj Y) ≅ X`, see `mapBifunctorRightUnitor`. -/
noncomputable def mapBifunctorRightUnitorCofan (j : J) :
    (((mapBifunctor F J I).obj X).obj ((single₀ I).obj Y)).CofanMapObjFun p j :=
  CofanMapObjFun.mk _ _ _ (X j) (fun a ha =>
    if ha : a.2 = 0 then
      (mapBifunctorObjObjSingle₀Iso F Y e X a ha).hom ≫ eqToHom (by aesop)
    else
      (mapBifunctorObjObjSingle₀IsInitial F Y X a ha).to _)

@[simp, reassoc]
lemma mapBifunctorRightUnitorCofan_inj (j : J) :
    (mapBifunctorRightUnitorCofan F Y e p hp X j).inj ⟨⟨j, 0⟩, hp j⟩ =
      (F.obj (X j)).map (singleObjApplyIso (0 : I) Y).hom ≫ e.hom.app (X j) := by
  simp [mapBifunctorRightUnitorCofan]

/-- The cofan `mapBifunctorRightUnitorCofan F Y e p hp X j` is a colimit. -/
noncomputable def mapBifunctorRightUnitorCofanIsColimit (j : J) :
    IsColimit (mapBifunctorRightUnitorCofan F Y e p hp X j) :=
  mkCofanColimit _
    (fun s => e.inv.app (X j) ≫
      (F.obj (X j)).map (singleObjApplyIso (0 : I) Y).inv ≫ s.inj ⟨⟨j, 0⟩, hp j⟩)
    (fun s => by
      rintro ⟨⟨j', i⟩, h⟩
      by_cases hi : i = 0
      · subst hi
        simp only [Set.mem_preimage, hp, Set.mem_singleton_iff] at h
        subst h
        dsimp
        rw [mapBifunctorRightUnitorCofan_inj, assoc, Iso.hom_inv_id_app_assoc,
          ← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id, id_comp]
      · apply IsInitial.hom_ext
        exact mapBifunctorObjObjSingle₀IsInitial _ _ _ _ hi)
    (fun s m hm => by
      dsimp
      rw [← hm ⟨⟨j, 0⟩, hp j⟩, mapBifunctorRightUnitorCofan_inj, assoc, ← Functor.map_comp_assoc,
        Iso.inv_hom_id, Functor.map_id, id_comp, Iso.inv_hom_id_app_assoc])

lemma mapBifunctorRightUnitor_hasMap :
    HasMap (((mapBifunctor F J I).obj X).obj ((single₀ I).obj Y)) p :=
  CofanMapObjFun.hasMap _ _ _ (mapBifunctorRightUnitorCofanIsColimit F Y e p hp X)

variable [HasMap (((mapBifunctor F J I).obj X).obj ((single₀ I).obj Y)) p]
  [HasMap (((mapBifunctor F J I).obj X').obj ((single₀ I).obj Y)) p]

/-- Given `F : D ⥤ C ⥤ D`, `Y : C`, `e : F.flip.obj Y ≅ 𝟭 D`, `X : GradedObject J D` and
`p : J × I → J` such that `p ⟨j, 0⟩ = j` for all `j`,
this is the right unitor isomorphism `mapBifunctorMapObj F p X ((single₀ I).obj Y) ≅ X`. -/
noncomputable def mapBifunctorRightUnitor : mapBifunctorMapObj F p X ((single₀ I).obj Y) ≅ X :=
  isoMk _ _ (fun j => (CofanMapObjFun.iso
    (mapBifunctorRightUnitorCofanIsColimit F Y e p hp X j)).symm)

@[reassoc (attr := simp)]
lemma ι_mapBifunctorRightUnitor_hom_apply (j : J) :
    ιMapBifunctorMapObj F p X ((single₀ I).obj Y) j 0 j (hp j) ≫
        (mapBifunctorRightUnitor F Y e p hp X).hom j =
      (F.obj (X j)).map (singleObjApplyIso (0 : I) Y).hom ≫ e.hom.app (X j) := by
  dsimp [mapBifunctorRightUnitor]
  erw [CofanMapObjFun.ιMapObj_iso_inv]
  rw [mapBifunctorRightUnitorCofan_inj]

lemma mapBifunctorRightUnitor_inv_apply (j : J) :
    (mapBifunctorRightUnitor F Y e p hp X).inv j =
      e.inv.app (X j) ≫ (F.obj (X j)).map (singleObjApplyIso (0 : I) Y).inv ≫
        ιMapBifunctorMapObj F p X ((single₀ I).obj Y) j 0 j (hp j) := rfl

variable {Y Y'}

@[reassoc]
lemma mapBifunctorRightUnitor_inv_naturality :
    φ ≫ (mapBifunctorRightUnitor F Y e p hp X').inv =
      (mapBifunctorRightUnitor F Y e p hp X).inv ≫ mapBifunctorMapMap F p φ (𝟙 _):= by
  ext j
  dsimp
  rw [mapBifunctorRightUnitor_inv_apply, mapBifunctorRightUnitor_inv_apply, assoc, assoc,
    ι_mapBifunctorMapMap]
  dsimp
  rw [Functor.map_id, id_comp, NatTrans.naturality_assoc]
  erw [← NatTrans.naturality_assoc]
  rfl

@[reassoc]
lemma mapBifunctorRightUnitor_naturality :
    mapBifunctorMapMap F p φ (𝟙 _) ≫ (mapBifunctorRightUnitor F Y e p hp X').hom =
      (mapBifunctorRightUnitor F Y e p hp X).hom ≫ φ := by
  rw [← cancel_mono (mapBifunctorRightUnitor F Y e p hp X').inv, assoc, assoc, Iso.hom_inv_id,
    comp_id, mapBifunctorRightUnitor_inv_naturality, Iso.hom_inv_id_assoc]

end RightUnitor

end GradedObject

end CategoryTheory
