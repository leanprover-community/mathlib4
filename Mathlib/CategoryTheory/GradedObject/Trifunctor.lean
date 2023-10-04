/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.GradedObject.Bifunctor

namespace CategoryTheory

open Category Limits

variable {C₁ C₂ C₁₂ C₂₃ C₃ C₄ : Type*}
  [Category C₁] [Category C₂] [Category C₃] [Category C₄] [Category C₁₂] [Category C₂₃]
  (F F' : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄) (α : F ⟶ F') (e : F ≅ F')

namespace GradedObject

@[simps]
def mapTrifunctorObj {I₁ : Type*} (X₁ : GradedObject I₁ C₁) (I₂ I₃ : Type*) :
    GradedObject I₂ C₂ ⥤ GradedObject I₃ C₃ ⥤ GradedObject (I₁ × I₂ × I₃) C₄ where
  obj X₂ :=
    { obj := fun X₃ x => ((F.obj (X₁ x.1)).obj (X₂ x.2.1)).obj (X₃ x.2.2)
      map := fun {X₃ Y₃} φ x => ((F.obj (X₁ x.1)).obj (X₂ x.2.1)).map (φ x.2.2) }
  map {X₂ Y₂} φ :=
    { app := fun X₃ x => ((F.obj (X₁ x.1)).map (φ x.2.1)).app (X₃ x.2.2) }

@[simps]
def mapTrifunctor (I₁ I₂ I₃ : Type*) :
    GradedObject I₁ C₁ ⥤ GradedObject I₂ C₂ ⥤ GradedObject I₃ C₃ ⥤ GradedObject (I₁ × I₂ × I₃) C₄ where
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

@[simps]
def mapTrifunctorMapNatTrans (I₁ I₂ I₃ : Type*) :
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

@[simps]
def mapTrifunctorMapIso (I₁ I₂ I₃ : Type*) :
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

@[simp]
noncomputable def mapTrifunctorMapObj (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂)
    (X₃ : GradedObject I₃ C₃)
    [HasMap ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) p] :
    GradedObject J C₄ :=
  ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃).mapObj p

--abbrev mapTrifunctorMapObjFun (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂)
--  (X₃ : GradedObject I₃ C₃) (j : J) : p ⁻¹' {j}  → C₄ :=
--    (fun (⟨⟨i₁, i₂, i₃⟩, _⟩) => ((F.obj (X₁ i₁)).obj (X₂ i₂)).obj (X₃ i₃))

noncomputable def ιMapTrifunctorMapObj (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂)
    (X₃ : GradedObject I₃ C₃) (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J) (h : p ⟨i₁, i₂, i₃⟩ = j)
    [HasMap ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) p] :
    ((F.obj (X₁ i₁)).obj (X₂ i₂)).obj (X₃ i₃) ⟶ mapTrifunctorMapObj F p X₁ X₂ X₃ j :=
  ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃).ιMapObj p ⟨i₁, i₂, i₃⟩ j h

@[ext]
lemma mapTrifunctorMapObj_ext {X₁ : GradedObject I₁ C₁} {X₂ : GradedObject I₂ C₂}
    {X₃ : GradedObject I₃ C₃} {j : J} {A : C₄}
    [HasMap ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) p]
    (f g : mapTrifunctorMapObj F p X₁ X₂ X₃ j ⟶ A)
    (h : ∀ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (h : p ⟨i₁, i₂, i₃⟩ = j),
      ιMapTrifunctorMapObj F p X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ f =
        ιMapTrifunctorMapObj F p X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ g) : f = g := by
  apply mapObj_ext
  rintro ⟨i₁, i₂, i₃⟩ hi
  exact h _ _ _ hi

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
  {I₁ I₂ I₃ J : Type*}
    (r : I₁ × I₂ × I₃ → J)

structure Bifunctor₁₂BifunctorIndexData :=
  I₁₂ : Type*
  p : I₁ × I₂ → I₁₂
  q : I₁₂ × I₃ → J
  hpq : ∀ (i : I₁ × I₂ × I₃), r i = q ⟨p ⟨i.1, i.2.1⟩, i.2.2⟩

variable (ρ₁₂ : Bifunctor₁₂BifunctorIndexData r)

section

variable {r}

variable (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂) (X₃ : GradedObject I₃ C₃)
  [HasMap (((mapBifunctor F₁₂ I₁ I₂).obj X₁).obj X₂) ρ₁₂.p]
  [HasMap (((mapBifunctor G ρ₁₂.I₁₂ I₃).obj (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂)).obj X₃) ρ₁₂.q]

abbrev HasGoodBifunctor₁₂BifunctorObj :=
  ∀ (i₁₂ : ρ₁₂.I₁₂) (i₃ : I₃), (PreservesColimit (Discrete.functor (mapObjFun (((mapBifunctor F₁₂ I₁ I₂).obj X₁).obj X₂) ρ₁₂.p i₁₂))
    ((Functor.flip G).obj (X₃ i₃)))

noncomputable def ιMapBifunctor₁₂BifunctorMapObj (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J) (h : r (i₁, i₂, i₃) = j) :
    (G.obj ((F₁₂.obj (X₁ i₁)).obj (X₂ i₂))).obj (X₃ i₃) ⟶
      mapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ j :=
  (G.map (ιMapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂ i₁ i₂ _ rfl)).app (X₃ i₃) ≫
    ιMapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ (ρ₁₂.p ⟨i₁, i₂⟩) i₃ j (by rw [← h, ρ₁₂.hpq])

@[reassoc]
noncomputable def ιMapBifunctor₁₂BifunctorMapObj_eq (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J) (h : r (i₁, i₂, i₃) = j) (i₁₂ : ρ₁₂.I₁₂) (h' : ρ₁₂.p ⟨i₁, i₂⟩ = i₁₂) :
  ιMapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j h =
  (G.map (ιMapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂ i₁ i₂ i₁₂ h')).app (X₃ i₃) ≫
    ιMapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ i₁₂ i₃ j (by rw [← h, ← h', ρ₁₂.hpq]) := by
  subst h'
  rfl

noncomputable def ιMapBifunctor₁₂BifunctorMapObjOrZero [HasZeroMorphisms C₄] (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J) [DecidableEq J] :
    (G.obj ((F₁₂.obj (X₁ i₁)).obj (X₂ i₂))).obj (X₃ i₃) ⟶
      mapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ j :=
  if h : r (i₁, i₂, i₃) = j
    then ιMapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j h
    else 0

noncomputable def ιMapBifunctor₁₂BifunctorMapObjOrZero_eq [HasZeroMorphisms C₄] (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J) [DecidableEq J]
    (h : r (i₁, i₂, i₃) = j) :
    ιMapBifunctor₁₂BifunctorMapObjOrZero F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j =
      ιMapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j h := dif_pos h

noncomputable def ιMapBifunctor₁₂BifunctorMapObjOrZero_eq_zero [HasZeroMorphisms C₄] (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J) [DecidableEq J]
    (h : r (i₁, i₂, i₃) ≠ j) :
    ιMapBifunctor₁₂BifunctorMapObjOrZero F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j = 0 := dif_neg h

variable [H : HasGoodBifunctor₁₂BifunctorObj F₁₂ G ρ₁₂ X₁ X₂ X₃]

noncomputable def cofan₃MapBifunctor₁₂BifunctorMapObj (j : J) :
    ((((mapTrifunctor (bifunctorComp₁₂ F₁₂ G) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃).CofanMapObjFun r j :=
  Cofan.mk (mapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ j)
    (fun ⟨⟨i₁, i₂, i₃⟩, (hi : r ⟨i₁, i₂, i₃⟩ = j)⟩ =>
      ιMapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j hi)

noncomputable def isColimitCofan₃MapBifunctor₁₂BifunctorMapObj (j : J) :
    IsColimit (cofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j) := by
  let c₁₂ := fun i₁₂ => (((mapBifunctor F₁₂ I₁ I₂).obj X₁).obj X₂).cofanMapObj ρ₁₂.p i₁₂
  have h₁₂ : ∀ i₁₂, IsColimit (c₁₂ i₁₂) := fun i₁₂ => (((mapBifunctor F₁₂ I₁ I₂).obj X₁).obj X₂).isColimitCofanMapObj ρ₁₂.p i₁₂
  let c := (((mapBifunctor G ρ₁₂.I₁₂ I₃).obj (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂)).obj X₃).cofanMapObj ρ₁₂.q j
  have hc : IsColimit c := (((mapBifunctor G ρ₁₂.I₁₂ I₃).obj (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂)).obj X₃).isColimitCofanMapObj ρ₁₂.q j
  let c₁₂' := fun (i : ρ₁₂.q ⁻¹' {j}) => (G.flip.obj (X₃ i.1.2)).mapCocone (c₁₂ i.1.1)
  have hc₁₂' : ∀ i, IsColimit (c₁₂' i) := fun i => isColimitOfPreserves _ (h₁₂ i.1.1)
  let Z := (((mapTrifunctor (bifunctorComp₁₂ F₁₂ G) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃
  let p' : I₁ × I₂ × I₃ → ρ₁₂.I₁₂ × I₃ := fun ⟨i₁, i₂, i₃⟩ => ⟨ρ₁₂.p ⟨i₁, i₂⟩, i₃⟩
  let e : ∀ (i₁₂ : ρ₁₂.I₁₂) (i₃ : I₃), p' ⁻¹' {(i₁₂, i₃)} ≃ ρ₁₂.p ⁻¹' {i₁₂} := fun i₁₂ i₃ =>
    { toFun := fun ⟨⟨i₁, i₂, i₃'⟩, hi⟩ => ⟨⟨i₁, i₂⟩, by aesop⟩
      invFun := fun ⟨⟨i₁, i₂⟩, hi⟩ => ⟨⟨i₁, i₂, i₃⟩, by aesop⟩
      left_inv := fun ⟨⟨i₁, i₂, i₃'⟩, hi⟩ => by
        obtain rfl : i₃ = i₃' := by aesop
        rfl
      right_inv := fun _ => rfl }
  let c₁₂'' : ∀ (i : ρ₁₂.q ⁻¹' {j}), CofanMapObjFun Z p' (i.1.1, i.1.2) := fun ⟨⟨i₁₂, i₃⟩, hi⟩ => by
    refine' (Cocones.precompose (Iso.hom _)).obj ((Cocones.whiskeringEquivalence (Discrete.equivalence (e i₁₂ i₃))).functor.obj (c₁₂' ⟨⟨i₁₂, i₃⟩, hi⟩))
    refine' (Discrete.natIso (fun ⟨⟨i₁, i₂, i₃'⟩, hi⟩ => (G.obj ((F₁₂.obj (X₁ i₁)).obj (X₂ i₂))).mapIso (eqToIso _)))
    obtain rfl : i₃' = i₃ := congr_arg _root_.Prod.snd hi
    rfl
  have h₁₂'' : ∀ i, IsColimit (c₁₂'' i) := fun _ =>
    (IsColimit.precomposeHomEquiv _ _).symm (IsColimit.whiskerEquivalenceEquiv _ (hc₁₂' _))
  refine' IsColimit.ofIsoColimit (isColimitCofanMapObjComp Z p' ρ₁₂.q r ρ₁₂.hpq j
    (fun ⟨i₁₂, i₃⟩ h => c₁₂'' ⟨⟨i₁₂, i₃⟩, h⟩) (fun ⟨i₁₂, i₃⟩ h => h₁₂'' ⟨⟨i₁₂, i₃⟩, h⟩) c hc)
    (Cocones.ext (Iso.refl _) (fun ⟨⟨i₁, i₂, i₃⟩, h⟩ => _))
  dsimp [Cofan.inj]
  rw [comp_id, Functor.map_id, id_comp]
  rfl

variable {F₁₂ G ρ₁₂ X₁ X₂ X₃}

lemma HasGoodBifunctor₁₂BifunctorObj.hasMap : HasMap ((((mapTrifunctor (bifunctorComp₁₂ F₁₂ G) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) r :=
  fun j => ⟨_, isColimitCofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j⟩

variable (F₁₂ G ρ₁₂ X₁ X₂ X₃)

noncomputable def mapBifunctor₁₂BifunctorMapObjIso
    [HasMap ((((mapTrifunctor (bifunctorComp₁₂ F₁₂ G) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) r] :
    mapTrifunctorMapObj (bifunctorComp₁₂ F₁₂ G) r X₁ X₂ X₃ ≅
    mapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ :=
  isoMk _ _ (fun j => (CofanMapObjFun.iso (isColimitCofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j)).symm)

@[reassoc (attr := simp, nolint unusedHavesSuffices)]
lemma ι_mapBifunctor₁₂BifunctorMapObjIso_hom (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J) (h : r ⟨i₁, i₂, i₃⟩ = j) :
    have := H.hasMap
    ιMapTrifunctorMapObj (bifunctorComp₁₂ F₁₂ G) r X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ (mapBifunctor₁₂BifunctorMapObjIso F₁₂ G ρ₁₂ X₁ X₂ X₃).hom j =
      ιMapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j (by rw [← h, ρ₁₂.hpq]) := by
  have := H.hasMap
  dsimp [mapBifunctor₁₂BifunctorMapObjIso]
  apply CofanMapObjFun.ιMapObj_iso_inv

variable {X₁ X₂ X₃}

@[ext]
lemma mapBifunctor₁₂BifunctorMapObj_ext {j : J} {A : C₄}
    (f g : mapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ j ⟶ A)
    (h : ∀ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (h : r ⟨i₁, i₂, i₃⟩ = j),
      ιMapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ f =
        ιMapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ g) : f = g := by
  apply Cofan.IsColimit.hom_ext (isColimitCofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j)
  rintro ⟨i, hi⟩
  exact h _ _ _ hi

variable (X₁ X₂ X₃)

@[reassoc (attr := simp)]
lemma ι_mapBifunctor₁₂BifunctorMapObjIso_inv (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J) (h : r ⟨i₁, i₂, i₃⟩ = j) :
    have := H.hasMap
    ιMapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫
      (mapBifunctor₁₂BifunctorMapObjIso F₁₂ G ρ₁₂ X₁ X₂ X₃).inv j =
    ιMapTrifunctorMapObj (bifunctorComp₁₂ F₁₂ G) r X₁ X₂ X₃ i₁ i₂ i₃ j h := by
  have := H.hasMap
  dsimp only
  rw [← cancel_mono ((mapBifunctor₁₂BifunctorMapObjIso F₁₂ G ρ₁₂ X₁ X₂ X₃).hom j), assoc,
    iso_inv_hom_id_apply, comp_id, ι_mapBifunctor₁₂BifunctorMapObjIso_hom]

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

variable {I₁ I₂ I₃ J : Type*} (r : I₁ × I₂ × I₃ → J)

structure BifunctorBifunctor₂₃IndexData :=
  I₂₃ : Type*
  p : I₂ × I₃ → I₂₃
  q : I₁ × I₂₃ → J
  hpq : ∀ (i : I₁ × I₂ × I₃), r i = q ⟨i.1, p i.2⟩

variable {r} (ρ₂₃ : BifunctorBifunctor₂₃IndexData r)

section

variable (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂) (X₃ : GradedObject I₃ C₃)
  [HasMap (((mapBifunctor G₂₃ I₂ I₃).obj X₂).obj X₃) ρ₂₃.p]
  [HasMap (((mapBifunctor F I₁ ρ₂₃.I₂₃).obj X₁).obj (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃)) ρ₂₃.q]

abbrev HasGoodBifunctorBifunctor₂₃Obj :=
  ∀ (i₁ : I₁) (i₂₃ : ρ₂₃.I₂₃), PreservesColimit (Discrete.functor (mapObjFun (((mapBifunctor G₂₃ I₂ I₃).obj X₂).obj X₃) ρ₂₃.p i₂₃))
    (F.obj (X₁ i₁))

noncomputable def ιMapBifunctorBifunctor₂₃MapObj (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J) (h : r (i₁, i₂, i₃) = j) :
    (F.obj (X₁ i₁)).obj ((G₂₃.obj (X₂ i₂)).obj (X₃ i₃)) ⟶ mapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) j :=
  (F.obj (X₁ i₁)).map (ιMapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃ i₂ i₃ _ rfl) ≫
    ιMapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) i₁ (ρ₂₃.p ⟨i₂, i₃⟩) j (by rw [← h, ρ₂₃.hpq])

@[reassoc]
noncomputable def ιMapBifunctorBifunctor₂₃MapObj_eq (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J) (h : r (i₁, i₂, i₃) = j) (i₂₃ : ρ₂₃.I₂₃) (h' : ρ₂₃.p ⟨i₂, i₃⟩ = i₂₃) :
    ιMapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h =
    (F.obj (X₁ i₁)).map (ιMapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃ i₂ i₃ i₂₃ h') ≫
    ιMapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) i₁ i₂₃ j (by rw [← h, ρ₂₃.hpq, h']) := by
  subst h'
  rfl

noncomputable def ιMapBifunctorBifunctor₂₃MapObjOrZero [HasZeroMorphisms C₄] (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J) [DecidableEq J] :
    (F.obj (X₁ i₁)).obj ((G₂₃.obj (X₂ i₂)).obj (X₃ i₃)) ⟶ mapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) j :=
  if h : r (i₁, i₂, i₃) = j
    then ιMapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h
    else 0

noncomputable def ιMapBifunctorBifunctor₂₃MapObjOrZero_eq [HasZeroMorphisms C₄] (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J) [DecidableEq J]
    (h : r (i₁, i₂, i₃) = j) :
    ιMapBifunctorBifunctor₂₃MapObjOrZero F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j =
      ιMapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h := dif_pos h

noncomputable def ιMapBifunctorBifunctor₂₃MapObjOrZero_eq_zero [HasZeroMorphisms C₄] (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J) [DecidableEq J]
    (h : r (i₁, i₂, i₃) ≠ j) :
    ιMapBifunctorBifunctor₂₃MapObjOrZero F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j = 0 := dif_neg h

variable [H : HasGoodBifunctorBifunctor₂₃Obj F G₂₃ ρ₂₃ X₁ X₂ X₃]

noncomputable def cofan₃MapBifunctorBifunctor₂₃MapObj (j : J) :
    ((((mapTrifunctor (bifunctorComp₂₃ F G₂₃) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃).CofanMapObjFun r j :=
  Cofan.mk (mapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) j) (fun ⟨⟨i₁, i₂, i₃⟩, (hi : r ⟨i₁, i₂, i₃⟩ = j)⟩ =>
    ιMapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j hi)

noncomputable def isColimitCofan₃MapBifunctorBifunctor₂₃MapObj (j : J) :
    IsColimit (cofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j) := by
  let c₂₃ := fun i₂₃ => (((mapBifunctor G₂₃ I₂ I₃).obj X₂).obj X₃).cofanMapObj ρ₂₃.p i₂₃
  have h₂₃ : ∀ i₂₃, IsColimit (c₂₃ i₂₃) := fun i₂₃ => (((mapBifunctor G₂₃ I₂ I₃).obj X₂).obj X₃).isColimitCofanMapObj ρ₂₃.p i₂₃
  let c := (((mapBifunctor F I₁ ρ₂₃.I₂₃).obj X₁).obj (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃)).cofanMapObj ρ₂₃.q j
  have hc : IsColimit c := (((mapBifunctor F I₁ ρ₂₃.I₂₃).obj X₁).obj (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃)).isColimitCofanMapObj ρ₂₃.q j
  let c₂₃' := fun (i : ρ₂₃.q ⁻¹' {j}) => (F.obj (X₁ i.1.1)).mapCocone (c₂₃ i.1.2)
  have hc₂₃' : ∀ i, IsColimit (c₂₃' i) := fun i => isColimitOfPreserves _ (h₂₃ i.1.2)
  let Z := (((mapTrifunctor (bifunctorComp₂₃ F G₂₃) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃
  let p' : I₁ × I₂ × I₃ → I₁ × ρ₂₃.I₂₃ := fun ⟨i₁, i₂, i₃⟩ => ⟨i₁, ρ₂₃.p ⟨i₂, i₃⟩⟩
  let e : ∀ (i₁ : I₁) (i₂₃ : ρ₂₃.I₂₃) , p' ⁻¹' {(i₁, i₂₃)} ≃ ρ₂₃.p ⁻¹' {i₂₃} := fun i₁ i₂₃ =>
    { toFun := fun ⟨⟨i₁', i₂, i₃⟩, hi⟩ => ⟨⟨i₂, i₃⟩, by aesop⟩
      invFun := fun ⟨⟨i₂, i₃⟩, hi⟩  => ⟨⟨i₁, i₂, i₃⟩, by aesop⟩
      left_inv := fun ⟨⟨i₁', i₂, i₃⟩, hi⟩ => by
        obtain rfl : i₁ = i₁' := by aesop
        rfl
      right_inv := fun _ => rfl }
  let c₂₃'' : ∀ (i : ρ₂₃.q ⁻¹' {j}), CofanMapObjFun Z p' (i.1.1, i.1.2) := fun ⟨⟨i₁, i₂₃⟩, hi⟩ => by
    refine' (Cocones.precompose (Iso.hom _)).obj ((Cocones.whiskeringEquivalence (Discrete.equivalence (e i₁ i₂₃))).functor.obj (c₂₃' ⟨⟨i₁, i₂₃⟩, hi⟩))
    refine' Discrete.natIso (fun ⟨⟨i₁', i₂, i₃⟩, hi⟩ => eqToIso _)
    obtain rfl : i₁' = i₁ := congr_arg _root_.Prod.fst hi
    rfl
  have h₂₃'' : ∀ i, IsColimit (c₂₃'' i) := fun _ =>
    (IsColimit.precomposeHomEquiv _ _).symm (IsColimit.whiskerEquivalenceEquiv _ (hc₂₃' _))
  refine' IsColimit.ofIsoColimit (isColimitCofanMapObjComp Z p' ρ₂₃.q r ρ₂₃.hpq j
    (fun ⟨i₁, i₂₃⟩ h => c₂₃'' ⟨⟨i₁, i₂₃⟩, h⟩) (fun ⟨i₁, i₂₃⟩ h => h₂₃'' ⟨⟨i₁, i₂₃⟩, h⟩) c hc)
    (Cocones.ext (Iso.refl _) (fun ⟨⟨i₁, i₂, i₃⟩, h⟩ => _))
  dsimp [Cofan.inj]
  rw [comp_id, id_comp]
  rfl

variable {F G₂₃ ρ₂₃ X₁ X₂ X₃}

lemma HasGoodBifunctorBifunctor₂₃Obj.hasMap : HasMap ((((mapTrifunctor (bifunctorComp₂₃ F G₂₃) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) r :=
  fun j => ⟨_, isColimitCofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j⟩

variable (F G₂₃ ρ₂₃ X₁ X₂ X₃)

noncomputable def mapBifunctorBifunctor₂₃MapObjIso
    [HasMap ((((mapTrifunctor (bifunctorComp₂₃ F G₂₃) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) r] :
    mapTrifunctorMapObj (bifunctorComp₂₃ F G₂₃) r X₁ X₂ X₃ ≅
    mapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) :=
  isoMk _ _ (fun j => (CofanMapObjFun.iso (isColimitCofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j)).symm)

@[reassoc (attr := simp, nolint unusedHavesSuffices)]
lemma ι_mapBifunctorBifunctor₂₃MapObjIso_hom (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J) (h : r ⟨i₁, i₂, i₃⟩ = j) :
    have := H.hasMap
    ιMapTrifunctorMapObj (bifunctorComp₂₃ F G₂₃) r X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ (mapBifunctorBifunctor₂₃MapObjIso F G₂₃ ρ₂₃ X₁ X₂ X₃).hom j =
      ιMapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j (by rw [←h, ρ₂₃.hpq]) := by
  have := H.hasMap
  dsimp [mapBifunctorBifunctor₂₃MapObjIso]
  apply CofanMapObjFun.ιMapObj_iso_inv

variable {X₁ X₂ X₃}

@[ext]
lemma mapBifunctorBifunctor₂₃MapObj_ext {j : J} {A : C₄}
    (f g : mapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) j ⟶ A)
    (h : ∀ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (h : r ⟨i₁, i₂, i₃⟩ = j),
      ιMapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ f =
        ιMapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ g) : f = g := by
  apply Cofan.IsColimit.hom_ext (isColimitCofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j)
  rintro ⟨i, hi⟩
  exact h _ _ _ hi

variable (X₁ X₂ X₃)

@[reassoc (attr := simp)]
lemma ι_mapBifunctorBifunctor₂₃MapObjIso_inv (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J) (h : r ⟨i₁, i₂, i₃⟩ = j) :
  have := H.hasMap
  ιMapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫
    (mapBifunctorBifunctor₂₃MapObjIso F G₂₃ ρ₂₃ X₁ X₂ X₃).inv j =
    ιMapTrifunctorMapObj (bifunctorComp₂₃ F G₂₃) r X₁ X₂ X₃ i₁ i₂ i₃ j h := by
  have := H.hasMap
  dsimp only
  rw [← cancel_mono ((mapBifunctorBifunctor₂₃MapObjIso F G₂₃ ρ₂₃ X₁ X₂ X₃).hom j),
    assoc, ι_mapBifunctorBifunctor₂₃MapObjIso_hom, iso_inv_hom_id_apply, comp_id]

end

end

section

variable
  {F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂} {G : C₁₂ ⥤ C₃ ⥤ C₄}
  {F : C₁ ⥤ C₂₃ ⥤ C₄} {G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃}
  (associator : bifunctorComp₁₂ F₁₂ G ≅ bifunctorComp₂₃ F G₂₃)
  {I₁ I₂ I₃ J : Type*} {r : I₁ × I₂ × I₃ → J}
  (ρ₁₂ : Bifunctor₁₂BifunctorIndexData r)
  (ρ₂₃ : BifunctorBifunctor₂₃IndexData r)
  (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂) (X₃ : GradedObject I₃ C₃)
  [HasMap (((mapBifunctor F₁₂ I₁ I₂).obj X₁).obj X₂) ρ₁₂.p]
  [HasMap (((mapBifunctor G ρ₁₂.I₁₂ I₃).obj (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂)).obj X₃) ρ₁₂.q]
  [HasMap (((mapBifunctor G₂₃ I₂ I₃).obj X₂).obj X₃) ρ₂₃.p]
  [HasMap (((mapBifunctor F I₁ ρ₂₃.I₂₃).obj X₁).obj (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃)) ρ₂₃.q]
  [H₁₂ : HasGoodBifunctor₁₂BifunctorObj F₁₂ G ρ₁₂ X₁ X₂ X₃]
  [H₂₃ : HasGoodBifunctorBifunctor₂₃Obj F G₂₃ ρ₂₃ X₁ X₂ X₃]

noncomputable def mapBifunctorBifunctorAssociator :
    mapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ ≅
      mapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) :=
  have := H₁₂.hasMap
  have := H₂₃.hasMap
  (mapBifunctor₁₂BifunctorMapObjIso F₁₂ G ρ₁₂ X₁ X₂ X₃).symm ≪≫
    mapIso ((((mapTrifunctorMapIso associator I₁ I₂ I₃).app X₁).app X₂).app X₃) r ≪≫
    mapBifunctorBifunctor₂₃MapObjIso F G₂₃ ρ₂₃ X₁ X₂ X₃

@[reassoc (attr := simp, nolint unusedHavesSuffices)]
lemma ι_mapBifunctorBifunctorAssociator_hom (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J) (h : r (i₁, i₂, i₃) = j) :
    ιMapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫
      (mapBifunctorBifunctorAssociator associator ρ₁₂ ρ₂₃ X₁ X₂ X₃).hom j =
        ((associator.hom.app (X₁ i₁)).app (X₂ i₂)).app (X₃ i₃) ≫
          ιMapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h := by
  have := H₁₂.hasMap
  have := H₂₃.hasMap
  dsimp [mapBifunctorBifunctorAssociator]
  rw [ι_mapBifunctor₁₂BifunctorMapObjIso_inv_assoc, ιMapTrifunctorMapObj,
    ι_mapMap_assoc, mapTrifunctorMapNatTrans_app_app_app]
  erw [ι_mapBifunctorBifunctor₂₃MapObjIso_hom]

@[reassoc (attr := simp)]
lemma ι_mapBifunctorBifunctorAssociator_inv (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J) (h : r (i₁, i₂, i₃) = j) :
    ιMapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫
      (mapBifunctorBifunctorAssociator associator ρ₁₂ ρ₂₃ X₁ X₂ X₃).inv j =
    ((associator.inv.app (X₁ i₁)).app (X₂ i₂)).app (X₃ i₃) ≫
      ιMapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j h := by
  rw [← cancel_mono ((mapBifunctorBifunctorAssociator associator ρ₁₂ ρ₂₃ X₁ X₂ X₃).hom j),
    assoc, assoc, iso_inv_hom_id_apply, comp_id, ι_mapBifunctorBifunctorAssociator_hom,
    ← NatTrans.comp_app_assoc, ← NatTrans.comp_app, Iso.inv_hom_id_app,
    NatTrans.id_app, NatTrans.id_app, id_comp]

lemma ιOrZero_mapBifunctorBifunctorAssociator_hom [HasZeroMorphisms C₄] [DecidableEq J] (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J) :
    ιMapBifunctor₁₂BifunctorMapObjOrZero F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j ≫
      (mapBifunctorBifunctorAssociator associator ρ₁₂ ρ₂₃ X₁ X₂ X₃).hom j =
        ((associator.hom.app (X₁ i₁)).app (X₂ i₂)).app (X₃ i₃) ≫
          ιMapBifunctorBifunctor₂₃MapObjOrZero F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j := by
  by_cases r (i₁, i₂, i₃) = j
  · rw [ιMapBifunctor₁₂BifunctorMapObjOrZero_eq _ _ _ _ _ _ _ _ _ _ h,
      ιMapBifunctorBifunctor₂₃MapObjOrZero_eq _ _ _ _ _ _ _ _ _ _ h,
      ι_mapBifunctorBifunctorAssociator_hom]
  · rw [ιMapBifunctor₁₂BifunctorMapObjOrZero_eq_zero _ _ _ _ _ _ _ _ _ _ h,
      ιMapBifunctorBifunctor₂₃MapObjOrZero_eq_zero _ _ _ _ _ _ _ _ _ _ h, zero_comp, comp_zero]

end

end GradedObject

end CategoryTheory
