import Mathlib.CategoryTheory.GradedObject.Bifunctor

namespace CategoryTheory

variable {C₁ C₂ C₁₂ C₃ C₄ : Type*}
  [Category C₁] [Category C₂] [Category C₃] [Category C₄] [Category C₁₂]
  (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄)

namespace GradedObject

@[simps]
def mapTrifunctorFunctorObj {I₁ : Type*} (X₁ : GradedObject I₁ C₁) (I₂ I₃ : Type*) :
    GradedObject I₂ C₂ ⥤ GradedObject I₃ C₃ ⥤ GradedObject (I₁ × I₂ × I₃) C₄ where
  obj X₂ :=
    { obj := fun X₃ x => ((F.obj (X₁ x.1)).obj (X₂ x.2.1)).obj (X₃ x.2.2)
      map := fun {X₃ Y₃} φ x => ((F.obj (X₁ x.1)).obj (X₂ x.2.1)).map (φ x.2.2) }
  map {X₂ Y₂} φ :=
    { app := fun X₃ x => ((F.obj (X₁ x.1)).map (φ x.2.1)).app (X₃ x.2.2) }

@[simps]
def mapTrifunctorFunctor (I₁ I₂ I₃ : Type*) :
    GradedObject I₁ C₁ ⥤ GradedObject I₂ C₂ ⥤ GradedObject I₃ C₃ ⥤ GradedObject (I₁ × I₂ × I₃) C₄ where
  obj X₁ := mapTrifunctorFunctorObj F X₁ I₂ I₃
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

variable {I₁ I₂ I₃ J : Type*} (p : I₁ × I₂ × I₃ → J)

@[simp]
noncomputable def mapTrifunctorMapObj (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂)
    (X₃ : GradedObject I₃ C₃)
    [HasMap ((((mapTrifunctorFunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) p] :
    GradedObject J C₄ :=
  ((((mapTrifunctorFunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃).mapObj p

@[simp]
noncomputable def mapTrifunctorMapMap {X₁ Y₁ : GradedObject I₁ C₁} (f₁ : X₁ ⟶ Y₁)
    {X₂ Y₂ : GradedObject I₂ C₂} (f₂ : X₂ ⟶ Y₂)
    {X₃ Y₃ : GradedObject I₃ C₃} (f₃ : X₃ ⟶ Y₃)
    [HasMap ((((mapTrifunctorFunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) p]
    [HasMap ((((mapTrifunctorFunctor F I₁ I₂ I₃).obj Y₁).obj Y₂).obj Y₃) p] :
    mapTrifunctorMapObj F p X₁ X₂ X₃ ⟶ mapTrifunctorMapObj F p Y₁ Y₂ Y₃ :=
  GradedObject.mapMap ((((mapTrifunctorFunctor F I₁ I₂ I₃).map f₁).app X₂).app X₃ ≫
    (((mapTrifunctorFunctor F I₁ I₂ I₃).obj Y₁).map f₂).app X₃ ≫
    (((mapTrifunctorFunctor F I₁ I₂ I₃).obj Y₁).obj Y₂).map f₃) p


instance (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂) (X₃ : GradedObject I₃ C₃)
  [h : HasMap ((((mapTrifunctorFunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) p] :
      HasMap (((mapTrifunctorFunctorObj F X₁ I₂ I₃).obj X₂).obj X₃) p := h

set_option maxHeartbeats 400000 in
@[simps]
noncomputable def mapTrifunctorMapFunctorObj (X₁ : GradedObject I₁ C₁)
    [∀ X₂ X₃, HasMap ((((mapTrifunctorFunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) p] :
    GradedObject I₂ C₂ ⥤ GradedObject I₃ C₃ ⥤ GradedObject J C₄ where
  obj X₂ :=
    { obj := fun X₃ => mapTrifunctorMapObj F p X₁ X₂ X₃
      map := fun {X₃ Y₃} φ => mapTrifunctorMapMap F p (𝟙 X₁) (𝟙 X₂) φ }
  map {X₂ Y₂} φ :=
    { app := fun X₃ => mapTrifunctorMapMap F p (𝟙 X₁) φ (𝟙 X₃)
      naturality := fun {X₃ Y₃} φ => by
        dsimp
        simp only [Functor.map_id, mapTrifunctorFunctor_obj, NatTrans.id_app,
          Category.id_comp, Category.comp_id, ← mapMap_comp]
        apply congr_mapMap
        simp }

set_option maxHeartbeats 400000 in
@[simps]
noncomputable def mapTrifunctorMapFunctor
    [∀ X₁ X₂ X₃, HasMap ((((mapTrifunctorFunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) p] :
    GradedObject I₁ C₁ ⥤ GradedObject I₂ C₂ ⥤ GradedObject I₃ C₃ ⥤ GradedObject J C₄ where
  obj X₁ := mapTrifunctorMapFunctorObj F p X₁
  map := fun {X₁ Y₁} φ =>
    { app := fun X₂ =>
        { app := fun X₃ => mapTrifunctorMapMap F p φ (𝟙 X₂) (𝟙 X₃)
          naturality := fun {X₃ Y₃} φ => by
            dsimp [mapTrifunctorMapFunctorObj]
            simp only [Functor.map_id, mapTrifunctorFunctor_obj, NatTrans.id_app,
              Category.id_comp, Category.comp_id, ← mapMap_comp]
            apply congr_mapMap
            simp }
      naturality := fun {X₂ Y₂} φ => by
        ext X₃ : 2
        dsimp [mapTrifunctorMapFunctorObj]
        simp only [Functor.map_id, mapTrifunctorFunctor_obj, NatTrans.id_app,
          Category.comp_id, Category.id_comp, ← mapMap_comp]
        apply congr_mapMap
        simp only [← NatTrans.comp_app]
        congr 1
        simp }

end

section

variable (F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂) (G : C₁₂ ⥤ C₃ ⥤ C₄)

@[simps]
def bifunctorComp₁₂Obj (X₁ : C₁) : C₂ ⥤ C₃ ⥤ C₄ where
  obj X₂ :=
    { obj := fun X₃ => (G.obj ((F₁₂.obj X₁).obj X₂)).obj X₃
      map := fun {X₃ Y₃} φ => (G.obj ((F₁₂.obj X₁).obj X₂)).map φ }
  map {X₂ Y₂} φ :=
    { app := fun X₃ => (G.map ((F₁₂.obj X₁).map φ)).app X₃ }

@[simps]
def bifunctorComp₁₂ : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ where
  obj X₁ := bifunctorComp₁₂Obj F₁₂ G X₁
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

noncomputable def mapBifunctor₁₂BifunctorMapObj (X₁ : GradedObject I₁ C₁)
    (X₂ : GradedObject I₂ C₂) (X₃ : GradedObject I₃ C₃)
    [HasMap (((mapBifunctorFunctor F₁₂ I₁ I₂).obj X₁).obj X₂) p]
    [HasMap (((mapBifunctorFunctor G I₁₂ I₃).obj (mapBifunctorMapObj F₁₂ p X₁ X₂)).obj X₃) q] :
    GradedObject J C₄ :=
  mapBifunctorMapObj G q (mapBifunctorMapObj F₁₂ p X₁ X₂) X₃

section

variable (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂) (X₃ : GradedObject I₃ C₃)
  [HasMap (((mapBifunctorFunctor F₁₂ I₁ I₂).obj X₁).obj X₂) p]
  [HasMap (((mapBifunctorFunctor G I₁₂ I₃).obj (mapBifunctorMapObj F₁₂ p X₁ X₂)).obj X₃) q]
  [HasMap ((((mapTrifunctorFunctor (bifunctorComp₁₂ F₁₂ G) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) r]
  [HasMap ((((mapTrifunctorFunctor (bifunctorComp₁₂ F₁₂ G) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) (p' I₃ p)]
  [HasMap (((((mapTrifunctorFunctor (bifunctorComp₁₂ F₁₂ G) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃).mapObj (p' I₃ p)) q]
  [HasMap ((comap _ (π₁₂_₃ I₁ I₂ I₃)).obj (((mapBifunctorFunctor F₁₂ I₁ I₂).obj X₁).obj X₂)) (p' I₃ p)]
  [PreservesMap (γ G I₁₂ X₃) (p' I₃ p) ((comap _ (π₁₂_₃ I₁ I₂ I₃)).obj (((mapBifunctorFunctor F₁₂ I₁ I₂).obj X₁).obj X₂))]

attribute [local ext] mapObj_ext

noncomputable def mapBifunctor₁₂BifunctorMapObjIso₁ :
    (((((mapTrifunctorFunctor (bifunctorComp₁₂ F₁₂ G) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃).mapObj (p' I₃ p)).mapObj q ≅
      mapTrifunctorMapObj (bifunctorComp₁₂ F₁₂ G) r X₁ X₂ X₃ :=
  ((((mapTrifunctorFunctor (bifunctorComp₁₂ F₁₂ G) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃).mapObjMapObjIso (p' I₃ p) q r hr

noncomputable def mapBifunctor₁₂BifunctorMapObjIso₂ :
    ((((mapTrifunctorFunctor
      (bifunctorComp₁₂ F₁₂ G) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃).mapObj (p' I₃ p) ≅
    (applyFunctorsObj (γ G I₁₂ X₃)).obj
      (((comap _ (π₁₂_₃ I₁ I₂ I₃)).obj (((mapBifunctorFunctor F₁₂ I₁ I₂).obj X₁).obj X₂)).mapObj (p' I₃ p)) :=
  (comapObjApplyFunctorsObjObjMapObjIso (γ G I₁₂ X₃) (p' I₃ p) ((comap _ (π₁₂_₃ I₁ I₂ I₃)).obj (((mapBifunctorFunctor F₁₂ I₁ I₂).obj X₁).obj X₂)))

noncomputable def mapBifunctor₁₂BifunctorMapObjIso₃ :
    ((mapBifunctorFunctor G I₁₂ I₃).obj (mapBifunctorMapObj F₁₂ p X₁ X₂)).obj X₃ ≅
    (applyFunctorsObj (γ G I₁₂ X₃)).obj
      (((comap _ (π₁₂_₃ I₁ I₂ I₃)).obj (((mapBifunctorFunctor F₁₂ I₁ I₂).obj X₁).obj X₂)).mapObj (p' I₃ p)) :=
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
    mapTrifunctorMapObj (bifunctorComp₁₂ F₁₂ G) r X₁ X₂ X₃ ≅
    mapBifunctor₁₂BifunctorMapObj F₁₂ G p q X₁ X₂ X₃ :=
  (mapBifunctor₁₂BifunctorMapObjIso₁ F₁₂ G p q r hr X₁ X₂ X₃).symm ≪≫
    mapIso ((mapBifunctor₁₂BifunctorMapObjIso₂ F₁₂ G p X₁ X₂ X₃) ≪≫
      (mapBifunctor₁₂BifunctorMapObjIso₃ F₁₂ G p X₁ X₂ X₃).symm) q

end

end

end GradedObject

end CategoryTheory
