import Mathlib.CategoryTheory.GradedObject.Bifunctor

namespace CategoryTheory

variable {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
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

end GradedObject

end CategoryTheory
