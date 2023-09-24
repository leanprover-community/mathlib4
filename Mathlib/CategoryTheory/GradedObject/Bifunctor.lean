import Mathlib.CategoryTheory.GradedObject.Map

namespace CategoryTheory

variable {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
  (F : C₁ ⥤ C₂ ⥤ C₃)

namespace GradedObject

@[simps]
def mapBifunctorFunctor (I J : Type*) :
    GradedObject I C₁ ⥤ GradedObject J C₂ ⥤ GradedObject (I × J) C₃ where
  obj X :=
    { obj := fun Y ij => (F.obj (X ij.1)).obj (Y ij.2)
      map := fun φ ij => (F.obj (X ij.1)).map (φ ij.2) }
  map φ :=
    { app := fun Y ij => (F.map (φ ij.1)).app (Y ij.2) }

section

variable {I J K : Type*} (p : I × J → K)

@[simp]
noncomputable def mapBifunctorMapObj (X : GradedObject I C₁) (Y : GradedObject J C₂)
  [HasMap (((mapBifunctorFunctor F I J).obj X).obj Y) p] : GradedObject K C₃ :=
    (((mapBifunctorFunctor F I J).obj X).obj Y).mapObj p

@[simp]
noncomputable def mapBifunctorMapMap {X₁ X₂ : GradedObject I C₁} (f : X₁ ⟶ X₂)
    {Y₁ Y₂ : GradedObject J C₂} (g : Y₁ ⟶ Y₂)
    [HasMap (((mapBifunctorFunctor F I J).obj X₁).obj Y₁) p]
    [HasMap (((mapBifunctorFunctor F I J).obj X₂).obj Y₂) p] :
    mapBifunctorMapObj F p X₁ Y₁ ⟶ mapBifunctorMapObj F p X₂ Y₂ :=
  GradedObject.mapMap (((mapBifunctorFunctor F I J).map f).app Y₁ ≫ ((mapBifunctorFunctor F I J).obj X₂).map g) p

@[simps]
noncomputable def mapBifunctorMapFunctor [∀ X Y, HasMap (((mapBifunctorFunctor F I J).obj X).obj Y) p] :
    GradedObject I C₁ ⥤ GradedObject J C₂ ⥤ GradedObject K C₃ where
  obj X :=
    { obj := fun Y => mapBifunctorMapObj F p X Y
      map := fun ψ => mapBifunctorMapMap F p (𝟙 X) ψ }
  map {X₁ X₂} φ :=
    { app := fun Y => mapBifunctorMapMap F p φ (𝟙 Y)
      naturality := fun {Y₁ Y₂} ψ => by
        dsimp
        simp only [Functor.map_id, NatTrans.id_app, Category.id_comp, Category.comp_id,
          ← mapMap_comp, NatTrans.naturality] }

end

end GradedObject

end CategoryTheory
