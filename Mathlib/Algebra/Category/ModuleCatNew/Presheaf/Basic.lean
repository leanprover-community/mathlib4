import Mathlib.Algebra.Category.ModuleCatNew.ChangeOfRings
import Mathlib.Algebra.Category.Ring.Basic

universe v u v₁ u₁

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] (R : Cᵒᵖ ⥤ RingCat.{u})

structure PresheafOfModulesNew where
  obj (X : Cᵒᵖ) : ModuleCatNew.{v} (R.obj X)
  map {X Y : Cᵒᵖ} (f : X ⟶ Y) : obj X ⟶ (ModuleCatNew.restrictScalars (R.map f)).obj (obj Y)
  map_id (X : Cᵒᵖ) :
    map (𝟙 X) = (ModuleCatNew.restrictScalarsId (R.map_id X)).inv.app _ := by aesop_cat
  map_comp {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
      map (f ≫ g) =
      map f ≫ (ModuleCatNew.restrictScalars _).map (map g) ≫
        (ModuleCatNew.restrictScalarsComp (R.map_comp f g)).inv.app _ := by aesop_cat

namespace PresheafOfModulesNew

variable {R}
variable (M M₁ M₂ M₃ : PresheafOfModulesNew.{v} R)

@[ext]
structure Hom where
  app (X : Cᵒᵖ) : M₁.obj X ⟶ M₂.obj X
  naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) :
      M₁.map f ≫ (ModuleCatNew.restrictScalars (R.map f)).map (app Y) =
        app X ≫ M₂.map f := by aesop_cat

attribute [reassoc (attr := simp)] Hom.naturality

@[simps]
def Hom.id : Hom M M where
  app _ := 𝟙 _

variable {M₁ M₂ M₃}

@[simps]
def Hom.comp (f : Hom M₁ M₂) (g : Hom M₂ M₃) : Hom M₁ M₃ where
  app _ := f.app _ ≫ g.app _

instance : Category (PresheafOfModulesNew.{v} R) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[ext]
lemma hom_ext {f g : M₁ ⟶ M₂} (h : ∀ (X : Cᵒᵖ), f.app X = g.app X) :
    f = g := Hom.ext _ _ (by ext1; apply h)

end PresheafOfModulesNew
