namespace CategoryTheory

universe v v₁ v₂ u u₁ u₂

class Quiver (V : Type u) where
  Hom : V → V → Sort v

infixr:10 " ⟶ " => Quiver.Hom

structure Prefunctor (V : Type u₁) [Quiver.{v₁} V] (W : Type u₂) [Quiver.{v₂} W] where
  obj : V → W
  map : ∀ {X Y : V}, (X ⟶ Y) → (obj X ⟶ obj Y)

class CategoryStruct (obj : Type u) extends Quiver.{v + 1} obj : Type max u (v + 1) where
  id : ∀ X : obj, Hom X X
  comp : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)

notation "𝟙" => CategoryStruct.id  -- type as \b1

infixr:80 " ≫ " => CategoryStruct.comp -- type as \gg

class Category (obj : Type u) extends CategoryStruct.{v} obj : Type max u (v + 1) where
  id_comp : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f
  comp_id : ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f
  assoc : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), (f ≫ g) ≫ h = f ≫ g ≫ h

attribute [simp] Category.id_comp Category.comp_id Category.assoc

structure Functor (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]
    extends Prefunctor C D : Type max v₁ v₂ u₁ u₂ where
  map_id : ∀ X : C, map (𝟙 X) = 𝟙 (obj X)
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g

infixr:26 " ⥤ " => Functor -- type as \func

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

structure NatTrans (F G : C ⥤ D) : Type max u₁ v₂ where
  app : ∀ X : C, F.obj X ⟶ G.obj X
  naturality : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), F.map f ≫ app Y = app X ≫ G.map f

namespace NatTrans

variable {F G H : C ⥤ D}

theorem ext {α β : NatTrans F G} (w : ∀ X, α.app X = β.app X) : α = β := sorry

/-- `NatTrans.id F` is the identity natural transformation on a functor `F`. -/
protected def id (F : C ⥤ D) : NatTrans F F where
  app X := 𝟙 (F.obj X)
  naturality := sorry

@[simp]
theorem id_app (F : C ⥤ D) (X : C) : (NatTrans.id F).app X = 𝟙 (F.obj X) := rfl

/-- `vcomp α β` is the vertical compositions of natural transformations. -/
def vcomp (α : NatTrans F G) (β : NatTrans G H) : NatTrans F H where
  app X := α.app X ≫ β.app X
  naturality := sorry

@[simp]
theorem vcomp_app (α : NatTrans F G) (β : NatTrans G H) (X : C) :
    (vcomp α β).app X = α.app X ≫ β.app X := rfl

end NatTrans

open NatTrans

def Functor'.Category : Category.{max u₁ v₂} (C ⥤ D) where
  Hom F G := NatTrans F G
  id F := NatTrans.id F
  comp α β := vcomp α β
  comp_id := by
    intros
    apply NatTrans.ext
    intros
    -- We should be able to close the goal with `simp`, but `vcomp_app` won't fire.
    -- Instead, we resort to:
    erw [vcomp_app]
    erw [id_app]
    simp
  id_comp := sorry
  assoc := sorry


instance Functor.CategoryStruct : CategoryStruct.{max u₁ v₂} (C ⥤ D) where
  Hom F G := NatTrans F G
  id F := NatTrans.id F
  comp α β := vcomp α β

-- Changing this to Functor'.C makes it pick up fields from the `def` above?
def Functor'.CC : Category.{max u₁ v₂} (C ⥤ D) where
  Hom F G := NatTrans F G
  id F := NatTrans.id F
  comp α β := vcomp α β

theorem id_def (F : C ⥤ D) : 𝟙 F = NatTrans.id F := rfl
theorem comp_def {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) : α ≫ β = vcomp α β := rfl

instance Functor.CC : Category.{max u₁ v₂} (C ⥤ D) where
  comp_id := by
    intros
    apply NatTrans.ext
    intros
    simp [id_def, comp_def]
  id_comp := sorry
  assoc := sorry
