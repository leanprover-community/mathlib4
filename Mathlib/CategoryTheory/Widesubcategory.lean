/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Wide subcategories

A wide subcategory of a category `C` is a subcategory containing all the objects of `C`.

## Main declarations

Given a category `D`, a function `F : C → D `from a type `C` to the
objects of `D`, a morphism property `P` on `D` which contains identities and is stable under
composition, witnessed by `hP`, the type class `InducedWideCategory D F P hP` is a typeclass
synonym for `C` which comes equipped with a category structure with morphisms `X ⟶ Y` being the
morphisms in `D` which have the property `P`.

The instance `WideSubcategory.category` provides a category structure on `WideSubcategory P hP`
whose objects are the objects of `C` and morphisms are the morphisms in `C` which have the
property `P`.
-/

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

open MorphismProperty

section Induced

variable {C : Type u₁} (D : Type u₂) [Category.{v₁} D]
variable (F : C → D) (P : MorphismProperty D)
    (hP : IsMultiplicative P)

/-- `InducedWideCategory D F P hP`, where `F : C → D`, is a typeclass synonym for `C`,
which provides a category structure so that the morphisms `X ⟶ Y` are the morphisms
in `D` from `F X` to `F Y`.
-/
-- Porting note(#5171): removed @[nolint has_nonempty_instance]
@[nolint unusedArguments]
def InducedWideCategory (_F : C → D) (_P : MorphismProperty D)
    (_hP : IsMultiplicative _P) :=
  C

variable {D}

instance InducedWideCategory.hasCoeToSort {α : Sort*} [CoeSort D α] :
    CoeSort (InducedWideCategory D F P hP) α :=
  ⟨fun c => F c⟩

@[simps!]
instance InducedWideCategory.category :
    Category (InducedWideCategory D F P hP) where
  Hom X Y := {f : F X ⟶ F Y | P f}
  id X := ⟨𝟙 (F X), P.id_mem (F X)⟩
  comp {X Y Z} f g := ⟨f.1 ≫ g.1, P.comp_mem _ _ f.2 g.2⟩

/-- The forgetful functor from an induced wide category to the original category,
forgetting the extra data.
-/
@[simps]
def wideInducedFunctor : InducedWideCategory D F P hP ⥤ D where
  obj := F
  map {X Y} f := f.1

/-- The induced functor `wideInducedFunctor F P hP : InducedWideCategory D F P hP ⥤ D`
is faithful. -/
instance InducedWideCategory.faithful : (wideInducedFunctor F P hP).Faithful where
  map_injective {X Y} f g eq := by
    cases f
    cases g
    aesop

end Induced

section WideSubcategory

variable {C : Type u₁} [Category.{v₁} C]
variable (P : MorphismProperty C)
    (hP : IsMultiplicative P)

/--
Structure for wide subcategories. Objects ignore the morphism property.
-/
@[ext, nolint unusedArguments]
structure WideSubcategory (_P : MorphismProperty C)
    (_hP : IsMultiplicative _P) where
  /-- The category of which this is a wide subcategory-/
  obj : C

@[simps!]
instance WideSubcategory.category : Category.{v₁} (WideSubcategory P hP) :=
  InducedWideCategory.category WideSubcategory.obj P hP

lemma WideSubcategory.id_def (X : WideSubcategory P hP) : (CategoryStruct.id X).1 = 𝟙 X.obj := rfl

lemma WideSubcategory.comp_def {X Y Z : WideSubcategory P hP} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).1 = (f.1 ≫ g.1 : X.obj ⟶ Z.obj) := rfl

/-- The forgetful functor from a wide subcategory into the original category
("forgetting" the condition).
-/
def wideSubcategoryInclusion : WideSubcategory P hP ⥤ C :=
  wideInducedFunctor WideSubcategory.obj P hP

@[simp]
theorem wideSubcategoryInclusion.obj {X} : (wideSubcategoryInclusion P hP).obj X = X.obj :=
  rfl

@[simp]
theorem wideSubcategoryInclusion.map {X Y} {f : X ⟶ Y} :
    (wideSubcategoryInclusion P hP).map f = f.1 :=
  rfl

/-- The inclusion of a wide subcategory is faithful. -/
instance wideSubcategory.faithful : (wideSubcategoryInclusion P hP).Faithful := by
  exact inferInstanceAs (wideInducedFunctor WideSubcategory.obj P hP).Faithful

end WideSubcategory

end CategoryTheory
