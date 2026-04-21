/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Wide subcategories

A wide subcategory of a category `C` is a subcategory containing all the objects of `C`.

## Main declarations

Given a category `D`, a function `F : C → D` from a type `C` to the objects of `D`,
and a morphism property `P` on `D` which contains identities and is stable under
composition, the type class `InducedWideCategory D F P` is a typeclass
synonym for `C` which comes equipped with a category structure whose morphisms `X ⟶ Y` are the
morphisms in `D` which have the property `P`.

The instance `WideSubcategory.category` provides a category structure on `WideSubcategory P`
whose objects are the objects of `C` and morphisms are the morphisms in `C` which have the
property `P`.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

open MorphismProperty

section Induced

variable {C : Type u₁} (D : Type u₂) [Category.{v₁} D]
variable (F : C → D) (P : MorphismProperty D) [P.IsMultiplicative]

/-- `InducedWideCategory D F P`, where `F : C → D`, is a typeclass synonym for `C`,
which provides a category structure so that the morphisms `X ⟶ Y` are the morphisms
in `D` from `F X` to `F Y` which satisfy a property `P : MorphismProperty D` that is multiplicative.
-/
@[nolint unusedArguments]
def InducedWideCategory (_F : C → D) (_P : MorphismProperty D) [IsMultiplicative _P] :=
  C

variable {D}

instance InducedWideCategory.hasCoeToSort {α : Sort*} [CoeSort D α] :
    CoeSort (InducedWideCategory D F P) α :=
  ⟨fun c => F c⟩

variable {F P} in
/-- The type of morphisms in `InducedWideCategory D F P` between `X` and `Y`
is a 2-field structure consisting of a morphism `F X ⟶ F Y` in `D` that satisfies
the property `P`. -/
@[ext]
structure InducedWideCategory.Hom (X Y : InducedWideCategory D F P) where
  /-- The underlying morphism. -/
  hom : F X ⟶ F Y
  /-- The property that the morphism satisfies. -/
  property : P hom

@[simps!]
instance InducedWideCategory.category :
    Category (InducedWideCategory D F P) where
  Hom X Y := Hom X Y
  id X := ⟨𝟙 (F X), P.id_mem (F X)⟩
  comp {_ _ _} f g := ⟨f.1 ≫ g.1, P.comp_mem _ _ f.2 g.2⟩

/-- The forgetful functor from an induced wide category to the original category. -/
@[simps]
def wideInducedFunctor : InducedWideCategory D F P ⥤ D where
  obj := F
  map {_ _} f := f.1

/-- The induced functor `wideInducedFunctor F P : InducedWideCategory D F P ⥤ D`
is faithful. -/
instance InducedWideCategory.faithful : (wideInducedFunctor F P).Faithful where
  map_injective {X Y} f g eq := by
    cases f
    cases g
    aesop

end Induced

section WideSubcategory

variable {C : Type u₁} [Category.{v₁} C]
variable (P : MorphismProperty C) [IsMultiplicative P]

/--
Structure for wide subcategories. Objects ignore the morphism property.
-/
@[ext, nolint unusedArguments]
structure WideSubcategory (_P : MorphismProperty C) [IsMultiplicative _P] where
  /-- The category of which this is a wide subcategory -/
  obj : C

instance WideSubcategory.category : Category.{v₁} (WideSubcategory P) :=
  InducedWideCategory.category WideSubcategory.obj P

@[ext]
lemma WideSubcategory.hom_ext {X Y : WideSubcategory P} {f g : X ⟶ Y} (h : f.hom = g.hom) :
    f = g :=
  InducedWideCategory.Hom.ext h

@[simp]
lemma WideSubcategory.id_def (X : WideSubcategory P) : (CategoryStruct.id X).1 = 𝟙 X.obj := rfl

@[simp]
lemma WideSubcategory.comp_def {X Y Z : WideSubcategory P} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).1 = (f.1 ≫ g.1 : X.obj ⟶ Z.obj) := rfl

/-- The forgetful functor from a wide subcategory into the original category
("forgetting" the condition).
-/
def wideSubcategoryInclusion : WideSubcategory P ⥤ C :=
  wideInducedFunctor WideSubcategory.obj P

@[simp]
theorem wideSubcategoryInclusion.obj (X) : (wideSubcategoryInclusion P).obj X = X.obj :=
  rfl

@[simp]
theorem wideSubcategoryInclusion.map {X Y} {f : X ⟶ Y} :
    (wideSubcategoryInclusion P).map f = f.1 :=
  rfl

/-- The inclusion of a wide subcategory is faithful. -/
instance wideSubcategory.faithful : (wideSubcategoryInclusion P).Faithful :=
  inferInstanceAs (wideInducedFunctor WideSubcategory.obj P).Faithful

variable {P} in
/-- Build an isomorphism in `WideSubcategory P` from an isomorphism in `C`. -/
@[simps!]
def isoMk {X Y : WideSubcategory P} (e : X.obj ≅ Y.obj)
    (h₁ : P e.hom) (h₂ : P e.inv) : X ≅ Y where
  hom := ⟨e.hom, h₁⟩
  inv := ⟨e.inv, h₂⟩

end WideSubcategory

end CategoryTheory
