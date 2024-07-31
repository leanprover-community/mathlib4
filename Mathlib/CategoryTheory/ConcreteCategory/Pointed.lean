/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.ConcreteCategory.Basic

/-!
# The category of pointed objects of a concrete category

This file defines the category of pointed objects of a concrete category. In a concrete category
`C`, a pointed object is an object `X` together with a distinguished element of the underlying type
of `X`, often called the basepoint.

## Main definitions

* `Pointed C` is the type of pointed objects in a concrete category `C`. We equip this type
  with a category structure where the morphisms are the morphisms of the original category that
  preserve the basepoint.

* `Pointed.map`, for a map of concrete categories, takes the pointed objects of `C` to
  the pointed objects of `D`.

* `Pointed.functor` gives, for a map of concrete categories, a functor between the correponding
  categories of pointed objects.

### Implementation notes

This construction is equivalent to a special case of the category of elements construction and
also to a particular comma construction. This files provides a more convenient API for directly
working with the category of pointed objects. We prove the equivalences in
`CategoryTheory.ConcreteCategory.Pointed.elementsEquivalence` and
`CategoryTheory.ConcreteCategory.structuredArrowEquivalence`.
-/

namespace CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C] [ConcreteCategory.{w,v,u} C]

namespace ConcreteCategory

attribute [local instance] ConcreteCategory.hasCoeToSort
attribute [local instance] ConcreteCategory.instFunLike

variable (C) in

/-- The pointed objects of a category `C`. A pointed object in `C` is an object `obj : C`
together with a distinguished element `pt` of the underlying type of `obj`, often called
the basepoint. -/
class Pointed where
  /-- the underlying object -/
  obj : C
  /-- the basepoint -/
  pt : obj

namespace Pointed

@[ext]
lemma ext {A B : Pointed C} (h₁ : A.obj = B.obj)
    (h₂ : ConcreteCategory.forget.map (eqToHom h₁) A.pt = B.pt) :
    A = B := by
  obtain ⟨X, x⟩ := A
  obtain ⟨Y, y⟩ := B
  cases h₁
  congr 1
  aesop

/-- The type of morphisms between pointed objects. A morphism of pointed objects is a morphism
in the original category between the objects which preserve the basepoints. -/
structure Hom (A B : Pointed C) where
  /-- the object morphism -/
  obj : A.obj ⟶ B.obj
  /-- compatibility with the basedpoint -/
  pt : obj A.pt = B.pt := by aesop_cat

/-- The category structure on the category of pointed objects. -/
@[simps!]
instance category : Category (Pointed C) where
  Hom := Pointed.Hom
  id A := ⟨𝟙 A.obj, by aesop_cat⟩
  comp {X Y Z} f g := ⟨f.obj ≫ g.obj, by
    simp [f.pt, g.pt]⟩

/-- Constructor for morphisms of the category pointed objects. -/
@[simps!]
def homMk (A B : Pointed C) (f : A.obj ⟶ B.obj) (hf : f A.pt = B.pt) :
    A ⟶ B :=
  ⟨f, hf⟩

@[ext]
theorem Hom.ext {A B : Pointed C} (f g : A ⟶ B) (w : f.obj = g.obj) : f = g := by
  cases f
  cases g
  cases w
  rfl

@[simp]
theorem comp_obj {A B C : Pointed C} {f : A ⟶ B} {g : B ⟶ C} : (f ≫ g).obj = f.obj ≫ g.obj := rfl

@[simp]
theorem id_obj {A : Pointed C} : (𝟙 A : A ⟶ A).obj = 𝟙 A.obj := rfl

@[simp]
theorem id_pt {A B : Pointed C} (f : A ⟶ B) : f.obj A.pt = B.pt := f.pt

instance concreteCategory : ConcreteCategory (Pointed C) where
  forget :=
    { obj := fun A ↦ A.obj
      map := fun f ↦ f.obj }
  forget_faithful := by
    refine ⟨@fun X Y ↦ ?_⟩
    dsimp
    fapply Function.Injective.comp
    · apply forget_faithful.map_injective
    · apply Hom.ext

instance : (forget (Pointed C)).Faithful := by
  exact forget_faithful

/-- The forward direction of the equivalence `Pointed C ≌ (forget C).Elements`. -/
@[simps obj]
def toCategoryOfElement :
    Pointed C ⥤ (forget C).Elements where
  obj X := ⟨X.obj, X.pt⟩
  map {X Y} f := ⟨f.obj, f.pt⟩

/-- The reverse direction of the equivalence `Pointed C ≌ (forget C).Elements`. -/
@[simps map]
def fromCategoryOfElements :
    (forget C).Elements ⥤ Pointed C where
  obj X := ⟨X.1, X.2⟩
  map {X Y} f := ⟨f.1, f.2⟩

/-- The equivalence between `Pointed C` and the category of elements of the forgetful
functor of `C`. -/
@[simps! functor_obj functor_map inverse_obj inverse_map unitIso_hom
  unitIso_inv counitIso_hom counitIso_inv]
def elementsEquivalence : Pointed C ≌ (forget C).Elements :=
  Equivalence.mk (toCategoryOfElement) (fromCategoryOfElements)
    (NatIso.ofComponents fun X => eqToIso (by aesop_cat))
    (NatIso.ofComponents fun X => eqToIso (by aesop_cat))

/-- The equivalence between `Pointed C` and the comma category `(*, ConcreteCategory.forget)`. -/
@[simps! functor_obj functor_map inverse_obj inverse_map unitIso_hom
  unitIso_inv counitIso_hom counitIso_inv]
def structuredArrowEquivalence :
    Pointed C ≌ StructuredArrow PUnit (forget C) :=
  (elementsEquivalence).trans (CategoryOfElements.structuredArrowEquivalence _)

variable {D : Type u} [Category.{v} D] [ConcreteCategory.{w,v,u} D]

/-- For a map of concrete categories, `Pointed.map` takes the pointed objects of `C` to
the pointed objects of `D`. -/
@[simps!]
def map [HasForget₂ C D] (A : Pointed C) : Pointed D where
  obj := (forget₂ C D).obj A.obj
  pt := by
    rw [← Functor.comp_obj, HasForget₂.forget_comp]
    exact A.pt

/-- A map of concrete categories induces a functor between the correponding category of pointed
objects. -/
@[simps!]
def functor [HasForget₂ C D] : Pointed C ⥤ Pointed D :=
  toCategoryOfElement ⋙
    CategoryOfElements.map (eqToHom HasForget₂.forget_comp.symm) ⋙
      CategoryOfElements.pullback (ConcreteCategory.forget (C:= D)) (forget₂ C D) ⋙
        fromCategoryOfElements

end Pointed

end ConcreteCategory

end CategoryTheory
