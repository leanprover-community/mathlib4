/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.CategoryTheory.DiscreteCategory
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Bicategory.Strict

#align_import category_theory.category.Cat from "leanprover-community/mathlib"@"e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b"

/-!
# Category of categories

This file contains the definition of the category `Cat` of all categories.
In this category objects are categories and
morphisms are functors between these categories.

## Implementation notes

Though `Cat` is not a concrete category, we use `bundled` to define
its carrier type.
-/


universe v u

namespace CategoryTheory

-- intended to be used with explicit universe parameters
/-- Category of categories. -/
@[nolint checkUnivs]
def Cat :=
  Bundled Category.{v, u}
set_option linter.uppercaseLean3 false in
#align category_theory.Cat CategoryTheory.Cat

namespace Cat

instance : Inhabited Cat :=
  ⟨⟨Type u, CategoryTheory.types⟩⟩

--Porting note: maybe this coercion should be defined to be `objects.obj`?
instance : CoeSort Cat (Type u) :=
  ⟨Bundled.α⟩

instance str (C : Cat.{v, u}) : Category.{v, u} C :=
  Bundled.str C
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.str CategoryTheory.Cat.str

/-- Construct a bundled `Cat` from the underlying type and the typeclass. -/
def of (C : Type u) [Category.{v} C] : Cat.{v, u} :=
  Bundled.of C
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.of CategoryTheory.Cat.of

/-- Bicategory structure on `Cat` -/
instance bicategory : Bicategory.{max v u, max v u} Cat.{v, u}
    where
  Hom C D := C ⥤ D
  id C := 𝟭 C
  comp F G := F ⋙ G
  homCategory := fun _ _ => Functor.category
  whiskerLeft {C} {D} {E} F G H η := whiskerLeft F η
  whiskerRight {C} {D} {E} F G η H := whiskerRight η H
  associator {A} {B} {C} D := Functor.associator
  leftUnitor {A} B := Functor.leftUnitor
  rightUnitor {A} B := Functor.rightUnitor
  pentagon := fun {A} {B} {C} {D} {E}=> Functor.pentagon
  triangle {A} {B} {C} := Functor.triangle
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.bicategory CategoryTheory.Cat.bicategory

/-- `Cat` is a strict bicategory. -/
instance bicategory.strict : Bicategory.Strict Cat.{v, u} where
  id_comp {C} {D} F := by cases F; rfl
                          -- ⊢ 𝟙 C ≫ Functor.mk toPrefunctor✝ = Functor.mk toPrefunctor✝
                                   -- 🎉 no goals
  comp_id {C} {D} F := by cases F; rfl
                          -- ⊢ Functor.mk toPrefunctor✝ ≫ 𝟙 D = Functor.mk toPrefunctor✝
                                   -- 🎉 no goals
  assoc := by intros; rfl
              -- ⊢ (f✝ ≫ g✝) ≫ h✝ = f✝ ≫ g✝ ≫ h✝
                      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.bicategory.strict CategoryTheory.Cat.bicategory.strict

/-- Category structure on `Cat` -/
instance category : LargeCategory.{max v u} Cat.{v, u} :=
  StrictBicategory.category Cat.{v, u}
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.category CategoryTheory.Cat.category

@[simp]
theorem id_map {C : Cat} {X Y : C} (f : X ⟶ Y) : (𝟙 C : C ⥤ C).map f = f :=
  Functor.id_map f
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.id_map CategoryTheory.Cat.id_map

@[simp]
theorem comp_obj {C D E : Cat} (F : C ⟶ D) (G : D ⟶ E) (X : C) : (F ≫ G).obj X = G.obj (F.obj X) :=
  Functor.comp_obj F G X
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.comp_obj CategoryTheory.Cat.comp_obj

@[simp]
theorem comp_map {C D E : Cat} (F : C ⟶ D) (G : D ⟶ E) {X Y : C} (f : X ⟶ Y) :
    (F ≫ G).map f = G.map (F.map f) :=
  Functor.comp_map F G f
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.comp_map CategoryTheory.Cat.comp_map

/-- Functor that gets the set of objects of a category. It is not
called `forget`, because it is not a faithful functor. -/
def objects : Cat.{v, u} ⥤ Type u where
  obj C := C
  map F := F.obj
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.objects CategoryTheory.Cat.objects

-- porting note: this instance was needed for CategoryTheory.Category.Cat.Limit
instance (X : Cat.{v, u}) : Category (objects.obj X) := (inferInstance : Category X)

section

attribute [local simp] eqToHom_map

/-- Any isomorphism in `Cat` induces an equivalence of the underlying categories. -/
def equivOfIso {C D : Cat} (γ : C ≅ D) : C ≌ D
    where
  functor := γ.hom
  inverse := γ.inv
  unitIso := eqToIso <| Eq.symm γ.hom_inv_id
  counitIso := eqToIso γ.inv_hom_id
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.equiv_of_iso CategoryTheory.Cat.equivOfIso

end

end Cat

/-- Embedding `Type` into `Cat` as discrete categories.

This ought to be modelled as a 2-functor!
-/
@[simps]
def typeToCat : Type u ⥤ Cat where
  obj X := Cat.of (Discrete X)
  map := fun {X} {Y} f => by
    dsimp
    -- ⊢ Cat.of (Discrete X) ⟶ Cat.of (Discrete Y)
    exact Discrete.functor (Discrete.mk ∘ f)
    -- 🎉 no goals
  map_id X := by
    apply Functor.ext
    -- ⊢ autoParam (∀ (X_1 Y : ↑({ obj := fun X => Cat.of (Discrete X), map := fun {X …
    · intro X Y f
      -- ⊢ ({ obj := fun X => Cat.of (Discrete X), map := fun {X Y} f => id (Discrete.f …
      cases f
      -- ⊢ ({ obj := fun X => Cat.of (Discrete X), map := fun {X Y} f => id (Discrete.f …
      simp only [id_eq, eqToHom_refl, Cat.id_map, Category.comp_id, Category.id_comp]
      -- ⊢ (Discrete.functor (Discrete.mk ∘ 𝟙 X✝)).map { down := down✝ } = { down := do …
      apply ULift.ext
      -- ⊢ ((Discrete.functor (Discrete.mk ∘ 𝟙 X✝)).map { down := down✝ }).down = { dow …
      aesop_cat
      -- 🎉 no goals
    · aesop_cat
      -- 🎉 no goals
  map_comp f g := by apply Functor.ext; aesop_cat
                     -- ⊢ autoParam (∀ (X Y : ↑({ obj := fun X => Cat.of (Discrete X), map := fun {X Y …
                                        -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Type_to_Cat CategoryTheory.typeToCat

instance : Faithful typeToCat.{u} where
  map_injective {_X} {_Y} _f _g h :=
    funext fun x => congr_arg Discrete.as (Functor.congr_obj h ⟨x⟩)

instance : Full typeToCat.{u} where
  preimage F := Discrete.as ∘ F.obj ∘ Discrete.mk
  witness := by
    intro X Y F
    -- ⊢ typeToCat.map ((fun {X Y} F => Discrete.as ∘ F.obj ∘ Discrete.mk) F) = F
    apply Functor.ext
    -- ⊢ autoParam (∀ (X_1 Y_1 : ↑(typeToCat.obj X)) (f : X_1 ⟶ Y_1), (typeToCat.map  …
    · intro x y f
      -- ⊢ (typeToCat.map ((fun {X Y} F => Discrete.as ∘ F.obj ∘ Discrete.mk) F)).map f …
      dsimp
      -- ⊢ (Discrete.functor (Discrete.mk ∘ Discrete.as ∘ F.obj ∘ Discrete.mk)).map f = …
      apply ULift.ext
      -- ⊢ ((Discrete.functor (Discrete.mk ∘ Discrete.as ∘ F.obj ∘ Discrete.mk)).map f) …
      aesop_cat
      -- 🎉 no goals
    · rintro ⟨x⟩
      -- ⊢ (typeToCat.map ((fun {X Y} F => Discrete.as ∘ F.obj ∘ Discrete.mk) F)).obj { …
      apply Discrete.ext
      -- ⊢ ((typeToCat.map ((fun {X Y} F => Discrete.as ∘ F.obj ∘ Discrete.mk) F)).obj  …
      rfl
      -- 🎉 no goals

end CategoryTheory
