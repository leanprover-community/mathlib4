/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Control.EquivFunctor
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Types

#align_import category_theory.core from "leanprover-community/mathlib"@"369525b73f229ccd76a6ec0e0e0bf2be57599768"

/-!
# The core of a category

The core of a category `C` is the (non-full) subcategory of `C` consisting of all objects,
and all isomorphisms. We construct it as a `CategoryTheory.Groupoid`.

`CategoryTheory.Core.inclusion : Core C ⥤ C` gives the faithful inclusion into the original
category.

Any functor `F` from a groupoid `G` into `C` factors through `CategoryTheory.Core C`,
but this is not functorial with respect to `F`.
-/

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

-- morphism levels before object levels. See note [CategoryTheory universes].
/-- The core of a category C is the groupoid whose morphisms are all the
isomorphisms of C. -/
-- Porting note(#5171): linter not yet ported
-- @[nolint has_nonempty_instance]

def Core (C : Type u₁) := C
#align category_theory.core CategoryTheory.Core

variable {C : Type u₁} [Category.{v₁} C]

instance coreCategory : Groupoid.{v₁} (Core C) where
  Hom (X Y : C) := X ≅ Y
  id (X : C) := Iso.refl X
  comp f g := Iso.trans f g
  inv {X Y} f := Iso.symm f
#align category_theory.core_category CategoryTheory.coreCategory

namespace Core

@[simp]
/- Porting note: abomination -/
theorem id_hom (X : C) : Iso.hom (coreCategory.id X) = @CategoryStruct.id C _ X := by
  rfl
#align category_theory.core.id_hom CategoryTheory.Core.id_hom

@[simp]
theorem comp_hom {X Y Z : Core C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl
#align category_theory.core.comp_hom CategoryTheory.Core.comp_hom

variable (C)

/-- The core of a category is naturally included in the category. -/
def inclusion : Core C ⥤ C where
  obj := id
  map f := f.hom
#align category_theory.core.inclusion CategoryTheory.Core.inclusion

-- Porting note: This worked without proof before.
instance : (inclusion C).Faithful where
  map_injective := by
    intro _ _
    apply Iso.ext

variable {C} {G : Type u₂} [Groupoid.{v₂} G]

-- Note that this function is not functorial
-- (consider the two functors from [0] to [1], and the natural transformation between them).
/-- A functor from a groupoid to a category C factors through the core of C. -/
def functorToCore (F : G ⥤ C) : G ⥤ Core C where
  obj X := F.obj X
  map f := ⟨F.map f, F.map (Groupoid.inv f), _, _⟩
#align category_theory.core.functor_to_core CategoryTheory.Core.functorToCore

/-- We can functorially associate to any functor from a groupoid to the core of a category `C`,
a functor from the groupoid to `C`, simply by composing with the embedding `Core C ⥤ C`.
-/
def forgetFunctorToCore : (G ⥤ Core C) ⥤ G ⥤ C :=
  (whiskeringRight _ _ _).obj (inclusion C)
#align category_theory.core.forget_functor_to_core CategoryTheory.Core.forgetFunctorToCore

end Core

/-- `ofEquivFunctor m` lifts a type-level `EquivFunctor`
to a categorical functor `Core (Type u₁) ⥤ Core (Type u₂)`.
-/
def ofEquivFunctor (m : Type u₁ → Type u₂) [EquivFunctor m] : Core (Type u₁) ⥤ Core (Type u₂) where
  obj := m
  map f := (EquivFunctor.mapEquiv m f.toEquiv).toIso
  map_id α := by apply Iso.ext; funext x; exact congr_fun (EquivFunctor.map_refl' _) x
  map_comp f g := by
    apply Iso.ext; funext x; dsimp
    erw [Iso.toEquiv_comp, EquivFunctor.map_trans']
    rw [Function.comp]
#align category_theory.of_equiv_functor CategoryTheory.ofEquivFunctor

end CategoryTheory
