/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Control.EquivFunctor
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Types

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
def Core (C : Type u₁) := C

variable {C : Type u₁} [Category.{v₁} C]

instance coreCategory : Groupoid.{v₁} (Core C) where
  Hom (X Y : C) := X ≅ Y
  id (X : C) := Iso.refl X
  comp f g := Iso.trans f g
  inv {_ _} f := Iso.symm f

namespace Core

@[simp]
/- Porting note: abomination -/
theorem id_hom (X : C) : Iso.hom (coreCategory.id X) = @CategoryStruct.id C _ X := by
  rfl

@[simp]
theorem comp_hom {X Y Z : Core C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

variable (C)

/-- The core of a category is naturally included in the category. -/
def inclusion : Core C ⥤ C where
  obj := id
  map f := f.hom

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
  map f := { hom := F.map f, inv := F.map (Groupoid.inv f) }

/-- We can functorially associate to any functor from a groupoid to the core of a category `C`,
a functor from the groupoid to `C`, simply by composing with the embedding `Core C ⥤ C`.
-/
def forgetFunctorToCore : (G ⥤ Core C) ⥤ G ⥤ C :=
  (whiskeringRight _ _ _).obj (inclusion C)

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
    erw [Iso.toEquiv_comp]
    rw [EquivFunctor.map_trans', Function.comp]

end CategoryTheory
