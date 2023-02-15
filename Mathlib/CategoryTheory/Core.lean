/-
Copyright (c) 2019 Scott Morrison All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.core
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Control.EquivFunctor
import Mathbin.CategoryTheory.Groupoid
import Mathbin.CategoryTheory.Whiskering
import Mathbin.CategoryTheory.Types

/-!
# The core of a category

The core of a category `C` is the (non-full) subcategory of `C` consisting of all objects,
and all isomorphisms. We construct it as a `groupoid`.

`core.inclusion : core C ⥤ C` gives the faithful inclusion into the original category.

Any functor `F` from a groupoid `G` into `C` factors through `core C`,
but this is not functorial with respect to `F`.
-/


namespace CategoryTheory

universe v₁ v₂ u₁ u₂

-- morphism levels before object levels. See note [category_theory universes].
/-- The core of a category C is the groupoid whose morphisms are all the
isomorphisms of C. -/
@[nolint has_nonempty_instance]
def Core (C : Type u₁) :=
  C
#align category_theory.core CategoryTheory.Core

variable {C : Type u₁} [Category.{v₁} C]

instance coreCategory : Groupoid.{v₁} (Core C)
    where
  Hom := fun X Y : C => X ≅ Y
  inv X Y f := Iso.symm f
  id X := Iso.refl X
  comp X Y Z f g := Iso.trans f g
#align category_theory.core_category CategoryTheory.coreCategory

namespace Core

@[simp]
theorem id_hom (X : Core C) : Iso.hom (𝟙 X) = 𝟙 X :=
  rfl
#align category_theory.core.id_hom CategoryTheory.Core.id_hom

@[simp]
theorem comp_hom {X Y Z : Core C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).Hom = f.Hom ≫ g.Hom :=
  rfl
#align category_theory.core.comp_hom CategoryTheory.Core.comp_hom

variable (C)

/-- The core of a category is naturally included in the category. -/
def inclusion : Core C ⥤ C where
  obj := id
  map X Y f := f.Hom
#align category_theory.core.inclusion CategoryTheory.Core.inclusion

instance : Faithful (inclusion C) where

variable {C} {G : Type u₂} [Groupoid.{v₂} G]

-- Note that this function is not functorial
-- (consider the two functors from [0] to [1], and the natural transformation between them).
/-- A functor from a groupoid to a category C factors through the core of C. -/
noncomputable def functorToCore (F : G ⥤ C) : G ⥤ Core C
    where
  obj X := F.obj X
  map X Y f := ⟨F.map f, F.map (inv f)⟩
#align category_theory.core.functor_to_core CategoryTheory.Core.functorToCore

/-- We can functorially associate to any functor from a groupoid to the core of a category `C`,
a functor from the groupoid to `C`, simply by composing with the embedding `core C ⥤ C`.
-/
def forgetFunctorToCore : (G ⥤ Core C) ⥤ G ⥤ C :=
  (whiskeringRight _ _ _).obj (inclusion C)
#align category_theory.core.forget_functor_to_core CategoryTheory.Core.forgetFunctorToCore

end Core

/-- `of_equiv_functor m` lifts a type-level `equiv_functor`
to a categorical functor `core (Type u₁) ⥤ core (Type u₂)`.
-/
def ofEquivFunctor (m : Type u₁ → Type u₂) [EquivFunctor m] : Core (Type u₁) ⥤ Core (Type u₂)
    where
  obj := m
  map α β f := (EquivFunctor.mapEquiv m f.toEquiv).toIso
  -- These are not very pretty.
  map_id' α := by ext; exact congr_fun (EquivFunctor.map_refl _) x
  map_comp' α β γ f g := by
    ext
    simp only [EquivFunctor.mapEquiv_apply, Equiv.toIso_hom, Function.comp_apply, core.comp_hom,
      types_comp]
    erw [iso.to_equiv_comp, EquivFunctor.map_trans]
#align category_theory.of_equiv_functor CategoryTheory.ofEquivFunctor

end CategoryTheory

