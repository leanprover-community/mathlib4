/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.closed.types
! leanprover-community/mathlib commit 024a4231815538ac739f52d08dd20a55da0d6b23
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Presheaf
import Mathbin.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathbin.CategoryTheory.Limits.Shapes.Types
import Mathbin.CategoryTheory.Closed.Cartesian

/-!
# Cartesian closure of Type

Show that `Type u₁` is cartesian closed, and `C ⥤ Type u₁` is cartesian closed for `C` a small
category in `Type u₁`.
Note this implies that the category of presheaves on a small category `C` is cartesian closed.
-/


namespace CategoryTheory

noncomputable section

open Category Limits

universe v₁ v₂ u₁ u₂

variable {C : Type v₂} [Category.{v₁} C]

section CartesianClosed

instance (X : Type v₁) : IsLeftAdjoint (Types.binaryProductFunctor.obj X)
    where
  right :=
    { obj := fun Y => X ⟶ Y
      map := fun Y₁ Y₂ f g => g ≫ f }
  adj :=
    Adjunction.mkOfUnitCounit
      { Unit := { app := fun Z (z : Z) x => ⟨x, z⟩ }
        counit := { app := fun Z xf => xf.2 xf.1 } }

instance : HasFiniteProducts (Type v₁) :=
  hasFiniteProducts_of_hasProducts.{v₁} _

instance : CartesianClosed (Type v₁)
    where closed' X :=
    { isAdj := Adjunction.leftAdjointOfNatIso (Types.binaryProductIsoProd.app X) }

instance {C : Type u₁} [Category.{v₁} C] : HasFiniteProducts (C ⥤ Type u₁) :=
  hasFiniteProducts_of_hasProducts.{u₁} _

instance {C : Type v₁} [SmallCategory C] : CartesianClosed (C ⥤ Type v₁)
    where closed' F :=
    {
      isAdj := by
        letI := functor_category.prod_preserves_colimits F
        apply is_left_adjoint_of_preserves_colimits (prod.functor.obj F) }

end CartesianClosed

end CategoryTheory

