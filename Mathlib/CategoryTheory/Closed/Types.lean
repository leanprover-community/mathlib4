/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.CategoryTheory.Closed.Cartesian

#align_import category_theory.closed.types from "leanprover-community/mathlib"@"024a4231815538ac739f52d08dd20a55da0d6b23"

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

instance (X : Type v₁) : IsLeftAdjoint (Types.binaryProductFunctor.obj X) where
  right :=
    { obj := fun Y => X ⟶ Y
      map := fun f g => g ≫ f }
  adj :=
    Adjunction.mkOfUnitCounit
      { unit := { app := fun Z (z : Z) x => ⟨x, z⟩ }
        counit := { app := fun Z xf => xf.2 xf.1 } }

-- Porting note: this instance should be moved to a higher file.
instance : HasFiniteProducts (Type v₁) :=
  hasFiniteProducts_of_hasProducts.{v₁} _

instance : CartesianClosed (Type v₁) :=
  CartesianClosed.mk _
    (fun X => Adjunction.leftAdjointOfNatIso (Types.binaryProductIsoProd.app X))

-- porting note: in mathlib3, the assertion was for `(C ⥤ Type u₁)`, but then Lean4 was
-- confused with universes. It makes no harm to relax the universe assumptions here.
instance {C : Type u₁} [Category.{v₁} C] : HasFiniteProducts (C ⥤ Type u₂) :=
  hasFiniteProducts_of_hasProducts _

instance {C : Type v₁} [SmallCategory C] : CartesianClosed (C ⥤ Type v₁) :=
  CartesianClosed.mk _
    (fun F =>
      letI := FunctorCategory.prodPreservesColimits F
      isLeftAdjointOfPreservesColimits (prod.functor.obj F))

end CartesianClosed

end

end CategoryTheory
