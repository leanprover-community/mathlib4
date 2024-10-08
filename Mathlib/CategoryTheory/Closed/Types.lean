/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.CategoryTheory.Closed.Cartesian

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

/-- The adjunction `Limits.Types.binaryProductFunctor.obj X ⊣ coyoneda.obj (Opposite.op X)`
for any `X : Type v₁`. -/
def Types.binaryProductAdjunction (X : Type v₁) :
    Limits.Types.binaryProductFunctor.obj X ⊣ coyoneda.obj (Opposite.op X) where
  unit := { app := fun Z (z : Z) x => ⟨x, z⟩ }
  counit := { app := fun Z xf => xf.2 xf.1 }

instance (X : Type v₁) : (Types.binaryProductFunctor.obj X).IsLeftAdjoint :=
  ⟨_, ⟨Types.binaryProductAdjunction X⟩⟩

instance : CartesianClosed (Type v₁) := CartesianClosed.mk _
  (fun X => Exponentiable.mk _ _
    ((Types.binaryProductAdjunction X).ofNatIsoLeft (Types.binaryProductIsoProd.app X)))

instance {C : Type v₁} [SmallCategory C] : CartesianClosed (C ⥤ Type v₁) :=
  CartesianClosed.mk _
    (fun F => by
      letI := FunctorCategory.prodPreservesColimits F
      have := Presheaf.isLeftAdjoint_of_preservesColimits (prod.functor.obj F)
      exact Exponentiable.mk _ _ (Adjunction.ofIsLeftAdjoint (prod.functor.obj F)))

-- TODO: once we have `MonoidalClosed` instances for functor categories into general monoidal
-- closed categories, replace this with that, as it will be a more explicit construction.
/-- This is not a good instance because of the universe levels. Below is the instance where the
target category is `Type (max u₁ v₁)`. -/
def cartesianClosedFunctorToTypes {C : Type u₁} [Category.{v₁} C] :
    CartesianClosed (C ⥤ Type (max u₁ v₁ u₂)) :=
  let e : (ULiftHom.{max u₁ v₁ u₂} (ULift.{max u₁ v₁ u₂} C)) ⥤ Type (max u₁ v₁ u₂) ≌
      C ⥤ Type (max u₁ v₁ u₂) :=
      Functor.asEquivalence ((whiskeringLeft _ _ _).obj
        (ULift.equivalence.trans ULiftHom.equiv).functor)
  cartesianClosedOfEquiv e

-- TODO: once we have `MonoidalClosed` instances for functor categories into general monoidal
-- closed categories, replace this with that, as it will be a more explicit construction.
instance {C : Type u₁} [Category.{v₁} C] : CartesianClosed (C ⥤ Type (max u₁ v₁)) :=
  cartesianClosedFunctorToTypes

-- TODO: once we have `MonoidalClosed` instances for functor categories into general monoidal
-- closed categories, replace this with that, as it will be a more explicit construction.
instance {C : Type u₁} [Category.{v₁} C] [EssentiallySmall.{v₁} C] :
    CartesianClosed (C ⥤ Type v₁) :=
  let e : (SmallModel C) ⥤ Type v₁ ≌ C ⥤ Type v₁ :=
    Functor.asEquivalence ((whiskeringLeft _ _ _).obj (equivSmallModel _).functor)
  cartesianClosedOfEquiv e

end CartesianClosed

end

end CategoryTheory
