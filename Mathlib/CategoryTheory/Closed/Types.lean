/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# Cartesian closure of Type

Show that `Type u₁` is Cartesian closed, and `C ⥤ Type u₁` is Cartesian closed for `C` a small
category in `Type u₁`.
Note this implies that the category of presheaves on a small category `C` is Cartesian closed.
-/


namespace CategoryTheory

noncomputable section

open Category Limits MonoidalCategory

universe v₁ v₂ u₁ u₂

variable {C : Type v₂} [Category.{v₁} C]

section CartesianClosed

/-- The adjunction `tensorLeft.obj X ⊣ coyoneda.obj (Opposite.op X)`
for any `X : Type v₁`. -/
def Types.tensorProductAdjunction (X : Type v₁) :
    tensorLeft X ⊣ coyoneda.obj (Opposite.op X) where
  unit := { app := fun Z (z : Z) x => ⟨x, z⟩ }
  counit := { app := fun _ xf => xf.2 xf.1 }

instance (X : Type v₁) : (tensorLeft X).IsLeftAdjoint :=
  ⟨_, ⟨Types.tensorProductAdjunction X⟩⟩

instance : CartesianClosed (Type v₁) := CartesianClosed.mk _
  fun X => Exponentiable.mk _ _ (Types.tensorProductAdjunction X)

instance {C : Type v₁} [SmallCategory C] : CartesianClosed (C ⥤ Type v₁) :=
  CartesianClosed.mk _ fun F => by
    haveI : ∀ X : Type v₁, PreservesColimits (tensorLeft X) := by infer_instance
    letI : PreservesColimits (tensorLeft F) := ⟨by infer_instance⟩
    have := Presheaf.isLeftAdjoint_of_preservesColimits.{v₁} (tensorLeft F)
    exact Exponentiable.mk _ _ (Adjunction.ofIsLeftAdjoint (tensorLeft F))

-- TODO: once we have `MonoidalClosed` instances for functor categories into general monoidal
-- closed categories, replace this with that, as it will be a more explicit construction.
attribute [local instance] uliftCategory in
/-- This is not a good instance because of the universe levels. Below is the instance where the
target category is `Type (max u₁ v₁)`. -/
def cartesianClosedFunctorToTypes {C : Type u₁} [Category.{v₁} C] :
    CartesianClosed (C ⥤ Type (max u₁ v₁ u₂)) :=
  let e : (ULiftHom.{max u₁ v₁ u₂} (ULift.{max u₁ v₁ u₂} C)) ⥤ Type (max u₁ v₁ u₂) ≌
      C ⥤ Type (max u₁ v₁ u₂) :=
      Functor.asEquivalence ((Functor.whiskeringLeft _ _ _).obj
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
    Functor.asEquivalence ((Functor.whiskeringLeft _ _ _).obj (equivSmallModel _).functor)
  cartesianClosedOfEquiv e

end CartesianClosed

end

end CategoryTheory
