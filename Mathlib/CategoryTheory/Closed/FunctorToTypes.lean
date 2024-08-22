/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.CategoryTheory.Functor.FunctorHom

/-!
# Functors to Type are closed.

Show that `C ⥤ Type max w v u` is monoidal closed for `C` a category in `Type u` with morphisms in
`Type v`, and `w` an arbitrary universe.

## TODO
It should be shown that `C ⥤ Type max w v u` is cartesian closed.
-/


universe w v' v u u'

open CategoryTheory Functor MonoidalCategory

namespace CategoryTheory.FunctorToTypes

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

variable (F : C ⥤ Type max w v u)

/-- When `F G H : C ⥤ Type max w v u`, we have `(F ⊗ G ⟶ H) ≃ (G ⟶ F.functorHom H)`. -/
def functorHomEquiv (G H : C ⥤ Type max w v u) : (F ⊗ G ⟶ H) ≃ (G ⟶ F.functorHom H) :=
  (HomObjEquiv F H G).trans (Functor.functorHomEquiv F H G)

/-- Given a morphism `f : G ⟶ H`, an object `c : C`, and an element of `(F.functorHom G).obj c`,
construct an element of `(F.functorHom H).obj c`. -/
def rightAdj_map {F G H : C ⥤ Type max w v u} (f : G ⟶ H) (c : C) (a : (F.functorHom G).obj c) :
    (F.functorHom H).obj c where
      app := fun d b ↦ (a.app d b) ≫ (f.app d)
      naturality g h := by
        have := a.naturality g h
        change (F.map g ≫ a.app _ (h ≫ g)) ≫ _ = _
        aesop

/-- A right adjoint of `tensorLeft F`. -/
def rightAdj : (C ⥤ Type max w v u) ⥤ C ⥤ Type max w v u where
  obj G := F.functorHom G
  map f := { app := rightAdj_map f }

/-- The adjunction `tensorLeft F ⊣ rightAdj F`. -/
def adj : tensorLeft F ⊣ rightAdj F where
  homEquiv := functorHomEquiv F
  unit := {
    app := fun G ↦ functorHomEquiv F _ _ (𝟙 _)
    naturality := fun G H f ↦ by
      ext c y
      dsimp [rightAdj, functorHomEquiv, Functor.functorHomEquiv]
      ext d
      dsimp only [Monoidal.tensorObj_obj, rightOp_obj]
      rw [Eq.symm (FunctorToTypes.naturality G H f _ y)]
      rfl }
  counit := { app := fun G ↦ (functorHomEquiv F _ _).2 (𝟙 _) }

instance closed : Closed F where
  adj := adj F

instance monoidalClosed : MonoidalClosed (C ⥤ Type max w v u) where

end CategoryTheory.FunctorToTypes
