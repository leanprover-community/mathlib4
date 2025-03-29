/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Endomorphisms of an object in a bicategory, as a monoidal category.
-/


namespace CategoryTheory

variable {C : Type*} [Bicategory C]

/-- The endomorphisms of an object in a bicategory can be considered as a monoidal category. -/
def EndMonoidal (X : C) :=
  X ⟶ X
-- The `Category` instance should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380

instance (X : C) : Category (EndMonoidal X) :=
  show Category (X ⟶ X) from inferInstance

instance (X : C) : Inhabited (EndMonoidal X) :=
  ⟨𝟙 X⟩

open Bicategory

open MonoidalCategory

open Bicategory

attribute [local simp] EndMonoidal in
instance (X : C) : MonoidalCategory (EndMonoidal X) :=
  letI i : MonoidalCategoryStruct (EndMonoidal X) := {
    tensorObj f g := f ≫ g
    whiskerLeft {f _ _} η := f ◁ η
    whiskerRight {_ _} η h := η ▷ h
    tensorUnit := 𝟙 _
    associator f g h := α_ f g h
    leftUnitor f := λ_ f
    rightUnitor f := ρ_ f
  };
  ofTensorHom (
    tensor_comp := by
      intros
      unfold i
      dsimp
      rw [Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight, Category.assoc, Category.assoc,
        Bicategory.whisker_exchange_assoc]
  )

end CategoryTheory
