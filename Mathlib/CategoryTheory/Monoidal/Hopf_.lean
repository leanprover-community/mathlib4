/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Bimon_
import Mathlib.CategoryTheory.Monoidal.Conv

/-!
# The category of Hopf monoids in a braided monoidal category.

-/

noncomputable section

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory C]

/--
A Hopf monoid in a braided category `C` is a bimonoid object in `C` equipped with an antipode.
-/
structure Hopf_ where
  X : Bimon_ C
  S : X.X.X ⟶ X.X.X
  antipode_left : X.comul.hom ≫ (S ▷ X.X.X) ≫ X.X.mul = X.counit.hom ≫ X.X.one
  antipode_right : X.comul.hom ≫ (X.X.X ◁ S) ≫ X.X.mul = X.counit.hom ≫ X.X.one

/--
Morphisms of Hopf monoids are just morphisms of the underlying bimonoids.
In fact they automatically intertwine the antipodes, proved below.
-/
instance : Category (Hopf_ C) := inferInstanceAs <| Category (InducedCategory (Bimon_ C) Hopf_.X)

/-- Morphisms of Hopf monoids intertwine the antipodes. -/
theorem hom_antipode {A B : Hopf_ C} (f : A ⟶ B) : f.hom.hom ≫ B.S = A.S ≫ f.hom.hom := by
  -- We show these elements are equal by exhibiting an element in the convolution algebra
  -- between `A` (as a comonoid) and `B` (as a monoid),
  -- such that the LHS is a left inverse, and the RHS is a right inverse.
  apply left_inv_eq_right_inv
    (M := Conv ((Bimon_.toComon_ C).obj A.X) B.X.X)
    (a := f.hom.hom)
  · erw [Conv.mul_eq, Conv.one_eq]
    simp only [Bimon_.toComon__obj_X, Bimon_.toComon__obj_comul, comp_whiskerRight, Category.assoc,
      Bimon_.toComon__obj_counit]
    slice_lhs 3 4 =>
      rw [← whisker_exchange]
    slice_lhs 2 3 =>
      rw [← tensorHom_def]
    slice_lhs 1 2 =>
      rw [← Bimon_.hom_comul_hom f]
    slice_lhs 2 4 =>
      rw [B.antipode_left]
    slice_lhs 1 2 =>
      rw [Bimon_.hom_counit_hom f]
  · erw [Conv.mul_eq, Conv.one_eq]
    simp only [Bimon_.toComon__obj_X, Bimon_.toComon__obj_comul, MonoidalCategory.whiskerLeft_comp,
      Category.assoc, Bimon_.toComon__obj_counit]
    slice_lhs 2 3 =>
      rw [← whisker_exchange]
    slice_lhs 3 4 =>
      rw [← tensorHom_def]
    slice_lhs 3 4 =>
      rw [← f.hom.mul_hom]
    slice_lhs 1 3 =>
      rw [A.antipode_right]
    slice_lhs 2 3 =>
      rw [f.hom.one_hom]

-- TODO the antipode is an antihomomorphism.



end
