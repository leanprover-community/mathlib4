/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Bimon_

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
  antipode_left : X.comul.hom ≫ (𝟙 X.X.X ⊗ S) ≫ X.X.mul = X.counit.hom ≫ X.X.one
  antipode_right : X.comul.hom ≫ (S ⊗ 𝟙 X.X.X) ≫ X.X.mul = X.counit.hom ≫ X.X.one

/--
Morphisms of Hopf monoids are just morphisms of the underlying bimonoids.
In fact they automatically intertwine the antipodes, proved below.
-/
instance : Category (Hopf_ C) := inferInstanceAs <| Category (InducedCategory (Bimon_ C) Hopf_.X)

-- TODO morphisms intertwine the antipodes.
-- TODO the antipode is an antihomomorphism.

end
