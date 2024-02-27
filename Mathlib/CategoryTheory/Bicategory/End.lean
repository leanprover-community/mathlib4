/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Monoidal.Category

#align_import category_theory.bicategory.End from "leanprover-community/mathlib"@"6abb6de90754c5613a3aab6261eea9e5c72d539d"

/-!
# Endomorphisms of an object in a bicategory, as a monoidal category.
-/


namespace CategoryTheory

variable {C : Type*} [Bicategory C] (X : C)

-- do we need this instead of just reusing `End`?
/-- The endomorphisms of an object in a bicategory can be considered as a monoidal category. -/
def EndMonoidal := X ⟶ X
#align category_theory.End_monoidal CategoryTheory.EndMonoidal

-- Porting note: Deriving this fails in the definition above.
-- Adding category instance manually.
instance : Category (EndMonoidal X) := inferInstanceAs (Category (X ⟶ X))

instance (X : C) : Inhabited (EndMonoidal X) := ⟨𝟙 X⟩

open Bicategory

attribute [local simp] EndMonoidal whisker_exchange_assoc in
instance : MonoidalCategory (EndMonoidal X) where
  tensorObj f g := g ≫ f
  whiskerLeft {f g h} η := η ▷ f
  whiskerRight {f g} η h := h ◁ η
  tensorUnit := 𝟙 X
  associator f g h := (α_ h g f).symm
  leftUnitor f := ρ_ f
  rightUnitor f := λ_ f

end CategoryTheory
