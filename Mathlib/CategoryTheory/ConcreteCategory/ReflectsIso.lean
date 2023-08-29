/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Functor.ReflectsIso

#align_import category_theory.concrete_category.reflects_isomorphisms from "leanprover-community/mathlib"@"73dd4b5411ec8fafb18a9d77c9c826907730af80"

/-!
A `forget₂ C D` forgetful functor between concrete categories `C` and `D`
whose forgetful functors both reflect isomorphisms, itself reflects isomorphisms.
-/


universe u

namespace CategoryTheory

instance : ReflectsIsomorphisms (forget (Type u)) where reflects _ _ _ {i} := i

variable (C : Type (u + 1)) [Category C] [ConcreteCategory.{u} C]

variable (D : Type (u + 1)) [Category D] [ConcreteCategory.{u} D]

-- This should not be an instance, as it causes a typeclass loop
-- with `CategoryTheory.hasForgetToType`.
/-- A `forget₂ C D` forgetful functor between concrete categories `C` and `D`
where `forget C` reflects isomorphisms, itself reflects isomorphisms.
-/
theorem reflectsIsomorphisms_forget₂ [HasForget₂ C D] [ReflectsIsomorphisms (forget C)] :
    ReflectsIsomorphisms (forget₂ C D) :=
  { reflects := fun X Y f {i} => by
      skip
      -- ⊢ IsIso f
      haveI i' : IsIso ((forget D).map ((forget₂ C D).map f)) := Functor.map_isIso (forget D) _
      -- ⊢ IsIso f
      haveI : IsIso ((forget C).map f) := by
        have := @HasForget₂.forget_comp C D
        rw [← this]
        exact i'
      apply isIso_of_reflects_iso f (forget C) }
      -- 🎉 no goals
#align category_theory.reflects_isomorphisms_forget₂ CategoryTheory.reflectsIsomorphisms_forget₂

end CategoryTheory
