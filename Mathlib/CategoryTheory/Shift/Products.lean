/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.Algebra.Group.Prod

/-!
# The shift on a product category

-/

namespace CategoryTheory

open Category

variable (C₁ C₂ : Type*) [Category C₁] [Category C₂]

lemma prod.eqTohom_fst {X Y : C₁ × C₂} (h : X = Y) :
    (eqToHom h).1 = eqToHom (by rw [h]) := by
  subst h; rfl

lemma prod.eqTohom_snd {X Y : C₁ × C₂} (h : X = Y) :
    (eqToHom h).2 = eqToHom (by rw [h]) := by
  subst h; rfl

variable
  (A₁ A₂ : Type*) [AddMonoid A₁] [AddMonoid A₂]
  [HasShift C₁ A₁] [HasShift C₂ A₂]

namespace HasShift

attribute [local simp] prod.eqTohom_fst prod.eqTohom_snd
  shiftFunctorAdd_add_zero_hom_app shiftFunctorAdd_zero_add_hom_app
  shiftFunctorAdd_assoc_hom_app shiftFunctorAdd' in

def shiftMkCoreProd : ShiftMkCore (C₁ × C₂) (A₁ × A₂) where
  F := fun ⟨x₁, x₂⟩ ↦ Functor.prod (shiftFunctor C₁ x₁) (shiftFunctor C₂ x₂)
  zero := NatIso.ofComponents (fun ⟨X₁, X₂⟩ ↦
    Iso.prod ((shiftFunctorZero C₁ A₁).app X₁) ((shiftFunctorZero C₂ A₂).app X₂))
  add := fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ↦ NatIso.ofComponents (fun ⟨X₁, X₂⟩ ↦
    Iso.prod ((shiftFunctorAdd C₁ x₁ y₁).app X₁) ((shiftFunctorAdd C₂ x₂ y₂).app X₂))

instance instProd : HasShift (C₁ × C₂) (A₁ × A₂) :=
  hasShiftMk _ _ (shiftMkCoreProd C₁ C₂ A₁ A₂)

end HasShift

end CategoryTheory
