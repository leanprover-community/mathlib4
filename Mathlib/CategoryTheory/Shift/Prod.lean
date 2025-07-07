/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Group.Prod
import Mathlib.CategoryTheory.Shift.Basic

/-!
# The shift on the product category

-/

namespace CategoryTheory

variable (C₁ C₂ : Type*) [Category C₁] [Category C₂]

@[simp]
lemma Prod.eqToHom_fst {X Y : C₁ × C₂} (h : X = Y) :
    (eqToHom h).1 = eqToHom (by rw [h]) := by
  subst h
  rfl

@[simp]
lemma Prod.eqToHom_snd {X Y : C₁ ×  C₂} (h : X = Y) :
    (eqToHom h).2 = eqToHom (by rw [h]) := by
  subst h
  rfl

variable (A₁ A₂ : Type*) [AddMonoid A₁] [AddMonoid A₂] [HasShift C₁ A₁] [HasShift C₂ A₂]

attribute [local simp] shiftFunctorAdd_add_zero_hom_app shiftFunctorAdd_zero_add_hom_app
  shiftFunctorAdd_assoc_hom_app shiftFunctorAdd' in
instance HasShift.prod : HasShift (C₁ × C₂) (A₁ × A₂) :=
  hasShiftMk _ _
    { F := fun ⟨x₁, x₂⟩ ↦ (shiftFunctor C₁ x₁).prod (shiftFunctor C₂ x₂)
      zero := NatIso.prod (shiftFunctorZero C₁ A₁) (shiftFunctorZero C₂ A₂)
      add := fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ↦
        NatIso.prod (shiftFunctorAdd C₁ x₁ y₁) (shiftFunctorAdd C₂ x₂ y₂) }

end CategoryTheory
