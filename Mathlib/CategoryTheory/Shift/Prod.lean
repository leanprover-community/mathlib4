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

variable {A₁ A₂}

@[simp]
lemma shiftFunctor_prod (a : A₁ × A₂) :
    shiftFunctor (C₁ × C₂) a = (shiftFunctor C₁ a.1).prod (shiftFunctor C₂ a.2) := rfl

variable (A₁ A₂) in
@[simp]
lemma shiftFunctorZero_prod :
    shiftFunctorZero (C₁ × C₂) (A₁ × A₂) =
      NatIso.prod (shiftFunctorZero C₁ A₁) (shiftFunctorZero C₂ A₂) := rfl

@[simp]
lemma shiftFunctorAdd_prod (a b : A₁ × A₂) :
    shiftFunctorAdd (C₁ × C₂) a b =
      NatIso.prod (shiftFunctorAdd C₁ a.1 b.1) (shiftFunctorAdd C₂ a.2 b.2) := rfl

@[simp]
lemma shiftFunctorAdd'_prod (a b c : A₁ × A₂) (h : a + b = c) :
    shiftFunctorAdd' (C₁ × C₂) a b c h =
      NatIso.prod (shiftFunctorAdd' C₁ a.1 b.1 c.1 (by aesop))
        (shiftFunctorAdd' C₂ a.2 b.2 c.2 (by aesop)) := by
  subst h
  rfl

end CategoryTheory
