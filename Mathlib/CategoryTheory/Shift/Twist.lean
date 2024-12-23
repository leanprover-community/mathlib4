/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Group.Int
import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.CategoryTheory.CatCenter.Basic

/-!
# Twisting a shift

-/

namespace CategoryTheory

open Category

variable (C : Type*) [Category C] (A : Type*) [AddMonoid A] [HasShift C A]
  {G : Type*} [AddGroup G] [HasShift C G]

structure TwistShiftData where
  ε (a b) : (CatCenter C)ˣ
  add_zero (a : A) : ε a (0 : A) = 1
  zero_add (b : A) : ε (0 : A) b = 1
  assoc (a b c : A) : ε (a + b) c * ε a b = ε a (b + c) * ε b c
  commutes (a b c : A) : (shiftFunctor C a).CommutesWithCenterElement (ε b c).val :=
    by infer_instance

namespace TwistShiftData

attribute [simp] add_zero zero_add

variable {C A}

@[nolint unusedArguments]
def toCategory (_ : TwistShiftData C A) : Type _ := C

variable (t : TwistShiftData C A)

lemma ε_add (a₁ a₂ b : A) :
    t.ε (a₁ + a₂) b = t.ε a₁ (a₂ + b) * t.ε a₂ b * (t.ε a₁ a₂)⁻¹ := by
  rw [← t.assoc a₁ a₂ b, mul_inv_cancel_right]

lemma ε_neg (t : TwistShiftData C G) (a b : G) :
    t.ε (-a) b = t.ε a (-a) * (t.ε a (-a + b))⁻¹ := by
  have := t.assoc a (-a) b
  simp only [add_neg_cancel, zero_add, one_mul] at this
  simp only [this, mul_inv_cancel_comm]

set_option linter.docPrime false in
lemma ε_add' (a b₁ b₂ : A) :
    t.ε a (b₁ + b₂) = t.ε (a + b₁) b₂ * t.ε a b₁ * (t.ε b₁ b₂)⁻¹ := by
  simp [t.assoc a b₁ b₂]

set_option linter.docPrime false in
lemma ε_neg' (t : TwistShiftData C G) (a b : G) :
    t.ε a (-b) = t.ε b (-b) * (t.ε (a - b) b)⁻¹ := by
  have := t.assoc (a - b) b (-b)
  simp only [sub_add_cancel, add_neg_cancel, add_zero, one_mul] at this
  simp only [← this, mul_inv_cancel_right]

lemma assoc_val (a b c : A) :
    (t.ε (a + b) c).val * (t.ε a b).val = (t.ε a (b + c)).val * (t.ε b c).val := by
  exact congr_arg Units.val (t.assoc a b c)

instance : Category t.toCategory := inferInstanceAs (Category C)

def shiftMkCore : ShiftMkCore C A where
  F a := shiftFunctor C a
  zero := shiftFunctorZero C A
  add a b := (Functor.rightUnitor _).symm ≪≫
      isoWhiskerLeft _ (CatCenter.unitsMulEquiv (t.ε a b)) ≪≫
      Functor.rightUnitor _ ≪≫ shiftFunctorAdd C a b
  add_zero_hom_app a X := by
    dsimp
    rw [CatCenter.naturality_assoc]
    simp [shiftFunctorAdd_add_zero_hom_app]
  zero_add_hom_app b X := by simp [shiftFunctorAdd_zero_add_hom_app]
  assoc_hom_app a b c X := by
    have := t.commutes
    dsimp
    simp only [id_comp, Functor.map_comp, Functor.map_app_of_commutesWithCenterElement,
      Category.assoc]
    conv_lhs => rw [CatCenter.naturality_assoc, shiftFunctorAdd_assoc_hom_app a b c X]
    conv_rhs => rw [CatCenter.naturality_assoc, CatCenter.naturality_assoc,
      CatCenter.naturality_assoc]
    dsimp [shiftFunctorAdd']
    simp only [eqToHom_app, Category.assoc, Functor.id_obj, ← CatCenter.mul_app_assoc,
      t.assoc_val a b c]

instance : HasShift t.toCategory A := hasShiftMk _ _ t.shiftMkCore

end TwistShiftData

end CategoryTheory
