/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.Algebra.Group.Prod

/-!

-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D]
  {M₁ M₂ : Type*} [AddMonoid M₁] [AddMonoid M₂]
  [HasShift C (M₁ × M₂)] [HasShift D (M₁ × M₂)] {F G : C ⥤ D}

namespace Functor.CommShift

@[implicit_reducible]
noncomputable def mkProd
    (iso₁ : ∀ (m₁ : M₁), shiftFunctor C (m₁, (0 : M₂)) ⋙ F ≅
      F ⋙ shiftFunctor D (m₁, (0 : M₂)))
    (iso₂ : ∀ (m₂ : M₂), shiftFunctor C ((0 : M₁), m₂) ⋙ F ≅
      F ⋙ shiftFunctor D ((0 : M₁), m₂))
    (zero₁ : iso₁ 0 = isoZero _ _)
    (zero₂ : iso₂ 0 = isoZero _ _)
    (add₁ : ∀ (m₁ m₁' : M₁), iso₁ (m₁ + m₁') = isoAdd' (by aesop) (iso₁ m₁) (iso₁ m₁'))
    (add₂ : ∀ (m₂ m₂' : M₂), iso₂ (m₂ + m₂') = isoAdd' (by aesop) (iso₂ m₂) (iso₂ m₂'))
    (comm : ∀ (m₁ : M₁) (m₂ : M₂),
      isoAdd' (c := (m₁, m₂)) (by aesop) (iso₁ m₁) (iso₂ m₂) =
        isoAdd' (by aesop) (iso₂ m₂) (iso₁ m₁)) :
    F.CommShift (M₁ × M₂) where
  commShiftIso m := isoAdd' (by aesop) (iso₁ m.1) (iso₂ m.2)
  commShiftIso_zero := by simp [zero₁, zero₂, isoAdd'_isoZero]
  commShiftIso_add := by
    rintro ⟨m₁, m₂⟩ ⟨m₁', m₂'⟩
    dsimp
    rw [add₁, add₂, isoAdd'_assoc (bc := (m₁', m₂ + m₂'))
      (abc := (m₁ + m₁', m₂ + m₂')) _ _ _ _ (by aesop) (by aesop),
      ← isoAdd'_assoc (a := (m₁', 0)) (ab := (m₁', m₂))
      _ _ _ (by aesop) (by aesop) (by aesop), comm,
      isoAdd'_assoc (bc := (m₁', m₂')) _ _ _ _ (by aesop) (by aesop),
      isoAdd, isoAdd'_assoc _ _ _ _ _ (by aesop)]

end Functor.CommShift

namespace NatTrans.CommShift

variable [F.CommShift (M₁ × M₂)] [G.CommShift (M₁ × M₂)] {τ : F ⟶ G}

lemma mk_prod (h₁ : ∀ (m₁ : M₁), CommShiftCore τ (m₁, (0 : M₂)))
    (h₂ : ∀ (m₂ : M₂), CommShiftCore τ ((0 : M₁), m₂)) :
    CommShift τ (M₁ × M₂) :=
  .of_core (fun (m₁, m₂) ↦ by
    rw [show (m₁, m₂) = (m₁, 0) + (0, m₂) by aesop]
    exact .add (h₁ m₁) (h₂ m₂))

end NatTrans.CommShift

end CategoryTheory
