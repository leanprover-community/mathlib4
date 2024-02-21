/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.Algebra.Group.Prod

/-!
# Shifts which commute

Given a category `C` equipped with shifts by two additive monoids `A` and `B`,
we introduce a typeclass `ShiftsComm C A B` which allows to construct
a shift by `A × B` on `C`. The data involve commuting isomorphisms
`shiftFunctor C b ⋙ shiftFunctor C a ≅ shiftFunctor C a ⋙ shiftFunctor C b`
for all `a : A` and `b : B` such that these isomorphisms (or their inverses)
satisfy the axioms of `(shiftFunctor C a).CommShift B` for all `a : A`
and `(shiftFunctor C b).CommShift A`.

This shall be used in order to construct a shift by `ℤ × ℤ` on the category
of homological bicomplexes.

-/

namespace CategoryTheory

open Category

variable (C A B : Type) [Category C] [AddMonoid A] [AddMonoid B]

class ShiftsComm [HasShift C A] [HasShift C B] where
  commIso (a : A) (b : B) :
    shiftFunctor C b ⋙ shiftFunctor C a ≅ shiftFunctor C a ⋙ shiftFunctor C b
  zero₁ (b : B) : commIso 0 b = (Functor.CommShift.isoZero (shiftFunctor C b) A).symm
  zero₂ (a : A) : commIso a 0 = (Functor.CommShift.isoZero (shiftFunctor C a) B)
  add₁ (a₁ a₂ : A) (b : B) : commIso (a₁ + a₂) b =
    (Functor.CommShift.isoAdd (commIso a₁ b).symm (commIso a₂ b).symm).symm
  add₂ (a : A) (b₁ b₂ : B) : commIso a (b₁ + b₂) =
    Functor.CommShift.isoAdd (commIso a b₁) (commIso a b₂)

variable {A B}

abbrev ShiftsComm' (_ : HasShift C A) (_ : HasShift C B) := ShiftsComm C A B

section

variable [HasShift C A] [HasShift C B] [ShiftsComm C A B]

def shiftsCommIso (a : A) (b : B) :
    shiftFunctor C b ⋙ shiftFunctor C a ≅ shiftFunctor C a ⋙ shiftFunctor C b :=
  ShiftsComm.commIso a b

lemma shiftComm_zero₁ (b : B) :
    shiftsCommIso C (0 : A) b = (Functor.CommShift.isoZero (shiftFunctor C b) A).symm :=
  ShiftsComm.zero₁ b

lemma shiftComm_zero₂ (a : A) :
    shiftsCommIso C a (0 : B) = (Functor.CommShift.isoZero (shiftFunctor C a) B) :=
  ShiftsComm.zero₂ a

end

namespace ShiftCombine

variable [HasShift C A] [HasShift C B] [ShiftsComm C A B]

def combineShiftFunctor (c : A × B) : C ⥤ C := shiftFunctor C c.1 ⋙ shiftFunctor C c.2

variable (A B) in
@[simps!]
noncomputable def combineShiftFunctorZero : combineShiftFunctor C (0 : A × B) ≅ 𝟭 C :=
  isoWhiskerRight (shiftFunctorZero C A) _ ≪≫ shiftFunctorZero C B

@[simps!]
noncomputable def combineShiftFunctorAdd' (c₁ c₂ c : A × B) (h : c₁ + c₂ = c) :
    combineShiftFunctor C c ≅ combineShiftFunctor C c₁ ⋙ combineShiftFunctor C c₂ := by
  refine' isoWhiskerRight (shiftFunctorAdd' C c₁.1 c₂.1 c.1 (by rw [← h]; rfl)) _ ≪≫
    isoWhiskerLeft _ (shiftFunctorAdd' C c₁.2 c₂.2 c.2 (by rw [← h]; rfl)) ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (shiftsCommIso C c₂.1 c₁.2).symm _) ≪≫
    isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫ (Functor.associator _ _ _).symm

noncomputable def combineShiftFunctorAdd (c c' : A × B) :
    combineShiftFunctor C (c + c') ≅ combineShiftFunctor C c ⋙ combineShiftFunctor C c' :=
  combineShiftFunctorAdd' C c c' _ rfl

lemma combineShiftFunctorAdd'_eq_combineShiftFunctorAdd (c c' : A × B) :
    combineShiftFunctorAdd' C c c' _ rfl = combineShiftFunctorAdd C c c' := rfl

lemma combineShiftFunctorAdd_hom_app_eq
    (c₁ c₂ c : A × B) (h : c₁ + c₂ = c) (X : C) :
    (combineShiftFunctorAdd C c₁ c₂).hom.app X = eqToHom (by subst h; rfl) ≫
      (combineShiftFunctorAdd' C c₁ c₂ c h).hom.app X := by
  subst h
  simp [combineShiftFunctorAdd'_eq_combineShiftFunctorAdd]

lemma zero_add_hom_app' (c : A × B) (X : C) :
    (combineShiftFunctorAdd' C 0 c c (zero_add c)).hom.app X =
      (combineShiftFunctor C c).map ((combineShiftFunctorZero C A B).inv.app X) := by
  dsimp
  simp only [combineShiftFunctorAdd'_hom_app, Prod.snd_zero, Prod.fst_zero, shiftComm_zero₂,
    Functor.CommShift.isoZero_inv_app, Functor.map_comp]
  dsimp [combineShiftFunctor]
  rw [shiftFunctorAdd'_zero_add_hom_app, shiftFunctorAdd'_zero_add_hom_app]
  dsimp
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp]
  erw [← NatTrans.naturality, ← NatTrans.naturality]
  rw [← NatTrans.naturality_assoc]
  rw [← NatTrans.naturality_assoc]
  rw [Iso.inv_hom_id_app, comp_id]
  dsimp
  simp only [Functor.map_comp]

lemma add_zero_hom_app' (c : A × B) (X : C) :
    (combineShiftFunctorAdd' C c 0 c (add_zero c)).hom.app X =
      (combineShiftFunctorZero C A B).inv.app ((combineShiftFunctor C c).obj X) := by
  dsimp
  simp only [combineShiftFunctorAdd'_hom_app, Prod.snd_zero, Prod.fst_zero, shiftComm_zero₁,
    Iso.symm_inv, Functor.CommShift.isoZero_hom_app, Functor.map_comp]
  dsimp [combineShiftFunctor]
  erw [← NatTrans.naturality_assoc, ← NatTrans.naturality_assoc]
  rw [← Functor.map_comp_assoc, shiftFunctorAdd'_add_zero_hom_app, Iso.inv_hom_id_app]
  dsimp
  rw [Functor.map_id, id_comp, shiftFunctorAdd'_add_zero_hom_app]

variable (A B)

noncomputable def shiftMkCore : ShiftMkCore C (A × B) where
  F := combineShiftFunctor C
  zero := combineShiftFunctorZero C A B
  add := combineShiftFunctorAdd C
  assoc_hom_app := sorry
  zero_add_hom_app c X := by
    rw [combineShiftFunctorAdd_hom_app_eq C 0 c c (zero_add c), zero_add_hom_app' C c X]
  add_zero_hom_app c X := by
    rw [combineShiftFunctorAdd_hom_app_eq C c 0 c (add_zero c), add_zero_hom_app' C c X]

end ShiftCombine

noncomputable def HasShift.combine [HasShift C A] [HasShift C B] [ShiftsComm C A B] :
  HasShift C (A × B) := hasShiftMk _ _ (ShiftCombine.shiftMkCore C A B)

end CategoryTheory
