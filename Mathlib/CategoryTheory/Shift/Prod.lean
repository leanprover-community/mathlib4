/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.Algebra.Group.Prod

/-!
# Shifts by a product

Given a category `C` equipped with shifts by two additive monoids `A` and `B`,
we introduce a typeclass `ShiftsComm C A B` which allows to construct
a shift `HasShift.prod C A B` by `A × B` on `C`. The data of this typeclass
involve commuting isomorphisms
`shiftFunctor C b ⋙ shiftFunctor C a ≅ shiftFunctor C a ⋙ shiftFunctor C b`
for all `a : A` and `b : B` such that these isomorphisms (or their inverses)
satisfy the axioms of `(shiftFunctor C a).CommShift B` for all `a : A`
and `(shiftFunctor C b).CommShift A` for all `b : B`.

This shall be used in order to construct a shift by `ℤ × ℤ` on the category
of homological bicomplexes.

-/

namespace CategoryTheory

open Category

variable (C A B : Type*) [Category C] [AddMonoid A] [AddMonoid B]

/-- This typeclass expresses the commutativity of two shifts on a category. -/
class ShiftsComm [HasShift C A] [HasShift C B] where
  /-- the commutation isomorphism -/
  commIso (a : A) (b : B) :
    shiftFunctor C b ⋙ shiftFunctor C a ≅ shiftFunctor C a ⋙ shiftFunctor C b
  zero₁ (b : B) : commIso 0 b = (Functor.CommShift.isoZero (shiftFunctor C b) A).symm := by
    aesop_cat
  zero₂ (a : A) : commIso a 0 = (Functor.CommShift.isoZero (shiftFunctor C a) B) := by
    aesop_cat
  add₁ (a₁ a₂ : A) (b : B) : commIso (a₁ + a₂) b =
    (Functor.CommShift.isoAdd (commIso a₁ b).symm (commIso a₂ b).symm).symm := by aesop_cat
  add₂ (a : A) (b₁ b₂ : B) : commIso a (b₁ + b₂) =
    Functor.CommShift.isoAdd (commIso a b₁) (commIso a b₂) := by aesop_cat

variable {A B}

/-- This typeclass expresses the commutativity of two shifts on a category. -/
abbrev ShiftsComm' (_ : HasShift C A) (_ : HasShift C B) := ShiftsComm C A B

section

variable [HasShift C A] [HasShift C B] [ShiftsComm C A B]

/-- The isomorphism expressing the commutativity of two shifts. -/
def shiftsCommIso (a : A) (b : B) :
    shiftFunctor C b ⋙ shiftFunctor C a ≅ shiftFunctor C a ⋙ shiftFunctor C b :=
  ShiftsComm.commIso a b

variable (A) in
lemma shiftComm_zero₁ (b : B) :
    shiftsCommIso C (0 : A) b = (Functor.CommShift.isoZero (shiftFunctor C b) A).symm :=
  ShiftsComm.zero₁ b

lemma shiftComm_add₁ (a₁ a₂ : A) (b : B) :
    shiftsCommIso C (a₁ + a₂) b = (Functor.CommShift.isoAdd (shiftsCommIso C a₁ b).symm
      (shiftsCommIso C a₂ b).symm).symm:=
  ShiftsComm.add₁ a₁ a₂ b

lemma shiftComm_add₁' (a₁ a₂ a : A) (h : a₁ + a₂ = a) (b : B) :
    shiftsCommIso C a b = (Functor.CommShift.isoAdd' h (shiftsCommIso C a₁ b).symm
      (shiftsCommIso C a₂ b).symm).symm := by
  subst h
  exact ShiftsComm.add₁ a₁ a₂ b


variable (B) in
lemma shiftComm_zero₂ (a : A) :
    shiftsCommIso C a (0 : B) = (Functor.CommShift.isoZero (shiftFunctor C a) B) :=
  ShiftsComm.zero₂ a

lemma shiftComm_add₂ (a : A) (b₁ b₂ : B) :
    shiftsCommIso C a (b₁ + b₂) = (Functor.CommShift.isoAdd (shiftsCommIso C a b₁)
      (shiftsCommIso C a b₂)) :=
  ShiftsComm.add₂ a b₁ b₂

lemma shiftComm_add₂' (a : A) (b₁ b₂ b : B) (h : b₁ + b₂ = b):
    shiftsCommIso C a b = (Functor.CommShift.isoAdd' h (shiftsCommIso C a b₁)
      (shiftsCommIso C a b₂)) := by
  subst h
  exact ShiftsComm.add₂ a b₁ b₂

end

namespace HasShift

namespace Prod

variable [HasShift C A] [HasShift C B] [ShiftsComm C A B]

/-- The shift by `⟨a, b⟩` is defined as `shiftFunctor C a ⋙ shiftFunctor C b`. -/
def prodShiftFunctor (c : A × B) : C ⥤ C := shiftFunctor C c.1 ⋙ shiftFunctor C c.2

variable (A B) in
/-- The isomorphism from `prodShiftFunctor C (0 : A × B)` to the identity functor. -/
@[simps!]
noncomputable def prodShiftFunctorZero : prodShiftFunctor C (0 : A × B) ≅ 𝟭 C :=
  isoWhiskerRight (shiftFunctorZero C A) _ ≪≫ shiftFunctorZero C B

/-- The compatibility of `prodShiftFunctor` with the addition in `A × B`. -/
@[simps!]
noncomputable def prodShiftFunctorAdd' (c₁ c₂ c : A × B) (h : c₁ + c₂ = c) :
    prodShiftFunctor C c ≅ prodShiftFunctor C c₁ ⋙ prodShiftFunctor C c₂ :=
  isoWhiskerRight (shiftFunctorAdd' C c₁.1 c₂.1 c.1 (by rw [← h]; rfl)) _ ≪≫
    isoWhiskerLeft _ (shiftFunctorAdd' C c₁.2 c₂.2 c.2 (by rw [← h]; rfl)) ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (shiftsCommIso C c₂.1 c₁.2).symm _) ≪≫
    isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫ (Functor.associator _ _ _).symm

/-- The compatibility of `prodShiftFunctor` with the addition in `A × B`. -/
noncomputable def prodShiftFunctorAdd (c c' : A × B) :
    prodShiftFunctor C (c + c') ≅ prodShiftFunctor C c ⋙ prodShiftFunctor C c' :=
  prodShiftFunctorAdd' C c c' _ rfl

lemma prodShiftFunctorAdd'_eq_prodShiftFunctorAdd (c c' : A × B) :
    prodShiftFunctorAdd' C c c' _ rfl = prodShiftFunctorAdd C c c' := rfl

lemma prodShiftFunctorAdd_hom_app_eq
    (c₁ c₂ c : A × B) (h : c₁ + c₂ = c) (X : C) :
    (prodShiftFunctorAdd C c₁ c₂).hom.app X = eqToHom (by subst h; rfl) ≫
      (prodShiftFunctorAdd' C c₁ c₂ c h).hom.app X := by
  subst h
  simp [prodShiftFunctorAdd'_eq_prodShiftFunctorAdd]

lemma zero_add_hom_app' (c : A × B) (X : C) :
    (prodShiftFunctorAdd' C 0 c c (zero_add c)).hom.app X =
      (prodShiftFunctor C c).map ((prodShiftFunctorZero C A B).inv.app X) := by
  dsimp
  simp only [prodShiftFunctorAdd'_hom_app, Prod.snd_zero, Prod.fst_zero, shiftComm_zero₂,
    Functor.CommShift.isoZero_inv_app, Functor.map_comp]
  dsimp [prodShiftFunctor]
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
    (prodShiftFunctorAdd' C c 0 c (add_zero c)).hom.app X =
      (prodShiftFunctorZero C A B).inv.app ((prodShiftFunctor C c).obj X) := by
  dsimp
  simp only [prodShiftFunctorAdd'_hom_app, Prod.snd_zero, Prod.fst_zero, shiftComm_zero₁,
    Iso.symm_inv, Functor.CommShift.isoZero_hom_app, Functor.map_comp]
  dsimp [prodShiftFunctor]
  erw [← NatTrans.naturality_assoc, ← NatTrans.naturality_assoc]
  rw [← Functor.map_comp_assoc, shiftFunctorAdd'_add_zero_hom_app, Iso.inv_hom_id_app]
  dsimp
  rw [Functor.map_id, id_comp, shiftFunctorAdd'_add_zero_hom_app]

lemma assoc_hom_app' (c₁ c₂ c₃ c₁₂ c₂₃ c : A × B)
    (h₁₂ : c₁ + c₂ = c₁₂) (h₂₃ : c₂ + c₃ = c₂₃) (h : c₁ + c₂ + c₃ = c) (X : C) :
    (prodShiftFunctorAdd' C c₁₂ c₃ c (by rw [← h₁₂, h])).hom.app X ≫
      (prodShiftFunctor C c₃).map ((prodShiftFunctorAdd' C c₁ c₂ c₁₂ h₁₂).hom.app X) =
      (prodShiftFunctorAdd' C c₁ c₂₃ c (by rw [← h₂₃, ← add_assoc, h])).hom.app X ≫
        (prodShiftFunctorAdd' C c₂ c₃ c₂₃ h₂₃).hom.app
          ((prodShiftFunctor C c₁).obj X) := by
  dsimp
  simp [shiftComm_add₂' C c₃.1 c₁.2 c₂.2 c₁₂.2 (by rw [← h₁₂]; rfl),
    shiftComm_add₁' C c₂.1 c₃.1 c₂₃.1 (by rw [← h₂₃]; rfl) c₁.2]
  dsimp [prodShiftFunctor]
  erw [← NatTrans.naturality_assoc, ← NatTrans.naturality_assoc,
    ← NatTrans.naturality_assoc, ← NatTrans.naturality_assoc]
  simp only [← Functor.map_comp, ← Functor.map_comp_assoc]
  rw [← shiftFunctorAdd'_assoc_hom_app c₁.1 c₂.1 c₃.1 c₁₂.1 c₂₃.1 c.1 (by rw [← h₁₂]; rfl)
    (by rw [← h₂₃]; rfl) (by rw [← h]; rfl) X]
  erw [Iso.inv_hom_id_app_assoc, ← NatTrans.naturality, Iso.inv_hom_id_app, comp_id]
  simp only [Functor.map_comp, assoc]
  erw [shiftFunctorAdd'_assoc_hom_app_assoc c₁.2 c₂.2 c₃.2 c₁₂.2 c₂₃.2 c.2
    (by rw [← h₁₂]; rfl) (by rw [← h₂₃]; rfl) (by rw [← h]; rfl)]
  congr 1
  dsimp
  simp only [Functor.map_comp, assoc, NatTrans.naturality_assoc,
    Functor.comp_obj, Functor.comp_map]
  simp only [← assoc]; congr 2; simp only [assoc]
  congr 2
  simp only [← Functor.map_comp]
  congr 2
  erw [← NatTrans.naturality]
  rfl

variable (A B)

/-- The data and properties which enables the definition of a shift by `A × B` on
a category given shifts by `A` and `B` which commute. -/
noncomputable def shiftMkCore : ShiftMkCore C (A × B) where
  F := prodShiftFunctor C
  zero := prodShiftFunctorZero C A B
  add := prodShiftFunctorAdd C
  assoc_hom_app c₁ c₂ c₃ X := by
    rw [← prodShiftFunctorAdd'_eq_prodShiftFunctorAdd C (c₁ + c₂) c₃,
      ← prodShiftFunctorAdd'_eq_prodShiftFunctorAdd C c₁ c₂,
      ← prodShiftFunctorAdd'_eq_prodShiftFunctorAdd C c₂ c₃,
      prodShiftFunctorAdd_hom_app_eq C c₁ (c₂ + c₃) (c₁ + c₂ + c₃) (add_assoc _ _ _).symm,
      assoc, eqToHom_trans_assoc, eqToHom_refl, id_comp,
      assoc_hom_app' C c₁ c₂ c₃ _ _ _ rfl rfl rfl]
  zero_add_hom_app c X := by
    rw [prodShiftFunctorAdd_hom_app_eq C 0 c c (zero_add c), zero_add_hom_app' C c X]
  add_zero_hom_app c X := by
    rw [prodShiftFunctorAdd_hom_app_eq C c 0 c (add_zero c), add_zero_hom_app' C c X]

end Prod

variable (A B)

/-- The shift by `A × B` on a category `C` when two shifts by `A` and `B` commute. -/
noncomputable def prod [HasShift C A] [HasShift C B] [ShiftsComm C A B] :
  HasShift C (A × B) := hasShiftMk _ _ (Prod.shiftMkCore C A B)

end HasShift

end CategoryTheory
