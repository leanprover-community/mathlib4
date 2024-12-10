/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.CategoryTheory.Adjunction.Opposites

/-!
# The (naive) shift on the opposite category

If `C` is a category equipped with a shift by a monoid `A`, the opposite category
can be equipped with a shift such that the shift functor by `n` is `(shiftFunctor C n).op`.
This is the "naive" opposite shift, which we shall set on a category `OppositeShift C A`,
which is a type synonym for `Cᵒᵖ`.

However, for the application to (pre)triangulated categories, we would like to
define the shift on `Cᵒᵖ` so that `shiftFunctor Cᵒᵖ n` for `n : ℤ` identifies to
`(shiftFunctor C (-n)).op` rather than `(shiftFunctor C n).op`. Then, the construction
of the shift on `Cᵒᵖ` shall combine the shift on `OppositeShift C A` and another
construction of the "pullback" of a shift by a monoid morphism like `n ↦ -n`.

-/

namespace CategoryTheory

open Limits

variable (C : Type*) [Category C] (A : Type*) [AddMonoid A] [HasShift C A]

namespace HasShift

/-- Construction of the naive shift on the opposite category of a category `C`:
the shiftfunctor by `n` is `(shiftFunctor C n).op`. -/
noncomputable def mkShiftCoreOp : ShiftMkCore Cᵒᵖ A where
  F n := (shiftFunctor C n).op
  zero := (NatIso.op (shiftFunctorZero C A)).symm
  add a b := (NatIso.op (shiftFunctorAdd C a b)).symm
  assoc_hom_app m₁ m₂ m₃ X :=
    Quiver.Hom.unop_inj ((shiftFunctorAdd_assoc_inv_app m₁ m₂ m₃ X.unop).trans
      (by simp [shiftFunctorAdd']))
  zero_add_hom_app n X :=
    Quiver.Hom.unop_inj ((shiftFunctorAdd_zero_add_inv_app n X.unop).trans (by simp))
  add_zero_hom_app n X :=
    Quiver.Hom.unop_inj ((shiftFunctorAdd_add_zero_inv_app n X.unop).trans (by simp))

end HasShift

/-- The category `OppositeShift C A` is the opposite category `Cᵒᵖ` equipped
with the naive shift: `shiftFunctor (OppositeShift C A) n` is `(shiftFunctor C n).op`. -/
@[nolint unusedArguments]
def OppositeShift (A : Type*) [AddMonoid A] [HasShift C A] := Cᵒᵖ

instance : Category (OppositeShift C A) := by
  dsimp only [OppositeShift]
  infer_instance

noncomputable instance : HasShift (OppositeShift C A) A :=
  hasShiftMk Cᵒᵖ A (HasShift.mkShiftCoreOp C A)

instance [HasZeroObject C] : HasZeroObject (OppositeShift C A) := by
  dsimp only [OppositeShift]
  infer_instance

instance [Preadditive C] : Preadditive (OppositeShift C A) := by
  dsimp only [OppositeShift]
  infer_instance

instance [Preadditive C] (n : A) [(shiftFunctor C n).Additive] :
    (shiftFunctor (OppositeShift C A) n).Additive := by
  change (shiftFunctor C n).op.Additive
  infer_instance

lemma oppositeShiftFunctorZero_inv_app (X : OppositeShift C A) :
    (shiftFunctorZero (OppositeShift C A) A).inv.app X =
      ((shiftFunctorZero C A).hom.app X.unop).op := rfl

lemma oppositeShiftFunctorZero_hom_app (X : OppositeShift C A) :
    (shiftFunctorZero (OppositeShift C A) A).hom.app X =
      ((shiftFunctorZero C A).inv.app X.unop).op := by
  rw [← cancel_mono ((shiftFunctorZero (OppositeShift C A) A).inv.app X),
    Iso.hom_inv_id_app, oppositeShiftFunctorZero_inv_app, ← op_comp,
    Iso.hom_inv_id_app, op_id]
  rfl

section Add

variable {C A}
variable (X : OppositeShift C A) (a b c : A) (h : a + b = c)

lemma oppositeShiftFunctorAdd_inv_app :
    (shiftFunctorAdd (OppositeShift C A) a b).inv.app X =
      ((shiftFunctorAdd C a b).hom.app X.unop).op := rfl

lemma oppositeShiftFunctorAdd_hom_app :
    (shiftFunctorAdd (OppositeShift C A) a b).hom.app X =
      ((shiftFunctorAdd C a b).inv.app X.unop).op := by
  rw [← cancel_mono ((shiftFunctorAdd (OppositeShift C A) a b).inv.app X),
    Iso.hom_inv_id_app, oppositeShiftFunctorAdd_inv_app, ← op_comp,
    Iso.hom_inv_id_app, op_id]
  rfl

lemma oppositeShiftFunctorAdd'_inv_app :
    (shiftFunctorAdd' (OppositeShift C A) a b c h).inv.app X =
      ((shiftFunctorAdd' C a b c h).hom.app X.unop).op := by
  subst h
  simp only [shiftFunctorAdd'_eq_shiftFunctorAdd, oppositeShiftFunctorAdd_inv_app]

lemma oppositeShiftFunctorAdd'_hom_app :
    (shiftFunctorAdd' (OppositeShift C A) a b c h).hom.app X =
      ((shiftFunctorAdd' C a b c h).inv.app X.unop).op := by
  subst h
  simp only [shiftFunctorAdd'_eq_shiftFunctorAdd, oppositeShiftFunctorAdd_hom_app]

end Add

variable {C A}
variable (X : OppositeShift C A) (a b : A) (h : a + b = 0)

lemma oppositeShiftFunctorCompIsoId_hom_app :
    (shiftFunctorCompIsoId (OppositeShift C A) a b h).hom.app X =
    ((shiftFunctorCompIsoId C a b h).inv.app X.unop).op := by
  simp [shiftFunctorCompIsoId, oppositeShiftFunctorAdd'_inv_app, oppositeShiftFunctorZero_hom_app]

lemma oppositeShiftFunctorCompIsoId_inv_app :
    (shiftFunctorCompIsoId (OppositeShift C A) a b h).inv.app X =
    ((shiftFunctorCompIsoId C a b h).hom.app X.unop).op := by
  simp [shiftFunctorCompIsoId, oppositeShiftFunctorZero_inv_app, oppositeShiftFunctorAdd'_hom_app]

section CommShift

open Functor

variable {D : Type*} [Category D] [HasShift D A] (F : C ⥤ D)

namespace Opposite

noncomputable scoped instance commShiftOp [CommShift F A] :
    CommShift (C := OppositeShift C A) (D := OppositeShift D A) F.op A where
  iso a := (NatIso.op (F.commShiftIso a)).symm
  zero := by
    simp only
    rw [commShiftIso_zero]
    ext _
    simp only [op_obj, comp_obj, Iso.symm_hom, NatIso.op_inv, NatTrans.op_app,
      CommShift.isoZero_inv_app, op_comp, CommShift.isoZero_hom_app, op_map]
    erw [oppositeShiftFunctorZero_inv_app, oppositeShiftFunctorZero_hom_app]
    rfl
  add a b := by
    simp only
    rw [commShiftIso_add]
    ext _
    simp only [op_obj, comp_obj, Iso.symm_hom, NatIso.op_inv, NatTrans.op_app,
      CommShift.isoAdd_inv_app, op_comp, Category.assoc, CommShift.isoAdd_hom_app, op_map]
    erw [oppositeShiftFunctorAdd_inv_app, oppositeShiftFunctorAdd_hom_app]
    rfl

noncomputable def commShiftRemoveOp
    [CommShift (C := OppositeShift C A) (D := OppositeShift D A) F.op A] : CommShift F A where
  iso a := NatIso.removeOp (F.op.commShiftIso (C := OppositeShift C A)
    (D := OppositeShift D A) a).symm
  zero := by
    simp only
    rw [commShiftIso_zero]
    ext _
    simp only [comp_obj, NatIso.removeOp_hom, Iso.symm_hom, NatTrans.removeOp_app, op_obj,
      CommShift.isoZero_inv_app, op_map, unop_comp, Quiver.Hom.unop_op, CommShift.isoZero_hom_app]
    erw [oppositeShiftFunctorZero_hom_app, oppositeShiftFunctorZero_inv_app]
    rfl
  add a b := by
    simp only
    rw [commShiftIso_add]
    ext _
    simp only [comp_obj, NatIso.removeOp_hom, Iso.symm_hom, NatTrans.removeOp_app, op_obj,
      CommShift.isoAdd_inv_app, op_map, unop_comp, Quiver.Hom.unop_op, Category.assoc,
      CommShift.isoAdd_hom_app]
    erw [oppositeShiftFunctorAdd_hom_app, oppositeShiftFunctorAdd_inv_app]
    rfl

end Opposite

namespace Functor

open scoped Opposite

lemma commShiftOpIso [CommShift F A] (a : A) :
    F.op.commShiftIso a (C := OppositeShift C A) (D := OppositeShift D A) =
    (NatIso.op (F.commShiftIso a)).symm := rfl

end Functor

end CommShift

end CategoryTheory

namespace CategoryTheory

variable (C : Type*) [Category C] (A : Type*) [AddGroup A] [HasShift C A]

/--
The opposite of `(shiftEquiv' C a a' _).toAdjunction` is
`(shiftEquiv' (OppositeShift C A) a' a _).toAdjunction`.
-/
lemma shiftEquiv'_toAdjunction_op (a a' : A) (h : a + a' = 0) :
    (shiftEquiv' C a a' h).toAdjunction.opAdjointOpOfAdjoint =
    (shiftEquiv' (OppositeShift C A) a' a (by simp [eq_neg_of_add_eq_zero_left h])).toAdjunction :=
    by
  ext
  · simp only [Functor.id_obj, shiftEquiv'_inverse, shiftEquiv'_functor, Functor.comp_obj,
    Functor.op_obj, Adjunction.opAdjointOpOfAdjoint_unit_app, Equivalence.toAdjunction_counit,
    Equivalence.toAdjunction_unit]
    rw [opEquiv_apply, opEquiv_symm_apply, shiftEquiv'_unit, shiftEquiv'_counit,
    oppositeShiftFunctorCompIsoId_inv_app]
    simp
  · simp only [shiftEquiv'_functor, shiftEquiv'_inverse, Functor.comp_obj, Functor.op_obj,
    Functor.id_obj, Adjunction.opAdjointOpOfAdjoint_counit_app, Equivalence.toAdjunction_unit,
    Equivalence.toAdjunction_counit]
    rw [opEquiv_apply, opEquiv_symm_apply, shiftEquiv'_unit, shiftEquiv'_counit,
    oppositeShiftFunctorCompIsoId_hom_app]
    simp

/--
The opposite of `(shiftEquiv' C a a' _).symm.toAdjunction` is
`(shiftEquiv' (OppositeShift C A) a' a _).symm.toAdjunction`.
-/
lemma shiftEquiv'_symm_toAdjunction_op (a a' : A) (h : a + a' = 0) :
    (shiftEquiv' C a a' h).symm.toAdjunction.opAdjointOpOfAdjoint =
    (shiftEquiv' (OppositeShift C A) a' a
    (by simp [eq_neg_of_add_eq_zero_left h])).symm.toAdjunction := by
  ext
  · simp only [Functor.id_obj, Equivalence.symm_inverse, shiftEquiv'_functor,
    Equivalence.symm_functor, shiftEquiv'_inverse, Functor.comp_obj, Functor.op_obj,
    Adjunction.opAdjointOpOfAdjoint_unit_app, Equivalence.toAdjunction_counit,
    Equivalence.toAdjunction_unit]
    rw [opEquiv_apply, opEquiv_symm_apply, shiftEquiv'_symm_unit, shiftEquiv'_symm_counit,
    oppositeShiftFunctorCompIsoId_inv_app]
    simp
  · simp only [Equivalence.symm_functor, shiftEquiv'_inverse, Equivalence.symm_inverse,
    shiftEquiv'_functor, Functor.comp_obj, Functor.op_obj, Functor.id_obj,
    Adjunction.opAdjointOpOfAdjoint_counit_app, Equivalence.toAdjunction_unit,
    Equivalence.toAdjunction_counit]
    rw [opEquiv_apply, opEquiv_symm_apply, shiftEquiv'_symm_unit, shiftEquiv'_symm_counit,
    oppositeShiftFunctorCompIsoId_hom_app]
    simp

end CategoryTheory
