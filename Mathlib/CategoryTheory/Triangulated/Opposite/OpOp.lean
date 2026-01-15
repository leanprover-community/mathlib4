/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Opposite.Basic

/-!
# The triangulated equivalence `Cᵒᵖᵒᵖ ≌ C`.

In this file, we show that if `C` is a pretriangulated category, then
the functors `opOp C : C ⥤ Cᵒᵖᵒᵖ` and `unopUnop C : Cᵒᵖᵒᵖ ⥤ C` are triangulated.
We also show that the unit and counit isomorphisms of the equivalence
`opOpEquivalence C : Cᵒᵖᵒᵖ ≌ C` are compatible with shifts, which is summarized
by the property `(opOpEquivalence C).IsTriangulated`.

-/

@[expose] public section

namespace CategoryTheory

open Opposite Pretriangulated.Opposite Limits

variable (C : Type*) [Category* C] [HasShift C ℤ]

namespace Pretriangulated

namespace Opposite

namespace OpOpCommShift

/-- The isomorphism expressing the commutation of the functor `opOp C : C ⥤ Cᵒᵖᵒᵖ`
with the shift by `n : ℤ`. -/
def iso (n : ℤ) :
    shiftFunctor C n ⋙ opOp C ≅ opOp C ⋙ shiftFunctor Cᵒᵖᵒᵖ n :=
  NatIso.ofComponents
    (fun X ↦ ((shiftFunctorOpIso C (-n) n (neg_add_cancel n)).app (op X)).op ≪≫
      (shiftFunctorOpIso Cᵒᵖ n (-n) (add_neg_cancel n)).symm.app (op (op X)))
    (fun f ↦ Quiver.Hom.unop_inj (by
      simp [shiftFunctor_op_map _ n (-n), shiftFunctor_op_map _ (-n) n]))

variable {C}

@[reassoc]
lemma iso_hom_app (X : C) (n m : ℤ) (hnm : n + m = 0 := by lia) :
    (iso C n).hom.app X =
      ((shiftFunctorOpIso C m n (by lia)).hom.app (op X)).op ≫
        (shiftFunctorOpIso Cᵒᵖ _ _ hnm).inv.app (op (op X)) := by
  obtain rfl : m = -n := by lia
  rfl

@[reassoc]
lemma iso_inv_app (X : C) (n m : ℤ) (hnm : n + m = 0 := by lia) :
    (iso C n).inv.app X =
      (shiftFunctorOpIso Cᵒᵖ _ _ hnm).hom.app (op (op X)) ≫
        ((shiftFunctorOpIso C m n (by lia)).inv.app (op X)).op := by
  obtain rfl : m = -n := by lia
  rfl

end OpOpCommShift

namespace UnopUnopCommShift

/-- The isomorphism expressing the commutation of the functor `unopUnop C : Cᵒᵖᵒᵖ ⥤ C`
with the shift by `n : ℤ`. -/
def iso (n : ℤ) :
    shiftFunctor Cᵒᵖᵒᵖ n ⋙ unopUnop C ≅ unopUnop C ⋙ shiftFunctor C n :=
  NatIso.ofComponents
    (fun X ↦ ((shiftFunctorOpIso Cᵒᵖ n (-n) (add_neg_cancel n)).app X).unop.unop ≪≫
      ((shiftFunctorOpIso C (-n) n (neg_add_cancel n)).symm.app X.unop).unop)
    (fun {X Y} f ↦ Quiver.Hom.op_inj (by
      simp [shiftFunctor_op_map _ n (-n), shiftFunctor_op_map _ (-n) n]))

variable {C}

@[reassoc]
lemma iso_hom_app (X : Cᵒᵖᵒᵖ) (n m : ℤ) (hnm : n + m = 0 := by lia) :
    (iso C n).hom.app X =
      ((shiftFunctorOpIso Cᵒᵖ n m hnm).hom.app X).unop.unop ≫
        ((shiftFunctorOpIso C m n (by lia)).inv.app X.unop).unop := by
  obtain rfl : m = -n := by lia
  rfl

@[reassoc]
lemma iso_inv_app (X : Cᵒᵖᵒᵖ) (n m : ℤ) (hnm : n + m = 0 := by lia) :
    (iso C n).inv.app X =
      ((shiftFunctorOpIso C m n (by lia)).hom.app X.unop).unop ≫
        ((shiftFunctorOpIso Cᵒᵖ n m hnm).inv.app X).unop.unop := by
  obtain rfl : m = -n := by lia
  rfl

end UnopUnopCommShift

open OpOpCommShift in
instance : (opOp C).CommShift ℤ where
  commShiftIso := iso _
  commShiftIso_zero := by
    ext X
    refine Quiver.Hom.unop_inj (Quiver.Hom.unop_inj ?_)
    simp [iso_hom_app X 0 0, shiftFunctorZero_op_inv_app,
      shiftFunctorZero_op_hom_app]
  commShiftIso_add p q := by
    ext X
    refine Quiver.Hom.unop_inj (Quiver.Hom.unop_inj ?_)
    simp [← shiftFunctorAdd'_eq_shiftFunctorAdd, ← unop_comp_assoc, ← Functor.map_comp,
      fun X n ↦ iso_hom_app X n (-n) (add_neg_cancel n),
      shiftFunctor_op_map _ q (-q),
      shiftFunctorAdd'_op_inv_app _ p q (p + q) rfl (-p) (-q) (-(p + q))
        (add_neg_cancel p) (add_neg_cancel q) (add_neg_cancel (p + q)),
      shiftFunctorAdd'_op_hom_app _ (-p) (-q) (-(p + q)) (by lia) p q (p + q)
        (neg_add_cancel p) (neg_add_cancel q) (neg_add_cancel (p + q))]

open UnopUnopCommShift in
instance : (unopUnop C).CommShift ℤ where
  commShiftIso := iso _
  commShiftIso_zero := by
    ext X
    simp [iso_hom_app _ 0 0, shiftFunctorZero_op_inv_app,
      shiftFunctorZero_op_hom_app]
  commShiftIso_add p q := by
    ext X
    simp only [Functor.CommShift.isoAdd_hom_app, op_comp,
      ← shiftFunctorAdd'_eq_shiftFunctorAdd, Functor.map_comp,
      fun X n ↦ iso_hom_app X n (-n) (add_neg_cancel n),
      shiftFunctorAdd'_op_hom_app _ p q (p + q) rfl (-p) (-q) (-(p + q))
        (add_neg_cancel p) (add_neg_cancel q) (add_neg_cancel (p + q)),
      shiftFunctorAdd'_op_inv_app _ (-p) (-q) (-(p + q)) (by lia) p q (p + q)
        (neg_add_cancel p) (neg_add_cancel q) (neg_add_cancel (p + q)),
      shiftFunctor_op_map _ (-q) q, shiftFunctor_op_map _ q (-q)]
    simp [← Functor.map_comp_assoc, ← unop_comp, ← unop_comp_assoc]

end Opposite

variable {C}

@[reassoc]
lemma commShiftIso_opOp_hom_app (X : C) (n m : ℤ) (hnm : n + m = 0 := by lia) :
    ((opOp C).commShiftIso n).hom.app X =
      ((shiftFunctorOpIso C m n (by lia)).hom.app (op X)).op ≫
        (shiftFunctorOpIso Cᵒᵖ _ _ hnm).inv.app (op (op X)) :=
  OpOpCommShift.iso_hom_app ..

@[reassoc]
lemma commShiftIso_opOp_inv_app (X : C) (n m : ℤ) (hnm : n + m = 0 := by lia) :
    ((opOp C).commShiftIso n).inv.app X =
      (shiftFunctorOpIso Cᵒᵖ _ _ hnm).hom.app (op (op X)) ≫
      ((shiftFunctorOpIso C m n (by lia)).inv.app (op X)).op :=
  OpOpCommShift.iso_inv_app ..

@[reassoc]
lemma commShiftIso_unopUnop_hom_app (X : Cᵒᵖᵒᵖ) (n m : ℤ) (hnm : n + m = 0 := by lia) :
    ((unopUnop C).commShiftIso n).hom.app X =
      ((shiftFunctorOpIso Cᵒᵖ n m hnm).hom.app X).unop.unop ≫
        ((shiftFunctorOpIso C m n (by lia)).inv.app X.unop).unop :=
  UnopUnopCommShift.iso_hom_app ..

@[reassoc]
lemma commShiftIso_unopUnop_inv_app (X : Cᵒᵖᵒᵖ) (n m : ℤ) (hnm : n + m = 0 := by lia) :
    ((unopUnop C).commShiftIso n).inv.app X =
      ((shiftFunctorOpIso C m n (by lia)).hom.app X.unop).unop ≫
        ((shiftFunctorOpIso Cᵒᵖ n m hnm).inv.app X).unop.unop :=
  UnopUnopCommShift.iso_inv_app ..

instance : (opOpEquivalence C).functor.CommShift ℤ :=
  inferInstanceAs ((unopUnop C).CommShift ℤ)

instance : (opOpEquivalence C).inverse.CommShift ℤ :=
  inferInstanceAs ((opOp C).CommShift ℤ)

instance : (opOpEquivalence C).CommShift ℤ :=
  Equivalence.CommShift.mk'' _ _
    { shift_comm n := by
        ext X
        simp [Functor.commShiftIso_comp_hom_app,
          commShiftIso_opOp_hom_app _ n (-n),
          commShiftIso_unopUnop_hom_app _ n (-n),
          ← unop_comp_assoc] }

variable [Preadditive C] [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C]

instance : (opOp C).IsTriangulated where
  map_distinguished T hT := by
    refine isomorphic_distinguished _ (op_distinguished _ (op_distinguished _ hT)) _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (Quiver.Hom.unop_inj ?_))
    have := (shiftFunctorCompIsoId C (-1) 1 (neg_add_cancel 1)).inv.naturality T.mor₃
    dsimp at this ⊢
    simp only [shiftFunctor_op_map _ 1 (-1), Functor.op_obj,
      unop_id, shiftFunctor_op_map _ (-1) 1,
      commShiftIso_opOp_hom_app _ 1 (-1),
      opShiftFunctorEquivalence_counitIso_inv_app _ 1 (-1) (add_neg_cancel 1),
      unop_comp, Quiver.Hom.unop_op, Category.assoc, ← op_comp, Iso.inv_hom_id_app_assoc,
      shiftFunctorCompIsoId_op_hom_app, Iso.unop_hom_inv_id_app_assoc, ← Functor.map_comp]
    simp [Functor.map_comp, shift_shiftFunctorCompIsoId_hom_app, ← reassoc_of% this]

instance : (opOpEquivalence C).IsTriangulated :=
  .mk'' _ (by dsimp; infer_instance)

instance : (unopUnop C).IsTriangulated :=
  inferInstanceAs ((opOpEquivalence C).functor.IsTriangulated)

end Pretriangulated

end CategoryTheory
