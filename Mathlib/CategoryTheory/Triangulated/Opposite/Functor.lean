/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated

/-!
# Opposites of functors between pretriangulated categories,

If `F : C ⥤ D` is a functor between pretriangulated categories, we prove that
`F` is a triangulated functor if and only if `F.op` is a triangulated functor.
In order to do this, we first show that a `CommShift` structure on `F` naturally
gives one on `F.op` (for the shifts on `Cᵒᵖ` and `Dᵒᵖ` defined in
`CategoryTheory.Triangulated.Opposite.Basic`), and we then prove
that `F.mapTriangle.op` and `F.op.mapTriangle` correspond to each other via the
equivalences `(Triangle C)ᵒᵖ ≌ Triangle Cᵒᵖ` and `(Triangle D)ᵒᵖ ≌ Triangle Dᵒᵖ`
given by `CategoryTheory.Pretriangulated.triangleOpEquivalence`.

-/

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D)
  [F.CommShift ℤ]

namespace Pretriangulated.Opposite

/-- If `F` commutes with shifts, so does `F.op`, for the shifts chosen on `Cᵒᵖ` in
`CategoryTheory.Triangulated.Opposite.Basic`.
-/
noncomputable scoped instance commShiftOpInt : F.op.CommShift ℤ := by
  letI F' : OppositeShift C ℤ ⥤ OppositeShift D ℤ := F.op
  letI : F'.CommShift ℤ := F.commShiftOp ℤ
  apply F'.commShiftPullback

end Pretriangulated.Opposite

namespace Functor

open Category Limits Pretriangulated Opposite

@[reassoc]
lemma op_commShiftIso_hom_app (X : Cᵒᵖ) (n m : ℤ) (h : n + m = 0):
    (F.op.commShiftIso n).hom.app X =
      (F.map ((shiftFunctorOpIso C n m h).hom.app X).unop).op ≫
        ((F.commShiftIso m).inv.app X.unop).op ≫
        (shiftFunctorOpIso D n m h).inv.app (op (F.obj X.unop)) := by
  obtain rfl : m = -n := by omega
  rfl

@[reassoc]
lemma op_commShiftIso_inv_app (X : Cᵒᵖ) (n m : ℤ) (h : n + m = 0):
    (F.op.commShiftIso n).inv.app X =
      (shiftFunctorOpIso D n m h).hom.app (op (F.obj X.unop)) ≫
        ((F.commShiftIso m).hom.app X.unop).op ≫
          (F.map ((shiftFunctorOpIso C n m h).inv.app X).unop).op := by
  rw [← cancel_epi ((F.op.commShiftIso n).hom.app X), Iso.hom_inv_id_app,
    op_commShiftIso_hom_app _ X n m h, assoc, assoc]
  simp [← op_comp, ← F.map_comp]

@[reassoc]
lemma shift_map_op {X Y : C} (f : X ⟶ Y) (n : ℤ) :
    (F.map f).op⟦n⟧' = (F.op.commShiftIso n).inv.app _ ≫
      (F.map (f.op⟦n⟧').unop).op ≫ (F.op.commShiftIso n).hom.app _ :=
  (NatIso.naturality_1 (F.op.commShiftIso n) f.op).symm

lemma map_shift_unop {X Y : Cᵒᵖ} (f : X ⟶ Y) (n : ℤ) :
    F.map ((f⟦n⟧').unop) = ((F.op.commShiftIso n).inv.app Y).unop ≫
      ((F.map f.unop).op⟦n⟧').unop ≫ ((F.op.commShiftIso n).hom.app X).unop := by
  simp [shift_map_op]

lemma map_opShiftFunctorEquivalence_unit_hom_app (F : C ⥤ D) [F.CommShift ℤ] (X : Cᵒᵖ) (n : ℤ) :
    F.op.map ((opShiftFunctorEquivalence C n).unitIso.hom.app X) =
      (opShiftFunctorEquivalence D n).unitIso.hom.app (F.op.obj X) ≫
        (shiftFunctor D n).op.map (((F.op).commShiftIso n).inv.app X) ≫
          ((F.commShiftIso n).hom.app _).op := by
  rw [F.op_commShiftIso_inv_app _ _ _ (add_neg_cancel n)]
  simp only [id_obj, op_obj, opShiftFunctorEquivalence, comp_obj, Iso.trans_hom, NatIso.op_hom,
    isoWhiskerRight_hom, Iso.symm_hom, NatTrans.comp_app, NatTrans.op_app, whiskerRight_app, op_map,
    unop_comp, Quiver.Hom.unop_op, map_comp, map_shiftFunctorCompIsoId_hom_app,
    commShiftIso_hom_naturality_assoc, op_comp, assoc]
  slice_rhs 2 3 => rw [← op_comp, ← Functor.map_comp, ← unop_comp, Iso.inv_hom_id_app]
  simp

lemma map_opShiftFunctorEquivalence_unit_inv_app (F : C ⥤ D) [F.CommShift ℤ] (X : Cᵒᵖ) (n : ℤ) :
    F.op.map ((opShiftFunctorEquivalence C n).unitIso.inv.app X) = ((F.commShiftIso n).inv.app _).op
      ≫ (shiftFunctor D n).op.map (((F.op).commShiftIso n).hom.app X) ≫
        (opShiftFunctorEquivalence D n).unitIso.inv.app (F.op.obj X) := by
  simp only [opShiftFunctorEquivalence, comp_obj, op_obj, id_obj, Iso.trans_inv,
    isoWhiskerRight_inv, Iso.symm_inv, NatIso.op_inv, NatTrans.comp_app, whiskerRight_app, op_map,
    NatTrans.op_app, unop_comp, Quiver.Hom.unop_op, map_comp, map_shiftFunctorCompIsoId_inv_app,
    assoc, op_comp, F.op_commShiftIso_hom_app _ _ _ (add_neg_cancel n)]
  slice_rhs 4 5 => rw [← op_comp, ← Functor.map_comp, ← unop_comp, Iso.inv_hom_id_app]
  simp only [op_obj, unop_id, map_id, op_id, id_comp]
  slice_rhs 1 2 => rw [← op_comp]
                   change ((F ⋙ shiftFunctor D n).map ((shiftFunctorOpIso C _ _
                     (add_neg_cancel n)).hom.app X).unop ≫ (F.commShiftIso n).inv.app _).op
                   rw [(F.commShiftIso n).inv.naturality]
  simp

lemma map_opShiftFunctorEquivalence_counit_hom_app (F : C ⥤ D) [F.CommShift ℤ] (X : Cᵒᵖ) (n : ℤ) :
    F.op.map ((opShiftFunctorEquivalence C n).counitIso.hom.app X) = (F.op.commShiftIso n).hom.app _
      ≫ (shiftFunctor Dᵒᵖ n).map ((F.commShiftIso n).inv.app _).op ≫
        (opShiftFunctorEquivalence D n).counitIso.hom.app (F.op.obj X) := by
  simp [F.op_commShiftIso_hom_app _ _ _ (add_neg_cancel n), opShiftFunctorEquivalence]

lemma map_opShiftFunctorEquivalence_counit_inv_app (F : C ⥤ D) [F.CommShift ℤ] (X : Cᵒᵖ) (n : ℤ) :
    F.op.map ((opShiftFunctorEquivalence C n).counitIso.inv.app X) =
      (opShiftFunctorEquivalence D n).counitIso.inv.app (F.op.obj X) ≫
        (shiftFunctor Dᵒᵖ n).map ((F.commShiftIso n).hom.app _).op ≫
          (F.op.commShiftIso n).inv.app _ := by
  simp [F.op_commShiftIso_inv_app _ _ _ (add_neg_cancel n), opShiftFunctorEquivalence]

variable [HasZeroObject C] [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] [HasZeroObject D] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]

/--
If `F : C ⥤ D` commutes with shifts, this expresses the compatibility of `F.mapTriangle`
with the equivalences `Pretriangulated.triangleOpEquivalence` on `C` and `D`.
-/
noncomputable def triangleOpEquivalence_functor_naturality :
    F.mapTriangle.op ⋙ (triangleOpEquivalence D).functor ≅
      (triangleOpEquivalence C).functor ⋙ F.op.mapTriangle := by
  refine NatIso.ofComponents (fun T ↦ ?_) ?_
  · refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) ?_
    simp only [triangleOpEquivalence_functor, Functor.comp_obj, Functor.op_obj,
      Functor.mapTriangle_obj, TriangleOpEquivalence.functor_obj, Triangle.mk_obj₃,
      Triangle.mk_obj₂, Triangle.mk_obj₁, Triangle.mk_mor₂, Triangle.mk_mor₁,
      opShiftFunctorEquivalence_inverse, opShiftFunctorEquivalence_functor, Triangle.mk_mor₃,
      op_comp, Functor.op_map, Quiver.Hom.unop_op, unop_comp, Functor.map_comp, Iso.refl_hom,
      Functor.map_id, comp_id, assoc, id_comp]
    change _ = F.op.map ((opShiftFunctorEquivalence C 1).counitIso.inv.app (Opposite.op _)) ≫ _
    rw [shift_map_op, map_shift_unop, map_opShiftFunctorEquivalence_counit_inv_app]
    simp only [id_obj, op_obj, comp_obj, Quiver.Hom.unop_op, op_comp, op_unop, Quiver.Hom.op_unop,
      assoc, Iso.inv_hom_id_app, comp_id, Iso.inv_hom_id_app_assoc,
      opShiftFunctorEquivalence_inverse, opShiftFunctorEquivalence_functor]
  · intro _ _ _
    simp only [triangleOpEquivalence_functor, comp_obj, op_obj, mapTriangle_obj,
      TriangleOpEquivalence.functor_obj, Triangle.mk_obj₃, Triangle.mk_obj₂, Triangle.mk_obj₁,
      Triangle.mk_mor₂, Triangle.mk_mor₁, opShiftFunctorEquivalence_inverse,
      opShiftFunctorEquivalence_functor, Triangle.mk_mor₃, op_comp, op_map, Quiver.Hom.unop_op,
      unop_comp, comp_map, Triangle.isoMk_hom, Iso.refl_hom, triangleCategory_comp]
    ext
    · simp only [Triangle.mk_obj₁, TriangleMorphism.comp_hom₁,
      TriangleOpEquivalence.functor_map_hom₁, Triangle.mk_obj₃, Quiver.Hom.unop_op,
      mapTriangle_map_hom₃, Triangle.homMk_hom₁, comp_id, mapTriangle_map_hom₁, op_map, id_comp]
    · simp only [Triangle.mk_obj₂, TriangleMorphism.comp_hom₂,
      TriangleOpEquivalence.functor_map_hom₂, Quiver.Hom.unop_op, mapTriangle_map_hom₂,
      Triangle.homMk_hom₂, comp_id, op_map, id_comp]
    · simp only [Triangle.mk_obj₃, TriangleMorphism.comp_hom₃,
      TriangleOpEquivalence.functor_map_hom₃, Quiver.Hom.unop_op, mapTriangle_map_hom₃,
      Triangle.homMk_hom₃, comp_id, op_map, id_comp]
      rfl

/--
If `F : C ⥤ D` commutes with shifts, this expresses the compatibility of `F.mapTriangle`
with the equivalences `Pretriangulated.triangleOpEquivalence` on `C` and `D`.
-/
noncomputable def triangleOpEquivalence_inverse_naturality :
    F.op.mapTriangle ⋙ (triangleOpEquivalence D).inverse ≅
      (triangleOpEquivalence C).inverse ⋙ F.mapTriangle.op :=
  (Functor.leftUnitor _).symm ≪≫ isoWhiskerRight (triangleOpEquivalence C).counitIso.symm _
  ≪≫ Functor.associator _ _ _ ≪≫ isoWhiskerLeft (triangleOpEquivalence C).inverse
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerLeft _ (isoWhiskerRight
  (triangleOpEquivalence_functor_naturality F).symm _) ≪≫ isoWhiskerLeft
  (triangleOpEquivalence C).inverse (Functor.associator _ _ _) ≪≫ isoWhiskerLeft
  (triangleOpEquivalence C).inverse (isoWhiskerLeft _ (triangleOpEquivalence D).unitIso.symm) ≪≫
  isoWhiskerLeft _ (Functor.rightUnitor _)

/-- If `F` is triangulated, so is `F.op`.
-/
lemma isTriangulated_op [F.IsTriangulated] : F.op.IsTriangulated where
  map_distinguished T dT := by
    rw [mem_distTriang_op_iff, ← Functor.comp_obj, ← distinguished_iff_of_iso
      ((triangleOpEquivalence_inverse_naturality F).app T).unop]
    exact F.map_distinguished _ ((mem_distTriang_op_iff _).mp dT)

/-- If `F.op` is triangulated, so is `F`.
-/
lemma isTriangulated_of_op [F.op.IsTriangulated] : F.IsTriangulated where
  map_distinguished T dT := by
    have := distinguished_iff_of_iso ((triangleOpEquivalence D).unitIso.app
      (Opposite.op (F.mapTriangle.obj T))).unop
    rw [Functor.id_obj, Opposite.unop_op (F.mapTriangle.obj T)] at this
    rw [← this, Functor.comp_obj, ← mem_distTriang_op_iff, ← Functor.op_obj, ← Functor.comp_obj,
      distinguished_iff_of_iso ((triangleOpEquivalence_functor_naturality F).app (Opposite.op T))]
    apply F.op.map_distinguished
    have := distinguished_iff_of_iso ((triangleOpEquivalence C).unitIso.app (Opposite.op T)).unop
    rw [Functor.id_obj, Opposite.unop_op T] at this
    rw [← this, Functor.comp_obj, ← mem_distTriang_op_iff] at dT
    exact dT

end Functor

end CategoryTheory
