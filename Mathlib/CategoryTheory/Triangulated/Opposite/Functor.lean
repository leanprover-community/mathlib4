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

lemma oppositeCommShiftInt_iso_eq (n m : ℤ) (h : n + m = 0) :
    Functor.commShiftIso (F := F.op) n = isoWhiskerRight (shiftFunctorOpIso C n m h) F.op ≪≫
      NatIso.op (Functor.CommShift.iso (F := F) m).symm ≪≫
        isoWhiskerLeft F.op (shiftFunctorOpIso D n m h).symm := by
  ext
  rw [@commShiftPullback_iso_eq Cᵒᵖ _ ℤ ℤ _ _  (AddMonoidHom.mk' (fun (n : ℤ) => -n)
    (by intros; dsimp; omega)) (inferInstance : HasShift (OppositeShift C ℤ) ℤ)
    (OppositeShift D ℤ) _ (inferInstance : HasShift (OppositeShift D ℤ) ℤ) F.op
    (commShiftOp F ℤ) n m (eq_neg_of_add_eq_zero_right h)]
  rfl

lemma map_opShiftFunctorEquivalence_unit_hom_app (F : C ⥤ D) [F.CommShift ℤ] (X : Cᵒᵖ) (n : ℤ) :
    F.op.map ((opShiftFunctorEquivalence C n).unitIso.hom.app X) =
      (opShiftFunctorEquivalence D n).unitIso.hom.app (F.op.obj X) ≫
        (shiftFunctor D n).op.map (((F.op).commShiftIso n).inv.app X) ≫
          ((F.commShiftIso n).hom.app _).op := by
  rw [oppositeCommShiftInt_iso_eq F n (-n) (by simp)]
  simp only [id_obj, op_obj, opShiftFunctorEquivalence, comp_obj, Iso.trans_hom, NatIso.op_hom,
    isoWhiskerRight_hom, Iso.symm_hom, NatTrans.comp_app, NatTrans.op_app, whiskerRight_app, op_map,
    unop_comp, Quiver.Hom.unop_op, map_comp, map_shiftFunctorCompIsoId_hom_app,
    commShiftIso_hom_naturality_assoc, op_comp, assoc, Iso.trans_inv, isoWhiskerLeft_inv,
    Iso.symm_inv, NatIso.op_inv, isoWhiskerRight_inv, whiskerLeft_app]
  slice_rhs 2 3 => rw [← op_comp, ← Functor.map_comp, ← unop_comp, Iso.inv_hom_id_app]
  simp only [Functor.op_obj, unop_id, Functor.map_id, op_id, id_comp, assoc]
  rfl

lemma map_opShiftFunctorEquivalence_unit_inv_app (F : C ⥤ D) [F.CommShift ℤ] (X : Cᵒᵖ) (n : ℤ) :
    F.op.map ((opShiftFunctorEquivalence C n).unitIso.inv.app X) = ((F.commShiftIso n).inv.app _).op
      ≫ (shiftFunctor D n).op.map (((F.op).commShiftIso n).hom.app X) ≫
        (opShiftFunctorEquivalence D n).unitIso.inv.app (F.op.obj X) := by
  rw [oppositeCommShiftInt_iso_eq F n (-n) (by simp)]
  simp only [opShiftFunctorEquivalence, comp_obj, op_obj, id_obj, Iso.trans_inv,
    isoWhiskerRight_inv, Iso.symm_inv, NatIso.op_inv, NatTrans.comp_app, whiskerRight_app, op_map,
    NatTrans.op_app, unop_comp, Quiver.Hom.unop_op, map_comp, map_shiftFunctorCompIsoId_inv_app,
    assoc, op_comp, Iso.trans_hom, isoWhiskerRight_hom, NatIso.op_hom, Iso.symm_hom,
    isoWhiskerLeft_hom, whiskerLeft_app]
  slice_rhs 4 5 => rw [← op_comp, ← Functor.map_comp, ← unop_comp, Iso.inv_hom_id_app]
  simp only [Functor.op_obj, unop_id, Functor.map_id, op_id, id_comp]
  slice_rhs 1 2 => rw [← op_comp]
                   change ((F ⋙ shiftFunctor D n).map ((shiftFunctorOpIso C n (-n)
                     (by simp)).hom.app X).unop ≫ (F.commShiftIso n).inv.app _).op
                   rw [(F.commShiftIso n).inv.naturality]
  simp only [Functor.op_obj, Functor.comp_obj, Functor.comp_map, op_comp, assoc]
  rfl

lemma map_opShiftFunctorEquivalence_counit_hom_app (F : C ⥤ D) [F.CommShift ℤ] (X : Cᵒᵖ) (n : ℤ) :
    F.op.map ((opShiftFunctorEquivalence C n).counitIso.hom.app X) = (F.op.commShiftIso n).hom.app _
      ≫ (shiftFunctor Dᵒᵖ n).map ((F.commShiftIso n).inv.app _).op ≫
        (opShiftFunctorEquivalence D n).counitIso.hom.app (F.op.obj X) := by
  rw [oppositeCommShiftInt_iso_eq F n (-n) (by simp)]
  simp [opShiftFunctorEquivalence]
  rfl

lemma map_opShiftFunctorEquivalence_counit_inv_app (F : C ⥤ D) [F.CommShift ℤ] (X : Cᵒᵖ) (n : ℤ) :
    F.op.map ((opShiftFunctorEquivalence C n).counitIso.inv.app X) =
      (opShiftFunctorEquivalence D n).counitIso.inv.app (F.op.obj X) ≫
        (shiftFunctor Dᵒᵖ n).map ((F.commShiftIso n).hom.app _).op ≫
          (F.op.commShiftIso n).inv.app _ := by
  rw [oppositeCommShiftInt_iso_eq F n (-n) (by simp)]
  simp [opShiftFunctorEquivalence]
  rfl

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
    conv_rhs => congr; change F.op.map ((opShiftFunctorEquivalence C 1).counitIso.inv.app
                  (Opposite.op (Opposite.unop T).obj₁))
    rw [map_opShiftFunctorEquivalence_counit_inv_app]
    slice_rhs 3 4 => change (F.op.commShiftIso 1).inv.app _ ≫
                       (shiftFunctor Cᵒᵖ 1 ⋙ F.op).map (Opposite.unop T).mor₃.op
                     rw [← (F.op.commShiftIso (1 : ℤ)).inv.naturality]
    slice_rhs 4 5 => rw [Iso.inv_hom_id_app]
    simp only [opShiftFunctorEquivalence_inverse, opShiftFunctorEquivalence_functor, Functor.op_obj,
      Functor.comp_obj, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op, comp_id]
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
lemma isTriangulatedOp_of_isTriangulated [F.IsTriangulated] : F.op.IsTriangulated where
  map_distinguished T dT := by
    rw [mem_distTriang_op_iff, ← Functor.comp_obj, ← distinguished_iff_of_iso
      ((triangleOpEquivalence_inverse_naturality F).app T).unop]
    exact F.map_distinguished _ ((mem_distTriang_op_iff _).mp dT)

/-- If `F.op` is triangulated, so is `F`.
-/
lemma isTriangulated_of_isTriangulatedOp [F.op.IsTriangulated] : F.IsTriangulated where
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
