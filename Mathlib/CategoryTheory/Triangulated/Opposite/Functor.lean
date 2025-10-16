/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import Mathlib.CategoryTheory.Adjunction.Opposites

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

assert_not_exists TwoSidedIdeal

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D)
  [F.CommShift ℤ]

open Category Limits Pretriangulated Opposite

namespace Pretriangulated.Opposite

/-- If `F` commutes with shifts, so does `F.op`, for the shifts chosen on `Cᵒᵖ` in
`CategoryTheory.Triangulated.Opposite.Basic`.
-/
noncomputable scoped instance commShiftFunctorOpInt : F.op.CommShift ℤ :=
  inferInstanceAs ((PullbackShift.functor
    (AddMonoidHom.mk' (fun (n : ℤ) => -n) (by intros; dsimp; cutsat))
      (OppositeShift.functor ℤ F)).CommShift ℤ)

variable {F}

noncomputable scoped instance commShift_natTrans_op_int {G : C ⥤ D} [G.CommShift ℤ] (τ : F ⟶ G)
    [NatTrans.CommShift τ ℤ] : NatTrans.CommShift (NatTrans.op τ) ℤ :=
  inferInstanceAs (NatTrans.CommShift (PullbackShift.natTrans
    (AddMonoidHom.mk' (fun (n : ℤ) => -n) (by intros; dsimp; cutsat))
      (OppositeShift.natTrans ℤ τ)) ℤ)

noncomputable scoped instance commShift_adjunction_op_int {G : D ⥤ C} [G.CommShift ℤ] (adj : F ⊣ G)
    [Adjunction.CommShift adj ℤ] : Adjunction.CommShift adj.op ℤ := by
  have eq : adj.op = PullbackShift.adjunction
    (AddMonoidHom.mk' (fun (n : ℤ) => -n) (by intros; dsimp; cutsat))
      (OppositeShift.adjunction ℤ adj) := by
    ext
    dsimp [PullbackShift.adjunction, NatTrans.PullbackShift.natIsoId,
      NatTrans.PullbackShift.natIsoComp, PullbackShift.functor, PullbackShift.natTrans,
      OppositeShift.adjunction, OppositeShift.natTrans, NatTrans.OppositeShift.natIsoId,
      NatTrans.OppositeShift.natIsoComp, OppositeShift.functor]
    simp only [Category.comp_id, Category.id_comp]
  rw [eq]
  exact inferInstanceAs (Adjunction.CommShift (PullbackShift.adjunction
    (AddMonoidHom.mk' (fun (n : ℤ) => -n) (by intros; dsimp; cutsat))
      (OppositeShift.adjunction ℤ adj)) ℤ)

end Pretriangulated.Opposite

namespace Functor

@[reassoc]
lemma op_commShiftIso_hom_app (X : Cᵒᵖ) (n m : ℤ) (h : n + m = 0) :
    (F.op.commShiftIso n).hom.app X =
      (F.map ((shiftFunctorOpIso C n m h).hom.app X).unop).op ≫
        ((F.commShiftIso m).inv.app X.unop).op ≫
        (shiftFunctorOpIso D n m h).inv.app (op (F.obj X.unop)) := by
  obtain rfl : m = -n := by cutsat
  rfl

@[reassoc]
lemma op_commShiftIso_inv_app (X : Cᵒᵖ) (n m : ℤ) (h : n + m = 0) :
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

@[reassoc]
lemma map_shift_unop {X Y : Cᵒᵖ} (f : X ⟶ Y) (n : ℤ) :
    F.map ((f⟦n⟧').unop) = ((F.op.commShiftIso n).inv.app Y).unop ≫
      ((F.map f.unop).op⟦n⟧').unop ≫ ((F.op.commShiftIso n).hom.app X).unop := by
  simp [shift_map_op]

@[reassoc]
lemma map_opShiftFunctorEquivalence_unitIso_hom_app_unop (X : Cᵒᵖ) (n : ℤ) :
    F.map ((opShiftFunctorEquivalence C n).unitIso.hom.app X).unop =
      (F.commShiftIso n).hom.app _ ≫
        (((F.op).commShiftIso n).inv.app X).unop⟦n⟧' ≫
        ((opShiftFunctorEquivalence D n).unitIso.hom.app (op _)).unop := by
  dsimp [opShiftFunctorEquivalence]
  simp only [map_comp, unop_comp, Quiver.Hom.unop_op, assoc,
    map_shiftFunctorCompIsoId_hom_app, commShiftIso_hom_naturality_assoc,
    op_commShiftIso_inv_app _ _ _ _ (add_neg_cancel n)]
  congr 3
  rw [← Functor.map_comp_assoc, ← unop_comp,
    Iso.inv_hom_id_app]
  dsimp
  rw [map_id, id_comp]

@[reassoc]
lemma map_opShiftFunctorEquivalence_unitIso_inv_app_unop (X : Cᵒᵖ) (n : ℤ) :
    F.map ((opShiftFunctorEquivalence C n).unitIso.inv.app X).unop =
      ((opShiftFunctorEquivalence D n).unitIso.inv.app (op (F.obj X.unop))).unop ≫
        (((F.op).commShiftIso n).hom.app X).unop⟦n⟧' ≫
        ((F.commShiftIso n).inv.app _) := by
  rw [← cancel_mono (F.map ((opShiftFunctorEquivalence C n).unitIso.hom.app X).unop),
    ← F.map_comp, ← unop_comp, Iso.hom_inv_id_app,
    map_opShiftFunctorEquivalence_unitIso_hom_app_unop, assoc, assoc,
    Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, ← unop_comp]
  simp

@[reassoc]
lemma map_opShiftFunctorEquivalence_counitIso_hom_app_unop (X : Cᵒᵖ) (n : ℤ) :
    F.map ((opShiftFunctorEquivalence C n).counitIso.hom.app X).unop =
      ((opShiftFunctorEquivalence D n).counitIso.hom.app (op (F.obj X.unop))).unop ≫
        (((F.commShiftIso n).inv.app X.unop).op⟦n⟧').unop ≫
          ((F.op.commShiftIso n).hom.app (op (X.unop⟦n⟧))).unop := by
  apply Quiver.Hom.op_inj
  dsimp [opShiftFunctorEquivalence]
  rw [assoc, F.op_commShiftIso_hom_app_assoc _ _ _ (add_neg_cancel n), map_comp,
    map_shiftFunctorCompIsoId_inv_app_assoc, op_comp, op_comp_assoc, op_comp_assoc,
    NatTrans.naturality_assoc, op_map, Iso.inv_hom_id_app_assoc, Quiver.Hom.unop_op]

@[reassoc]
lemma map_opShiftFunctorEquivalence_counitIso_inv_app_unop (X : Cᵒᵖ) (n : ℤ) :
    F.map ((opShiftFunctorEquivalence C n).counitIso.inv.app X).unop =
      ((F.op.commShiftIso n).inv.app (op (X.unop⟦n⟧))).unop ≫
        (((F.commShiftIso n).hom.app X.unop).op⟦n⟧').unop ≫
          ((opShiftFunctorEquivalence D n).counitIso.inv.app (op (F.obj X.unop))).unop := by
  rw [← cancel_epi (F.map ((opShiftFunctorEquivalence C n).counitIso.hom.app X).unop),
    ← F.map_comp, ← unop_comp, Iso.inv_hom_id_app,
    map_opShiftFunctorEquivalence_counitIso_hom_app_unop]
  dsimp
  simp only [map_id, assoc, ← Functor.map_comp_assoc,
    ← unop_comp, Iso.inv_hom_id_app_assoc, ← op_comp,
    Iso.inv_hom_id_app]
  simp

end Functor

variable [HasZeroObject C] [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] [HasZeroObject D] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]

namespace Functor

/--
If `F : C ⥤ D` commutes with shifts, this expresses the compatibility of `F.mapTriangle`
with the equivalences `Pretriangulated.triangleOpEquivalence` on `C` and `D`.
-/
@[simps!]
noncomputable def mapTriangleOpCompTriangleOpEquivalenceFunctorApp (T : Triangle C) :
    (triangleOpEquivalence D).functor.obj (op (F.mapTriangle.obj T)) ≅
      F.op.mapTriangle.obj ((triangleOpEquivalence C).functor.obj (op T)) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by
      dsimp
      simp only [map_comp, shift_map_op, map_id, comp_id, op_comp, op_unop,
        map_opShiftFunctorEquivalence_counitIso_inv_app_unop,
        opShiftFunctorEquivalence_inverse, opShiftFunctorEquivalence_functor,
        Quiver.Hom.op_unop, assoc, id_comp])

/--
If `F : C ⥤ D` commutes with shifts, this expresses the compatibility of `F.mapTriangle`
with the equivalences `Pretriangulated.triangleOpEquivalence` on `C` and `D`.
-/
noncomputable def mapTriangleOpCompTriangleOpEquivalenceFunctor :
    F.mapTriangle.op ⋙ (triangleOpEquivalence D).functor ≅
      (triangleOpEquivalence C).functor ⋙ F.op.mapTriangle :=
  NatIso.ofComponents
    (fun T ↦ F.mapTriangleOpCompTriangleOpEquivalenceFunctorApp T.unop)
    (by intros; ext <;> dsimp <;> simp only [comp_id, id_comp])

/--
If `F : C ⥤ D` commutes with shifts, this is the 2-commutative square of categories
`CategoryTheory.Functor.mapTriangleOpCompTriangleOpEquivalenceFunctor`.
-/
noncomputable instance :
    CatCommSq (F.mapTriangle.op) (triangleOpEquivalence C).functor
      (triangleOpEquivalence D).functor F.op.mapTriangle :=
  ⟨F.mapTriangleOpCompTriangleOpEquivalenceFunctor⟩

/--
Vertical inverse of the 2-commutative square of
`CategoryTheory.Functor.mapTriangleOpCompTriangleOpEquivalenceFunctor`.
-/
noncomputable instance :
    CatCommSq (F.op.mapTriangle) (triangleOpEquivalence C).inverse
      (triangleOpEquivalence D).inverse F.mapTriangle.op :=
  CatCommSq.vInv (F.mapTriangle.op) (triangleOpEquivalence C)
      (triangleOpEquivalence D) F.op.mapTriangle inferInstance

/--
If `F : C ⥤ D` commutes with shifts, this expresses the compatibility of `F.mapTriangle`
with the equivalences `Pretriangulated.triangleOpEquivalence` on `C` and `D`.
-/
noncomputable def opMapTriangleCompTriangleOpEquivalenceInverse :
    F.op.mapTriangle ⋙ (triangleOpEquivalence D).inverse ≅
      (triangleOpEquivalence C).inverse ⋙ F.mapTriangle.op :=
  CatCommSq.iso (F.op.mapTriangle) (triangleOpEquivalence C).inverse
      (triangleOpEquivalence D).inverse F.mapTriangle.op

end Functor

namespace Pretriangulated.Opposite

open Functor in
/-- If `F` is triangulated, so is `F.op`.
-/
scoped instance functor_isTriangulated_op [F.IsTriangulated] : F.op.IsTriangulated where
  map_distinguished T dT := by
    rw [mem_distTriang_op_iff]
    exact Pretriangulated.isomorphic_distinguished _
      ((F.map_distinguished _ (unop_distinguished _ dT))) _
      (((opMapTriangleCompTriangleOpEquivalenceInverse F).symm.app T).unop)

end Pretriangulated.Opposite

namespace Functor

/-- If `F.op` is triangulated, so is `F`.
-/
lemma isTriangulated_of_op [F.op.IsTriangulated] : F.IsTriangulated where
  map_distinguished T dT := by
    have := distinguished_iff_of_iso ((triangleOpEquivalence D).unitIso.app
      (Opposite.op (F.mapTriangle.obj T))).unop
    rw [Functor.id_obj, Opposite.unop_op (F.mapTriangle.obj T)] at this
    rw [← this, Functor.comp_obj, ← mem_distTriang_op_iff, ← Functor.op_obj, ← Functor.comp_obj,
      distinguished_iff_of_iso ((mapTriangleOpCompTriangleOpEquivalenceFunctor F).app
      (Opposite.op T))]
    apply F.op.map_distinguished
    have := distinguished_iff_of_iso ((triangleOpEquivalence C).unitIso.app (Opposite.op T)).unop
    rw [Functor.id_obj, Opposite.unop_op T] at this
    rw [← this, Functor.comp_obj, ← mem_distTriang_op_iff] at dT
    exact dT

open Pretriangulated.Opposite in
/-- `F` is triangulated if and only if `F.op` is triangulated.
-/
lemma op_isTriangulated_iff : F.op.IsTriangulated ↔ F.IsTriangulated :=
  ⟨fun _ ↦ F.isTriangulated_of_op, fun _ ↦ inferInstance⟩

end Functor

end CategoryTheory
