/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Triangulated.Rotate
import Mathlib.Algebra.GroupPower.NegOnePow

/-!
# The shift on the category of triangles

In this file, it is shown that if `C` is a preadditive category with
a shift by `ℤ`, then the category of triangles `Triangle C` is also
endowed with a shift. We also show that rotating triangles three times
identifies with the shift by `1`.

The shift on the category of triangles was also obtained by Adam Topaz,
Johan Commelin and Andrew Yang during the Liquid Tensor Experiment.

-/

universe v u

namespace CategoryTheory

open Category Preadditive

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasShift C ℤ]
  [∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive]

namespace Pretriangulated

attribute [local simp] Triangle.eqToHom_hom₁ Triangle.eqToHom_hom₂ Triangle.eqToHom_hom₃
  shiftFunctorAdd_zero_add_hom_app shiftFunctorAdd_add_zero_hom_app
  shiftFunctorAdd'_eq_shiftFunctorAdd shift_shiftFunctorCompIsoId_inv_app

/-- The shift functor `Triangle C ⥤ Triangle C` by `n : ℤ` sends a triangle
to the triangle obtained by shifting the objects by `n` in `C` and by
multiplying the three morphisms by `(-1)^n`. -/
@[simps]
noncomputable def Triangle.shiftFunctor (n : ℤ) : Triangle C ⥤ Triangle C where
  obj T := Triangle.mk (n.negOnePow • T.mor₁⟦n⟧') (n.negOnePow • T.mor₂⟦n⟧')
    (n.negOnePow • T.mor₃⟦n⟧' ≫ (shiftFunctorComm C 1 n).hom.app T.obj₁)
  map f :=
    { hom₁ := f.hom₁⟦n⟧'
      hom₂ := f.hom₂⟦n⟧'
      hom₃ := f.hom₃⟦n⟧'
      comm₁ := by
        dsimp
        simp only [zsmul_comp, comp_zsmul, ← Functor.map_comp, f.comm₁]
      comm₂ := by
        dsimp
        simp only [zsmul_comp, comp_zsmul, ← Functor.map_comp, f.comm₂]
      comm₃ := by
        dsimp
        rw [zsmul_comp, comp_zsmul, ← Functor.map_comp_assoc, ← f.comm₃,
          Functor.map_comp, assoc, assoc]
        erw [(shiftFunctorComm C 1 n).hom.naturality]
        rfl }

/-- The canonical isomorphism `Triangle.shiftFunctor C 0 ≅ 𝟭 (Triangle C)`. -/
@[simps!]
noncomputable def Triangle.shiftFunctorZero : Triangle.shiftFunctor C 0 ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ ((CategoryTheory.shiftFunctorZero C ℤ).app _)
      ((CategoryTheory.shiftFunctorZero C ℤ).app _) ((CategoryTheory.shiftFunctorZero C ℤ).app _)
      (by aesop_cat) (by aesop_cat) (by
        dsimp
        simp only [one_zsmul, assoc, shiftFunctorComm_zero_hom_app,
          ← Functor.map_comp, Iso.inv_hom_id_app, Functor.id_obj, Functor.map_id,
          comp_id, NatTrans.naturality, Functor.id_map]))
    (by aesop_cat)

/-- The canonical isomorphism
`Triangle.shiftFunctor C n ≅ Triangle.shiftFunctor C a ⋙ Triangle.shiftFunctor C b`
when `a + b = n`. -/
@[simps!]
noncomputable def Triangle.shiftFunctorAdd' (a b n : ℤ) (h : a + b = n) :
    Triangle.shiftFunctor C n ≅ Triangle.shiftFunctor C a ⋙ Triangle.shiftFunctor C b :=
  NatIso.ofComponents
    (fun T => Triangle.isoMk _ _
      ((CategoryTheory.shiftFunctorAdd' C a b n h).app _)
      ((CategoryTheory.shiftFunctorAdd' C a b n h).app _)
      ((CategoryTheory.shiftFunctorAdd' C a b n h).app _)
      (by
        subst h
        dsimp
        rw [zsmul_comp, NatTrans.naturality, comp_zsmul, Functor.comp_map, Functor.map_zsmul,
          comp_zsmul, smul_smul, Int.negOnePow_add, mul_comm])
      (by
        subst h
        dsimp
        rw [zsmul_comp, NatTrans.naturality, comp_zsmul, Functor.comp_map, Functor.map_zsmul,
          comp_zsmul, smul_smul, Int.negOnePow_add, mul_comm])
      (by
        subst h
        dsimp
        rw [zsmul_comp, comp_zsmul, Functor.map_zsmul, zsmul_comp, comp_zsmul, smul_smul,
          assoc, Functor.map_comp, assoc]
        erw [← NatTrans.naturality_assoc]
        simp only [shiftFunctorAdd'_eq_shiftFunctorAdd, Int.negOnePow_add,
          shiftFunctorComm_hom_app_comp_shift_shiftFunctorAdd_hom_app, add_comm a]))
    (by aesop_cat)

/-- Rotating triangles three times identifies with the shift by `1`. -/
noncomputable def rotateRotateRotateIso :
    rotate C ⋙ rotate C ⋙ rotate C ≅ Triangle.shiftFunctor C 1 :=
  NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by aesop_cat) (by aesop_cat) (by aesop_cat))
    (by aesop_cat)

/-- Rotating triangles three times backwards identifies with the shift by `-1`. -/
noncomputable def invRotateInvRotateInvRotateIso :
    invRotate C ⋙ invRotate C ⋙ invRotate C ≅ Triangle.shiftFunctor C (-1) :=
  NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by aesop_cat)
      (by aesop_cat)
      (by
        dsimp [shiftFunctorCompIsoId]
        simp [shiftFunctorComm_eq C _ _ _ (add_neg_self (1 : ℤ))]))
    (by aesop_cat)

/-- The inverse of the rotation of triangles can be expressed using a double
rotation and the shift by `-1`. -/
noncomputable def invRotateIsoRotateRotateShiftFunctorNegOne :
    invRotate C ≅ rotate C ⋙ rotate C ⋙ Triangle.shiftFunctor C (-1) :=
  calc
    invRotate C ≅ invRotate C ⋙ 𝟭 _ := (Functor.rightUnitor _).symm
    _ ≅ invRotate C ⋙ Triangle.shiftFunctor C 0 :=
          isoWhiskerLeft _ (Triangle.shiftFunctorZero C).symm
    _ ≅ invRotate C ⋙ Triangle.shiftFunctor C 1 ⋙ Triangle.shiftFunctor C (-1) :=
          isoWhiskerLeft _ (Triangle.shiftFunctorAdd' C 1 (-1) 0 (add_neg_self 1))
    _ ≅ invRotate C ⋙ (rotate C ⋙ rotate C ⋙ rotate C) ⋙ Triangle.shiftFunctor C (-1) :=
          isoWhiskerLeft _ (isoWhiskerRight (rotateRotateRotateIso C).symm _)
    _ ≅ (invRotate C ⋙ rotate C) ⋙ rotate C ⋙ rotate C ⋙ Triangle.shiftFunctor C (-1) :=
          isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
            isoWhiskerLeft _ (Functor.associator _ _ _)) ≪≫ (Functor.associator _ _ _).symm
    _ ≅ 𝟭 _ ⋙ rotate C ⋙ rotate C ⋙ Triangle.shiftFunctor C (-1) :=
          isoWhiskerRight (triangleRotation C).counitIso _
    _ ≅ _ := Functor.leftUnitor _

noncomputable instance : HasShift (Triangle C) ℤ :=
  hasShiftMk (Triangle C) ℤ
    { F := Triangle.shiftFunctor C
      zero := Triangle.shiftFunctorZero C
      add := fun a b => Triangle.shiftFunctorAdd' C a b _ rfl
      assoc_hom_app := fun a b c T => by
        ext
        all_goals
          dsimp
          rw [← shiftFunctorAdd'_assoc_hom_app a b c _ _ _ rfl rfl (add_assoc a b c)]
          dsimp only [CategoryTheory.shiftFunctorAdd']
          simp }

end Pretriangulated

end CategoryTheory
