import Mathlib.CategoryTheory.Triangulated.Rotate
import Mathlib.Algebra.GroupPower.NegOnePow

open CategoryTheory Category Preadditive

variable (C : Type _) [Category C] [Preadditive C] [HasShift C ℤ]
  [∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive]

namespace CategoryTheory

namespace Pretriangulated

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
        congr 2
        exact ((shiftFunctorComm C 1 n).hom.naturality f.hom₁).symm }

@[simps!]
noncomputable def Triangle.shiftFunctorZero : Triangle.shiftFunctor C 0 ≅ 𝟭 _ :=
  NatIso.ofComponents (fun T => Triangle.isoMk _ _ ((CategoryTheory.shiftFunctorZero C ℤ).app _)
      ((CategoryTheory.shiftFunctorZero C ℤ).app _)
      ((CategoryTheory.shiftFunctorZero C ℤ).app _) (by aesop_cat) (by aesop_cat) (by
        dsimp
        rw [one_zsmul, assoc, shiftFunctorComm_zero_hom_app, assoc, ← Functor.map_comp,
          Iso.inv_hom_id_app]
        dsimp
        rw [Functor.map_id, comp_id, NatTrans.naturality]
        rfl)) (by aesop_cat)

@[simps!]
noncomputable def Triangle.shiftFunctorAdd' (a b n : ℤ) (h : a + b = n) :
    Triangle.shiftFunctor C n ≅ Triangle.shiftFunctor C a ⋙ Triangle.shiftFunctor C b :=
  NatIso.ofComponents (fun T => Triangle.isoMk _ _
      ((CategoryTheory.shiftFunctorAdd' C a b n h).app _)
      ((CategoryTheory.shiftFunctorAdd' C a b n h).app _)
      ((CategoryTheory.shiftFunctorAdd' C a b n h).app _)
      (by
        subst n
        dsimp
        rw [zsmul_comp, NatTrans.naturality, comp_zsmul, Functor.comp_map, Functor.map_zsmul,
          comp_zsmul, smul_smul, Int.negOnePow_add, mul_comm a.negOnePow])
      (by
        subst n
        dsimp
        rw [zsmul_comp, NatTrans.naturality, comp_zsmul, Functor.comp_map, Functor.map_zsmul,
          comp_zsmul, smul_smul, Int.negOnePow_add, mul_comm a.negOnePow])
      (by
        subst h
        dsimp
        rw [zsmul_comp, comp_zsmul, Functor.map_zsmul, zsmul_comp, comp_zsmul, smul_smul,
          assoc, Functor.map_comp, assoc]
        erw [← NatTrans.naturality_assoc]
        simp only [shiftFunctorAdd'_eq_shiftFunctorAdd,
          shiftFunctorComm_hom_app_comp_shift_shiftFunctorAdd_hom_app,
          add_comm a, Int.negOnePow_add]))
    (by aesop_cat)

noncomputable def rotateRotateRotateIso :
    rotate C ⋙ rotate C ⋙ rotate C ≅ Triangle.shiftFunctor C 1 :=
  NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by aesop_cat) (by aesop_cat) (by aesop_cat)) (by aesop_cat)

noncomputable def invRotateIsoRotateRotateShiftFunctorNegOne :
    invRotate C ≅ rotate C ⋙ rotate C ⋙ Triangle.shiftFunctor C (-1) :=
  (Functor.rightUnitor _).symm ≪≫
    isoWhiskerLeft _ ((Triangle.shiftFunctorZero C).symm ≪≫
      Triangle.shiftFunctorAdd' C 1 (-1) 0 (add_neg_self 1) ≪≫
      isoWhiskerRight (rotateRotateRotateIso C).symm _) ≪≫ (by exact Iso.refl _) ≪≫
    isoWhiskerRight ((triangleRotation C).counitIso) _ ≪≫ Functor.leftUnitor _

attribute [local simp] shift_shiftFunctorCompIsoId_inv_app

noncomputable def invRotateInvRotateInvRotateIso :
  invRotate C ⋙ invRotate C ⋙ invRotate C ≅ Triangle.shiftFunctor C (-1) :=
  NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by aesop_cat)
      (by aesop_cat)
      (by
        dsimp [shiftFunctorCompIsoId]
        simp [shiftFunctorComm_eq C _ _ _ (add_neg_self (1 : ℤ))])) (by aesop_cat)

namespace Triangle

attribute [local simp] Triangle.eqToHom_hom₁
  Triangle.eqToHom_hom₂ Triangle.eqToHom_hom₃
  shiftFunctorAdd'_eq_shiftFunctorAdd
  shiftFunctorAdd_zero_add_hom_app
  shiftFunctorAdd_add_zero_hom_app

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

@[simp]
lemma shiftFunctor_eq (n : ℤ) :
    CategoryTheory.shiftFunctor (Triangle C) n = shiftFunctor C n := rfl

@[simp]
lemma shiftFunctorZero_eq :
    CategoryTheory.shiftFunctorZero (Triangle C) ℤ = Triangle.shiftFunctorZero C :=
  ShiftMkCore.shiftFunctorZero_eq _

@[simp]
lemma shiftFunctorAdd_eq (a b : ℤ) :
    CategoryTheory.shiftFunctorAdd (Triangle C) a b =
      Triangle.shiftFunctorAdd' C a b _ rfl :=
  ShiftMkCore.shiftFunctorAdd_eq _ _ _

@[simp]
lemma shiftFunctorAdd'_eq (a b c : ℤ) (h : a + b = c) :
    CategoryTheory.shiftFunctorAdd' (Triangle C) a b c h =
      Triangle.shiftFunctorAdd' C a b c h := by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd]
  apply shiftFunctorAdd_eq


end Triangle

end Pretriangulated

end CategoryTheory
