import Mathlib.CategoryTheory.Triangulated.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Triangulated.TriangleShift

namespace CategoryTheory

open Category Limits Pretriangulated Preadditive

namespace Functor

variable {C D E : Type _} [Category C] [Category D] [Category E]
  [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
  [Preadditive C] [Preadditive D] [Preadditive E]
  (F : C ⥤ D) [F.HasCommShift ℤ] (G : D ⥤ E) [G.HasCommShift ℤ]

@[simps]
def mapTriangle : Pretriangulated.Triangle C ⥤ Pretriangulated.Triangle D where
  obj T := Pretriangulated.Triangle.mk (F.map T.mor₁) (F.map T.mor₂)
    (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁)
  map f :=
    { hom₁ := F.map f.hom₁
      hom₂ := F.map f.hom₂
      hom₃ := F.map f.hom₃
      comm₁ := by dsimp ; simp only [← F.map_comp, f.comm₁]
      comm₂ := by dsimp ; simp only [← F.map_comp, f.comm₂]
      comm₃ := by
        dsimp [Functor.comp]
        simp only [Category.assoc, ← NatTrans.naturality,
          ← F.map_comp_assoc, f.comm₃] }

attribute [local simp] map_zsmul comp_zsmul zsmul_comp

-- TODO : extend this to [(F.mapTriangle).HasCommShift ℤ]

noncomputable def mapTriangleCommShiftIso [F.Additive] (n : ℤ) :
    Triangle.shiftFunctor C n ⋙ F.mapTriangle ≅ F.mapTriangle ⋙ Triangle.shiftFunctor D n :=
  NatIso.ofComponents (fun T => Triangle.isoMk _ _
    ((F.commShiftIso n).app _) ((F.commShiftIso n).app _) ((F.commShiftIso n).app _)
    (by aesop_cat)
    (by aesop_cat)
    (by
      dsimp
      simp only [map_zsmul, map_comp, zsmul_comp, assoc, comp_zsmul,
        ← F.commShiftIso_hom_naturality_assoc]
      congr 2
      rw [F.map_shiftFunctorComm T.obj₁ 1 n]
      simp only [assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
      dsimp
      simp only [Functor.map_id, comp_id]))
    (by aesop_cat)


@[simps!]
def mapTriangleRotateIso [F.Additive] :
    F.mapTriangle ⋙ Pretriangulated.rotate D ≅
      Pretriangulated.rotate C ⋙ F.mapTriangle :=
    NatIso.ofComponents
      (fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) ((F.commShiftIso (1 : ℤ)).symm.app _)
        (by aesop_cat) (by aesop_cat) (by aesop_cat))
      (by aesop_cat)

@[simps!]
noncomputable def mapTriangleInvRotateIso [F.Additive] :
    F.mapTriangle ⋙ Pretriangulated.invRotate D ≅
      Pretriangulated.invRotate C ⋙ F.mapTriangle :=
    NatIso.ofComponents
      (fun T => Triangle.isoMk _ _ ((F.commShiftIso (-1 : ℤ)).symm.app _) (Iso.refl _) (Iso.refl _)
        (by aesop_cat) (by aesop_cat) (by aesop_cat)) (by aesop_cat)

end Functor
