import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Shift.HasCommShift
import Mathlib.CategoryTheory.Triangulated.TriangleShift

namespace CategoryTheory

open Category Limits Pretriangulated Preadditive ZeroObject

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

attribute [local simp] commShiftIso_comp_hom_app

@[simps!]
def mapTriangleCompIso : (F ⋙ G).mapTriangle ≅ F.mapTriangle ⋙ G.mapTriangle :=
  NatIso.ofComponents (fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by aesop_cat) (by aesop_cat) (by aesop_cat)) (by aesop_cat)

variable [HasZeroObject C] [HasZeroObject D]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

class IsTriangulated : Prop where
  map_distinguished : ∀ (T : Triangle C), (T ∈ distTriang C) → F.mapTriangle.obj T ∈ distTriang D

lemma map_distinguished [F.IsTriangulated] (T : Triangle C) (hT : T ∈ distTriang C) :
    F.mapTriangle.obj T ∈ distTriang D :=
  IsTriangulated.map_distinguished _ hT

namespace IsTriangulated

variable [F.IsTriangulated]

noncomputable def map_zero_object : F.obj 0 ≅ 0 := by
  apply IsZero.isoZero
  apply isZero_of_isIso_mor₁ _ (F.map_distinguished _ (contractible_distinguished (0 : C)))
  dsimp
  infer_instance

instance : PreservesZeroMorphisms F := by
  have h : 𝟙 (F.obj 0) = 0 := by
    rw [← IsZero.iff_id_eq_zero]
    apply isZero_of_isIso_mor₁ _ (F.map_distinguished _ (contractible_distinguished (0 : C)))
    dsimp
    infer_instance
  refine' ⟨fun X Y => _⟩
  have : (0 : X ⟶ Y) = 0 ≫ 𝟙 0 ≫ 0 := by simp
  rw [this, F.map_comp, F.map_comp, F.map_id, h, zero_comp, comp_zero]

noncomputable instance : PreservesLimitsOfShape (Discrete WalkingPair) F := by
  suffices ∀ (X₁ X₃ : C), IsIso (prodComparison F X₁ X₃) by
    have := fun (X₁ X₃ : C) => PreservesLimitPair.ofIsoProdComparison F X₁ X₃
    exact ⟨fun {K} => preservesLimitOfIsoDiagram F (diagramIsoPair K).symm⟩
  intro X₁ X₃
  let φ : F.mapTriangle.obj (binaryProductTriangle X₁ X₃) ⟶
      binaryProductTriangle (F.obj X₁) (F.obj X₃) :=
    { hom₁ := 𝟙 _
      hom₂ := prodComparison F X₁ X₃
      hom₃ := 𝟙 _
      comm₁ := by
        dsimp
        ext
        . simp only [assoc, prodComparison_fst, prod.comp_lift, comp_id, comp_zero,
            limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_left, BinaryFan.mk_fst,
            ← F.map_comp, F.map_id]
        . simp only [assoc, prodComparison_snd, prod.comp_lift, comp_id, comp_zero,
            limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_right, BinaryFan.mk_snd,
            ← F.map_comp, F.map_zero]
      comm₂ := by simp
      comm₃ := by simp }
  exact isIso₂_of_isIso₁₃ φ (F.map_distinguished _ (binaryProductTriangle_distinguished X₁ X₃))
    (binaryProductTriangle_distinguished _ _)
    (by dsimp ; infer_instance) (by dsimp ; infer_instance)

instance : F.Additive := F.additive_of_preserves_binary_products

end IsTriangulated

end Functor

end CategoryTheory
