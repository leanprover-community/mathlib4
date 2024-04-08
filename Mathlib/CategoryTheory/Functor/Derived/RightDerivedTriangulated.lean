import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
import Mathlib.CategoryTheory.Triangulated.Functor

namespace CategoryTheory

open Category Limits Pretriangulated

namespace Functor

variable {C D H : Type*} [Category C] [Category D] [Category H]
  (RF : H ⥤ D) {F : C ⥤ D} {L : C ⥤ H}
  (α : F ⟶ L ⋙ RF) (W : MorphismProperty C)
  [L.IsLocalization W]
  [RF.IsRightDerivedFunctor α W]
  [HasShift C ℤ] [HasShift D ℤ] [HasShift H ℤ]
  [HasZeroObject C] [HasZeroObject D] [HasZeroObject H]
  [Preadditive C] [Preadditive D] [Preadditive H]
  [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [∀ (n : ℤ), (shiftFunctor H n).Additive]
  [Pretriangulated C] [Pretriangulated D] [Pretriangulated H]
  [F.CommShift ℤ] [L.CommShift ℤ] [RF.CommShift ℤ]
  [NatTrans.CommShift α ℤ] [F.IsTriangulated] [L.IsTriangulated]

lemma isTriangulated_of_isRightDerivedFunctor
    (h : ∀ ⦃X Y : H⦄ (f : X ⟶ Y), ∃ (T : Triangle C) (_ : T ∈ distTriang C)
      (_ : IsIso (α.app T.obj₁)) (_ : IsIso (α.app T.obj₂)) (_ : IsIso (α.app T.obj₃)),
      Nonempty (Arrow.mk (L.map T.mor₁) ≅ Arrow.mk f)): RF.IsTriangulated where
  map_distinguished T hT := by
    suffices ∃ (T' : Triangle H) (_ : T ≅ T'), RF.mapTriangle.obj T' ∈ distTriang D by
      obtain ⟨T', e, hT'⟩ := this
      exact isomorphic_distinguished _ hT' _ (RF.mapTriangle.mapIso e)
    obtain ⟨T', hT', h₁, h₂, h₃, ⟨e⟩⟩ := h T.mor₁
    refine ⟨L.mapTriangle.obj T', Iso.symm (isoTriangleOfIso₁₂ _ _
        (L.map_distinguished T' hT') hT (Arrow.leftFunc.mapIso e)
        (Arrow.rightFunc.mapIso e) (by simp)),
      isomorphic_distinguished _ (F.map_distinguished T' hT') _
        (((mapTriangleCompIso L RF).symm.app T') ≪≫ Iso.symm
          (Triangle.isoMk _ _ (asIso (α.app _)) (asIso (α.app _)) (asIso (α.app _))
            (by simp) (by simp) ?_))⟩
    dsimp
    rw [assoc]
    erw [← NatTrans.naturality_assoc]
    rw [NatTrans.CommShift.comm_app]

end Functor

end CategoryTheory
