/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Right derived functors are triangulated

Let `F : C ⥤ D`, `L : C ⥤ H`, `F' : H ⥤ D` be functors between
pretriangulated categories. Let `α : F ⟶ L ⋙ F'` be a natural transformation.
We show that `F'` is triangulated if `F`, `L`, `F'` and `α` commute with
shifts, and for any morphism `f` in `H`, there exists a distinguished
triangle `T` in `C` such that `Arrow.mk (L.map T.mor₁) ≅ Arrow.mk f`,
and `α.app T.obj₁`, `α.app T.obj₂`, `α.app T.obj₃` are isomorphisms.

-/

namespace CategoryTheory.Functor

open Limits Pretriangulated

variable {C D H : Type*} [Category* C] [Category* D] [Category* H]
  (F' : H ⥤ D) {F : C ⥤ D} {L : C ⥤ H}
  [HasShift C ℤ] [HasShift D ℤ] [HasShift H ℤ]
  [HasZeroObject C] [HasZeroObject D] [HasZeroObject H]
  [Preadditive C] [Preadditive D] [Preadditive H]
  [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [∀ (n : ℤ), (shiftFunctor H n).Additive]
  [Pretriangulated C] [Pretriangulated D] [Pretriangulated H]
  [F.CommShift ℤ] [L.CommShift ℤ] [F'.CommShift ℤ]
  [F.IsTriangulated] [L.IsTriangulated]

set_option backward.isDefEq.respectTransparency false in
public lemma isTriangulated_of_leftExtension
    (α : F ⟶ L ⋙ F') [NatTrans.CommShift α ℤ]
    (h : ∀ ⦃X Y : H⦄ (f : X ⟶ Y), ∃ (T : Triangle C) (_ : T ∈ distTriang C)
      (_ : IsIso (α.app T.obj₁)) (_ : IsIso (α.app T.obj₂)) (_ : IsIso (α.app T.obj₃)),
      Nonempty (Arrow.mk (L.map T.mor₁) ≅ Arrow.mk f)) : F'.IsTriangulated where
  map_distinguished T hT := by
    suffices ∃ (T' : Triangle H) (_ : T ≅ T'), F'.mapTriangle.obj T' ∈ distTriang D by
      obtain ⟨T', e, hT'⟩ := this
      exact isomorphic_distinguished _ hT' _ (F'.mapTriangle.mapIso e)
    obtain ⟨T', hT', h₁, h₂, h₃, ⟨e⟩⟩ := h T.mor₁
    refine ⟨L.mapTriangle.obj T', (isoTriangleOfIso₁₂ _ _
        (L.map_distinguished T' hT') hT (Arrow.leftFunc.mapIso e)
        (Arrow.rightFunc.mapIso e) (by simp)).symm,
      isomorphic_distinguished _ (F.map_distinguished T' hT') _
        (((mapTriangleCompIso L F').symm.app T') ≪≫ Iso.symm
          (Triangle.isoMk _ _ (asIso (α.app _)) (asIso (α.app _)) (asIso (α.app _))
            (by simp) (by simp) ?_))⟩
    simp [NatTrans.shift_app_comm, ← dsimp% α.naturality_assoc, -NatTrans.naturality_assoc]

end CategoryTheory.Functor
