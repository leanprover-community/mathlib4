/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.GuitartExact.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-!
# Guitart exact squares and Kan extensions

Given a Guitart exact square `w : T ⋙ R ⟶ L ⋙ B`,
```
     T
  C₁ ⥤ C₂
L |     | R
  v     v
  C₃ ⥤ C₄
     B
```
we show that an extension `F' : C₄ ⥤ D` of `F : C₂ ⥤ D` along `R`
is a pointwise left Kan extension at `B.obj X₃` iff
the composition `T ⋙ F'` is a pointwise left Kan extension at `X₃`
of `B ⋙ F'`.

When suitable (pointwise) left Kan extensions exist, we also show that
the natural transformation of functors `(C₂ ⥤ D) ⥤ C₃ ⥤ D`
`(whiskeringLeft C₁ C₂ D).obj T ⋙ L.lan ⟶ R.lan ⋙ (whiskeringLeft C₃ C₄ D).obj B`
induced by a Guitart exact square `w` is an isomorphism.

## References

* https://ncatlab.org/nlab/show/exact+square

-/

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory

open Limits

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄} {D : Type u₅}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  [Category.{v₅} D]

namespace Functor.LeftExtension

variable {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
  {F : C₂ ⥤ D} (E : R.LeftExtension F)

/-- Given a square `w : TwoSquare T L R B` (consisting of a natural transformation
`T ⋙ R ⟶ L ⋙ B`), this is the obvious map `R.LeftExtension F → L.LeftExtension (T ⋙ F)`
obtained by the precomposition with `B` and the postcomposition with `w`. -/
abbrev compTwoSquare (w : TwoSquare T L R B) : L.LeftExtension (T ⋙ F) :=
  LeftExtension.mk (B ⋙ E.right)
    (whiskerLeft _ E.hom ≫ (associator _ _ _).inv ≫
      whiskerRight w.natTrans _ ≫ (associator _ _ _).hom)

/-- If `w : TwoSquare T L R B` is a Guitart exact square, and `E` is a left extension
of `F` along `R`, then `E` is a pointwise left Kan extension of `F` along `R` at
`B.obj X₃` iff `E.compTwoSquare w` is a pointwise left Kan extension
of `T ⋙ F` along `L` at `X₃`. -/
noncomputable def isPointwiseLeftKanExtensionAtCompTwoSquareEquiv
    (w : TwoSquare T L R B) (X₃ : C₃) [Final (w.costructuredArrowRightwards X₃)] :
    (E.compTwoSquare w).IsPointwiseLeftKanExtensionAt X₃ ≃
      E.IsPointwiseLeftKanExtensionAt (B.obj X₃) := by
  refine Equiv.trans ?_ (Final.isColimitWhiskerEquiv (w.costructuredArrowRightwards X₃) _)
  exact IsColimit.equivIsoColimit (Cocones.ext (Iso.refl _))

lemma nonempty_isPointwiseLeftKanExtensionAt_compTwoSquare_iff
    (w : TwoSquare T L R B) (X₃ : C₃) [Final (w.costructuredArrowRightwards X₃)] :
    Nonempty ((E.compTwoSquare w).IsPointwiseLeftKanExtensionAt X₃) ↔
      Nonempty (E.IsPointwiseLeftKanExtensionAt (B.obj X₃)) :=
  (E.isPointwiseLeftKanExtensionAtCompTwoSquareEquiv w _).nonempty_congr

variable {E} in
/-- If `w : TwoSquare T L R B` is a Guitart exact square, and `E` is a pointwise
left Kan extension of `F` along `R`, then `E.compTwoSquare w` is a pointwise left
Kan extension of `T ⋙ F` along `L`. -/
noncomputable def IsPointwiseLeftKanExtension.compTwoSquare
    (h : E.IsPointwiseLeftKanExtension) (w : TwoSquare T L R B) [w.GuitartExact] :
    (E.compTwoSquare w).IsPointwiseLeftKanExtension :=
  fun X₃ ↦ (E.isPointwiseLeftKanExtensionAtCompTwoSquareEquiv w X₃).symm (h _)

/-- If `w : TwoSquare T L R B` is a Guitart exact square, with `B` essentially surjective,
and `E` is a left extension of `F` along `R`, then `E` is a pointwise
left Kan extension of `F` along `R` provided `E.compTwoSquare w` is a pointwise left
Kan extension of `T ⋙ F` along `L`. -/
noncomputable def isPointwiseLeftKanExtensionOfCompTwoSquare
    (w : TwoSquare T L R B) [w.GuitartExact] [B.EssSurj]
    (h : (E.compTwoSquare w).IsPointwiseLeftKanExtension) :
    E.IsPointwiseLeftKanExtension :=
  fun X₄ ↦ E.isPointwiseLeftKanExtensionAtOfIso'
    (E.isPointwiseLeftKanExtensionAtCompTwoSquareEquiv w _ (h (B.objPreimage X₄)))
    (B.objObjPreimageIso X₄)

/-- If `w : TwoSquare T L R B` is a Guitart exact square, with `B` essentially surjective,
and `E` is a left extension of `F` along `R`, then `E` is a pointwise left Kan extension
of `F` along `R` iff `E.compTwoSquare w` is a pointwise left Kan extension
of `T ⋙ F` along `L`. -/
noncomputable def isPointwiseLeftKanExtensionEquivOfGuitartExact
    (w : TwoSquare T L R B) [w.GuitartExact] [B.EssSurj] :
    (E.compTwoSquare w).IsPointwiseLeftKanExtension ≃
      E.IsPointwiseLeftKanExtension where
  toFun h := E.isPointwiseLeftKanExtensionOfCompTwoSquare w h
  invFun h := h.compTwoSquare w
  left_inv _ := by subsingleton
  right_inv _ := by subsingleton

end Functor.LeftExtension

namespace TwoSquare

variable {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
   (w : TwoSquare T L R B)

include w

lemma hasPointwiseLeftKanExtensionAt_iff
    (F : C₂ ⥤ D) (X₃ : C₃) [(w.costructuredArrowRightwards X₃).Final] :
    L.HasPointwiseLeftKanExtensionAt (T ⋙ F) X₃ ↔
      R.HasPointwiseLeftKanExtensionAt F (B.obj X₃) := by
  dsimp [Functor.HasPointwiseLeftKanExtensionAt]
  rw [← Functor.Final.hasColimit_comp_iff (w.costructuredArrowRightwards X₃)]
  rfl

lemma hasPointwiseLeftKanExtension_iff [w.GuitartExact] [B.EssSurj] (F : C₂ ⥤ D) :
    L.HasPointwiseLeftKanExtension (T ⋙ F) ↔
      R.HasPointwiseLeftKanExtension F := by
  dsimp [Functor.HasPointwiseLeftKanExtension]
  simp only [hasPointwiseLeftKanExtensionAt_iff w]
  refine ⟨fun h X₄ ↦ ?_, fun h _ ↦ h _⟩
  rw [← Functor.hasPointwiseLeftKanExtensionAt_iff_of_iso _ _ (B.objObjPreimageIso X₄)]
  apply h

lemma hasPointwiseLeftKanExtension [w.GuitartExact]
    (F : C₂ ⥤ D) [R.HasPointwiseLeftKanExtension F] :
    L.HasPointwiseLeftKanExtension (T ⋙ F) :=
  ((R.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension
    F).compTwoSquare w).hasPointwiseLeftKanExtension

lemma hasLeftKanExtension [w.GuitartExact]
    (F : C₂ ⥤ D) [R.HasPointwiseLeftKanExtension F] :
    L.HasLeftKanExtension (T ⋙ F) := by
  have := w.hasPointwiseLeftKanExtension F
  infer_instance

section

open Functor

section

variable [∀ (F : C₁ ⥤ D), L.HasLeftKanExtension F] [∀ (F : C₂ ⥤ D), R.HasLeftKanExtension F]

/-- The base change natural transformation for left Kan extensions associated to
a 2-square. -/
@[simps -isSimp]
noncomputable def lanBaseChange :
    (whiskeringLeft C₁ C₂ D).obj T ⋙ L.lan ⟶ R.lan ⋙ (whiskeringLeft C₃ C₄ D).obj B where
  app F :=
    ((L.lanAdjunction D).homEquiv _ _).symm
      ((LeftExtension.mk _ (R.lanUnit.app F)).compTwoSquare w).hom
  naturality {F₁ F₂} τ := by
    dsimp
    refine (Adjunction.homEquiv_naturality_left_symm ..).symm.trans
      (Eq.trans ?_ (Adjunction.homEquiv_naturality_right_symm ..))
    congr 1
    ext X
    have := R.lanUnit.naturality_app (T.obj X) τ
    simp [reassoc_of% this]

lemma isIso_lanBaseChange_app_iff (F : C₂ ⥤ D) :
    IsIso (w.lanBaseChange.app F) ↔
      IsLeftKanExtension _ ((LeftExtension.mk _ (R.lanUnit.app F)).compTwoSquare w).hom := by
  rw [lanBaseChange_app, isIso_lanAdjunction_homEquiv_symm_iff]
  simp

instance isIso_lanBaseChange_app (F : C₂ ⥤ D)
    [R.HasPointwiseLeftKanExtension F] [w.GuitartExact] :
    IsIso (w.lanBaseChange.app F) := by
  rw [isIso_lanBaseChange_app_iff]
  let hF := isPointwiseLeftKanExtensionOfIsLeftKanExtension (F := F) _ (R.lanUnit.app F)
  exact (hF.compTwoSquare w).isLeftKanExtension

end

instance [∀ (F : C₁ ⥤ D), L.HasLeftKanExtension F]
    [∀ (F : C₂ ⥤ D), R.HasPointwiseLeftKanExtension F] [w.GuitartExact] :
    IsIso (w.lanBaseChange (D := D)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  infer_instance

end

end TwoSquare

end CategoryTheory
