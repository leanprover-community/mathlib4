/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.WellOrderContinuous
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.HasIterationOfShape
import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Preservation of well order continuous functors

Given a well ordered type `J` and a functor `G : C ⥤ D`,
we define a type class `PreservesWellOrderContinuousOfShape J G`
saying that `G` preserves colimits of shape `Set.Iio j`
for any limit element `j : J`. It follows that if
`F : J ⥤ C` is well order continuous, then so is `F ⋙ G`.

-/

universe w w' v v' v'' u' u u''

namespace CategoryTheory

namespace Limits

variable {C : Type u} {D : Type u'} {E : Type u''}
  [Category.{v} C] [Category.{v'} D] [Category.{v''} E]
  (J : Type w) [LinearOrder J]

/-- A functor `G : C ⥤ D` satisfies `PreservesWellOrderContinuousOfShape J G`
if for any limit element `j` in the preordered type `J`, the functor `G`
preserves colimits of shape `Set.Iio j`. -/
class PreservesWellOrderContinuousOfShape (G : C ⥤ D) : Prop where
  preservesColimitsOfShape (j : J) (hj : Order.IsSuccLimit j) :
    PreservesColimitsOfShape (Set.Iio j) G := by infer_instance

variable {J} in
lemma preservesColimitsOfShape_of_preservesWellOrderContinuousOfShape (G : C ⥤ D)
    [PreservesWellOrderContinuousOfShape J G]
    (j : J) (hj : Order.IsSuccLimit j) :
    PreservesColimitsOfShape (Set.Iio j) G :=
  PreservesWellOrderContinuousOfShape.preservesColimitsOfShape j hj

instance (F : J ⥤ C) (G : C ⥤ D) [F.IsWellOrderContinuous]
    [PreservesWellOrderContinuousOfShape J G] :
    (F ⋙ G).IsWellOrderContinuous where
  nonempty_isColimit j hj := ⟨by
    have := preservesColimitsOfShape_of_preservesWellOrderContinuousOfShape G j hj
    exact isColimitOfPreserves G (F.isColimitOfIsWellOrderContinuous j hj)⟩

instance (G₁ : C ⥤ D) (G₂ : D ⥤ E)
    [PreservesWellOrderContinuousOfShape J G₁]
    [PreservesWellOrderContinuousOfShape J G₂] :
    PreservesWellOrderContinuousOfShape J (G₁ ⋙ G₂) where
  preservesColimitsOfShape j hj := by
    have := preservesColimitsOfShape_of_preservesWellOrderContinuousOfShape G₁ j hj
    have := preservesColimitsOfShape_of_preservesWellOrderContinuousOfShape G₂ j hj
    infer_instance

instance [HasIterationOfShape J C] (K : Type*) [Category K] (X : K) :
    PreservesWellOrderContinuousOfShape J ((evaluation K C).obj X) where
  preservesColimitsOfShape j hj := by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

instance [HasIterationOfShape J C] :
    PreservesWellOrderContinuousOfShape J (Arrow.leftFunc : _ ⥤ C) where
  preservesColimitsOfShape j hj := by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

instance [HasIterationOfShape J C] :
    PreservesWellOrderContinuousOfShape J (Arrow.rightFunc : _ ⥤ C) where
  preservesColimitsOfShape j hj := by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

end Limits

end CategoryTheory
