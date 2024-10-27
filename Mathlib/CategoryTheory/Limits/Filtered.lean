/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Types

/-!
# Filtered categories and limits

In this file , we show that `C` is filtered if and only if for every functor `F : J ⥤ C` from a
finite category there is some `X : C` such that `lim Hom(F·, X)` is nonempty.

Furthermore, we define the type classes `HasCofilteredLimitsOfSize` and `HasFilteredColimitsOfSize`.
-/


universe w' w v u

noncomputable section

open CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory

section NonemptyLimit

open CategoryTheory.Limits Opposite

/-- `C` is filtered if and only if for every functor `F : J ⥤ C` from a finite category there is
    some `X : C` such that `lim Hom(F·, X)` is nonempty.

    Lemma 3.1.2 of [Kashiwara2006] -/
theorem IsFiltered.iff_nonempty_limit : IsFiltered C ↔
    ∀ {J : Type v} [SmallCategory J] [FinCategory J] (F : J ⥤ C),
      ∃ (X : C), Nonempty (limit (F.op ⋙ yoneda.obj X)) := by
  rw [IsFiltered.iff_cocone_nonempty.{v}]
  refine ⟨fun h J _ _ F => ?_, fun h J _ _ F => ?_⟩
  · obtain ⟨c⟩ := h F
    exact ⟨c.pt, ⟨(limitCompYonedaIsoCocone F c.pt).inv c.ι⟩⟩
  · obtain ⟨pt, ⟨ι⟩⟩ := h F
    exact ⟨⟨pt, (limitCompYonedaIsoCocone F pt).hom ι⟩⟩

/-- `C` is cofiltered if and only if for every functor `F : J ⥤ C` from a finite category there is
    some `X : C` such that `lim Hom(X, F·)` is nonempty. -/
theorem IsCofiltered.iff_nonempty_limit : IsCofiltered C ↔
    ∀ {J : Type v} [SmallCategory J] [FinCategory J] (F : J ⥤ C),
      ∃ (X : C), Nonempty (limit (F ⋙ coyoneda.obj (op X))) := by
  rw [IsCofiltered.iff_cone_nonempty.{v}]
  refine ⟨fun h J _ _ F => ?_, fun h J _ _ F => ?_⟩
  · obtain ⟨c⟩ := h F
    exact ⟨c.pt, ⟨(limitCompCoyonedaIsoCone F c.pt).inv c.π⟩⟩
  · obtain ⟨pt, ⟨π⟩⟩ := h F
    exact ⟨⟨pt, (limitCompCoyonedaIsoCone F pt).hom π⟩⟩

end NonemptyLimit

namespace Limits

section

variable (C)

/-- Class for having all cofiltered limits of a given size. -/
@[pp_with_univ]
class HasCofilteredLimitsOfSize : Prop where
  /-- For all filtered types of size `w`, we have limits -/
  HasLimitsOfShape : ∀ (I : Type w) [Category.{w'} I] [IsCofiltered I], HasLimitsOfShape I C

/-- Class for having all filtered colimits of a given size. -/
@[pp_with_univ]
class HasFilteredColimitsOfSize : Prop where
  /-- For all filtered types of a size `w`, we have colimits -/
  HasColimitsOfShape : ∀ (I : Type w) [Category.{w'} I] [IsFiltered I], HasColimitsOfShape I C

end

instance (priority := 100) hasLimitsOfShape_of_has_cofiltered_limits
    [HasCofilteredLimitsOfSize.{w', w} C] (I : Type w) [Category.{w'} I] [IsCofiltered I] :
    HasLimitsOfShape I C :=
  HasCofilteredLimitsOfSize.HasLimitsOfShape _

instance (priority := 100) hasColimitsOfShape_of_has_filtered_colimits
    [HasFilteredColimitsOfSize.{w', w} C] (I : Type w) [Category.{w'} I] [IsFiltered I] :
    HasColimitsOfShape I C :=
  HasFilteredColimitsOfSize.HasColimitsOfShape _

end Limits

end CategoryTheory
