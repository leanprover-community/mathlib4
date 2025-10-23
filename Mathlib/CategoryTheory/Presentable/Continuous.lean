/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.Presheaf
import Mathlib.CategoryTheory.MorphismProperty.IsSmall
import Mathlib.CategoryTheory.SmallRepresentatives
import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-!
# `κ`-continuous functors

Given categories `C`, `D` and a regular cardinal `κ : Cardinal.{w}`, we define
`isCardinalContinuous C D κ : ObjectProperty C ⥤ D` as the property
of functors which preserves limits indexed by categories `J`
such that `HasCardinalLT (Arrow J) κ`.

When `C : Type w` is a small category, we show that `κ`-continuous
functors `Cᵒᵖ ⥤ Type w` are exactly the objects that are local with
respect to a suitable `w`-small family of morphisms.

## TODO (@joelriou)
* Show that `(isCardinalContinuous Cᵒᵖ (Type w) κ).FullSubcategory` is
locally `κ`-presentable, and that any locally `κ`-presentable category
is equivalent to a category of `κ`-continuous presheaves.

-/

universe w v v' u u'

namespace CategoryTheory

open Limits

namespace Functor

section

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (κ : Cardinal.{w}) [Fact κ.IsRegular]

variable (C D) in
def isCardinalContinuous : ObjectProperty (C ⥤ D) :=
  ⨅ (J : Type w) (_ : Category.{w} J) (_ : HasCardinalLT (Arrow J) κ),
    preservesLimitsOfShape C D J

lemma isCardinalContinuous_iff (F : C ⥤ D) (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    isCardinalContinuous C D κ F ↔
      ∀ (J : Type w) [SmallCategory J] (_ : HasCardinalLT (Arrow J) κ),
        PreservesLimitsOfShape J F := by
  simp [isCardinalContinuous]

variable {κ} in
lemma isCardinalContinuous.preservesColimitsOfShape {F : C ⥤ D}
    (hF : isCardinalContinuous C D κ F)
    (J : Type w) [SmallCategory.{w} J] (hκ : HasCardinalLT (Arrow J) κ) :
    PreservesLimitsOfShape J F :=
  (isCardinalContinuous_iff F κ).1 hF J hκ

end

end Functor

namespace Presheaf

open Functor

variable (C : Type w) [SmallCategory C] (κ : Cardinal.{w}) [Fact κ.IsRegular]

abbrev isCardinalContinuousMorphismProperty : MorphismProperty (Cᵒᵖ ⥤ Type w) :=
  ⨆ (J) (F : SmallCategoryCardinalLT.categoryFamily κ J ⥤ Cᵒᵖ),
    MorphismProperty.ofHoms (Presheaf.preservesLimitHomFamily F)

example : MorphismProperty.IsSmall.{w}
    (isCardinalContinuousMorphismProperty C κ) := by
  infer_instance

lemma isCardinalContinuous_eq_isLocal :
    isCardinalContinuous Cᵒᵖ (Type w) κ =
      (isCardinalContinuousMorphismProperty.{w} C κ).isLocal := by
  trans ⨅ (J : SmallCategoryCardinalLT κ),
    preservesLimitsOfShape Cᵒᵖ (Type w) (SmallCategoryCardinalLT.categoryFamily κ J)
  · refine le_antisymm ?_ ?_
    · simp only [le_iInf_iff]
      intro J P hP
      simpa using hP.preservesColimitsOfShape _ (SmallCategoryCardinalLT.hasCardinalLT κ J)
    · dsimp [isCardinalContinuous]
      simp only [le_iInf_iff]
      intro J _ hJ
      obtain ⟨J', ⟨e⟩⟩ := SmallCategoryCardinalLT.exists_equivalence κ J hJ
      rw [← congr_preservesLimitsOfShape _ _ e]
      apply iInf_le
  · simp [preservesLimitsOfShape_eq_isLocal]

end Presheaf

end CategoryTheory
