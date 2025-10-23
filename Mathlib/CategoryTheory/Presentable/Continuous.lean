/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.Limits
import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-!
# `κ`-continuous functors
-/
universe w v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (κ : Cardinal.{w}) [Fact κ.IsRegular]

namespace Functor

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

end Functor

end CategoryTheory
