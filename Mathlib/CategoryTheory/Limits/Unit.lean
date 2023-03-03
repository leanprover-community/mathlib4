/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.limits.unit
! leanprover-community/mathlib commit c85d2ff93210de84373ab4c9c6dba2b78494961e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Punit
import Mathbin.CategoryTheory.Limits.HasLimits

/-!
# `discrete punit` has limits and colimits

Mostly for the sake of constructing trivial examples, we show all (co)cones into `discrete punit`
are (co)limit (co)cones. We also show that such (co)cones exist, and that `discrete punit` has all
(co)limits.
-/


universe v' v

open CategoryTheory

namespace CategoryTheory.Limits

variable {J : Type v} [Category.{v'} J] {F : J ⥤ Discrete PUnit}

/-- A trivial cone for a functor into `punit`. `punit_cone_is_limit` shows it is a limit. -/
def punitCone : Cone F :=
  ⟨⟨⟨⟩⟩, (Functor.pUnitExt _ _).Hom⟩
#align category_theory.limits.punit_cone CategoryTheory.Limits.punitCone

/-- A trivial cocone for a functor into `punit`. `punit_cocone_is_limit` shows it is a colimit. -/
def punitCocone : Cocone F :=
  ⟨⟨⟨⟩⟩, (Functor.pUnitExt _ _).Hom⟩
#align category_theory.limits.punit_cocone CategoryTheory.Limits.punitCocone

/-- Any cone over a functor into `punit` is a limit cone.
-/
def punitConeIsLimit {c : Cone F} : IsLimit c := by tidy
#align category_theory.limits.punit_cone_is_limit CategoryTheory.Limits.punitConeIsLimit

/-- Any cocone over a functor into `punit` is a colimit cocone.
-/
def punitCoconeIsColimit {c : Cocone F} : IsColimit c := by tidy
#align category_theory.limits.punit_cocone_is_colimit CategoryTheory.Limits.punitCoconeIsColimit

instance : HasLimitsOfSize.{v', v} (Discrete PUnit) := by tidy

instance : HasColimitsOfSize.{v', v} (Discrete PUnit) := by tidy

end CategoryTheory.Limits

