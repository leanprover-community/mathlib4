/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.limits.unit
! leanprover-community/mathlib commit c85d2ff93210de84373ab4c9c6dba2b78494961e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.PUnit
import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# `Discrete PUnit` has limits and colimits

Mostly for the sake of constructing trivial examples, we show all (co)cones into `Discrete PUnit`
are (co)limit (co)cones. We also show that such (co)cones exist, and that `Discrete PUnit` has all
(co)limits.
-/


universe v' v

open CategoryTheory

namespace CategoryTheory.Limits

variable {J : Type v} [Category.{v'} J] {F : J ⥤ Discrete PUnit}

/-- A trivial cone for a functor into `PUnit`. `pUnitConeIsLimit` shows it is a limit. -/
def pUnitCone : Cone F :=
  ⟨⟨⟨⟩⟩, (Functor.pUnitExt _ _).hom⟩
#align category_theory.limits.punit_cone CategoryTheory.Limits.pUnitCone

/-- A trivial cocone for a functor into `PUnit`. `pUnitCoconeIsLimit` shows it is a colimit. -/
def pUnitCocone : Cocone F :=
  ⟨⟨⟨⟩⟩, (Functor.pUnitExt _ _).hom⟩
#align category_theory.limits.punit_cocone CategoryTheory.Limits.pUnitCocone

/-- Any cone over a functor into `PUnit` is a limit cone.
-/
def pUnitConeIsLimit {c : Cone F} : IsLimit c where
  lift := fun s => eqToHom (by simp)
#align category_theory.limits.punit_cone_is_limit CategoryTheory.Limits.pUnitConeIsLimit

/-- Any cocone over a functor into `PUnit` is a colimit cocone.
-/
def pUnitCoconeIsColimit {c : Cocone F} : IsColimit c where
  desc := fun s => eqToHom (by simp)
#align category_theory.limits.punit_cocone_is_colimit CategoryTheory.Limits.pUnitCoconeIsColimit

instance : HasLimitsOfSize.{v', v} (Discrete PUnit) :=
  ⟨fun _ _ => ⟨fun _ => ⟨pUnitCone, pUnitConeIsLimit⟩⟩⟩

instance : HasColimitsOfSize.{v', v} (Discrete PUnit) :=
  ⟨fun _ _ => ⟨fun _ => ⟨pUnitCocone, pUnitCoconeIsColimit⟩⟩⟩

end CategoryTheory.Limits
