/-
Copyright (c) 2024 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Filtered.OfColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Final

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits Functor

variable {A : Type u₁} [SmallCategory A]
variable {B : Type u₁} [SmallCategory B]
variable {T : Type u₁} [SmallCategory T]
variable (L : A ⥤ T) (R : B ⥤ T)

variable [IsFiltered B] [Final R] [∀ b : B, IsFiltered (CostructuredArrow L (R.obj b))]

def foo : IsFiltered A := by
  apply isFiltered_of_nonempty_limit_colimit_to_colimit_limit
  intro J _ _ F
  constructor
  let R' := Grothendieck.pre (CostructuredArrow.functor L) R
  haveI : IsIso (colimit.pre (CostructuredArrow.grothendieckProj L ⋙ F.flip) R') :=
    Final.colimit_pre_isIso R'
  refine lim.map (colimitIsoColimitGrothendieck L F.flip).hom ≫
    lim.map (inv (colimit.pre (CostructuredArrow.grothendieckProj L ⋙ F.flip) R')) ≫ ?_
  sorry

#check IsIso

end CategoryTheory
