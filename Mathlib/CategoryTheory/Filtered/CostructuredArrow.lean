/-
Copyright (c) 2024 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Filtered.OfColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Limits.Final

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits Functor

variable {A : Type u₁} [SmallCategory A]
variable {B : Type u₁} [SmallCategory B]
variable {T : Type u₁} [SmallCategory T]
variable (L : A ⥤ T) (R : B ⥤ T)

variable [IsFiltered B] [Final R] [∀ b, IsFiltered (CostructuredArrow L (R.obj b))]

def isFiltered_of_isFiltered_costructuredArrow : IsFiltered A := by
  apply isFiltered_of_nonempty_limit_colimit_to_colimit_limit
  intro J _ _ F
  constructor
  let R' := Grothendieck.pre (CostructuredArrow.functor L) R
  haveI : IsIso (colimit.pre (CostructuredArrow.grothendieckProj L ⋙ F.flip) R') :=
    Final.colimit_pre_isIso R'
  haveI : PreservesLimitsOfShape J (colim (J := B) (C := Type u₁)) :=
    inferInstance
  haveI : ∀ b, PreservesLimitsOfShape J
      (colim (J := (R ⋙ CostructuredArrow.functor L).obj b) (C := Type u₁)) := by
    intro b
    simp only [comp_obj, CostructuredArrow.functor_obj, Cat.of_α]
    exact filtered_colim_preservesFiniteLimits
  haveI : PreservesLimitsOfShape J
      (colim (J := (Grothendieck (R ⋙ CostructuredArrow.functor L))) (C := Type u₁)) := by
    sorry  -- TODO general lemma on `Grothendieck`
  refine lim.map ((colimitIsoColimitGrothendieck L F.flip).hom ≫
    (inv (colimit.pre (CostructuredArrow.grothendieckProj L ⋙ F.flip) R'))) ≫
    (colimitLimitIso (R' ⋙ CostructuredArrow.grothendieckProj L ⋙ F.flip).flip).inv ≫
    colim.map ?_ ≫
    colimit.pre _ R' ≫
    (colimitIsoColimitGrothendieck L (limit F)).inv
  rw [← Functor.assoc, ← Functor.assoc]
  exact (limitCompWhiskeringLeftIsoCompLimit F (R' ⋙ CostructuredArrow.grothendieckProj L)).hom

end CategoryTheory
