/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Functor.KanExtension.Dense
import Mathlib.CategoryTheory.Presentable.LocallyPresentable

/-!
# `κ`-presentable objects form a dense subcategory

In a `κ`-accessible category `C`, `isCardinalPresentable C κ` is
a dense subcategory.

-/

universe w v' v u' u

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C]

-- to be moved
/-- Given `P : ObjectProperty C`, and a presentation `P.ColimitOfShape J X`
of an object `X : C`, this is the induced functor `J ⥤ CostructuredArrow P.ι X`. -/
@[simps]
def ObjectProperty.ColimitOfShape.toCostructuredArrow
    {P : ObjectProperty C} {J : Type*} [Category J]
    {X : C} (p : P.ColimitOfShape J X) :
    J ⥤ CostructuredArrow P.ι X where
  obj j := CostructuredArrow.mk (Y := ⟨_, p.prop_diag_obj j⟩) (by exact p.ι.app j)
  map f := CostructuredArrow.homMk (by exact p.diag.map f)

variable {κ : Cardinal.{w}} [Fact κ.IsRegular]

-- to be moved
instance (X : (isCardinalPresentable C κ).FullSubcategory) :
    IsCardinalPresentable X.obj κ :=
  X.property

instance (X) : IsCardinalPresentable ((isCardinalPresentable C κ).ι.obj X) κ := by
  dsimp
  infer_instance

variable (C κ) in
lemma isCardinalFilteredGenerator_isCardinalPresentable
    [IsCardinalAccessibleCategory C κ] :
    (isCardinalPresentable C κ).IsCardinalFilteredGenerator κ := by
  obtain ⟨P, _, hP⟩ := HasCardinalFilteredGenerator.exists_generator C κ
  refine hP.of_le_isoClosure ?_ le_rfl
  rw [ObjectProperty.isoClosure_eq_self]
  exact hP.le_isCardinalPresentable

namespace IsCardinalAccessibleCategory

lemma final_toCostructuredArrow
    {J : Type u'} [Category.{v'} J] [EssentiallySmall.{w} J]
    [IsCardinalFiltered J κ] {X : C}
    (p : (isCardinalPresentable C κ).ColimitOfShape J X) :
      p.toCostructuredArrow.Final := by
  have := isFiltered_of_isCardinalFiltered J κ
  rw [Functor.final_iff_of_isFiltered]
  refine ⟨fun f ↦ ?_, fun {f j} g₁ g₂ ↦ ?_⟩
  · obtain ⟨j, g, hg⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit f.hom
    exact ⟨j, ⟨CostructuredArrow.homMk g⟩⟩
  · obtain ⟨k, a, h⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ p.isColimit g₁.left g₂.left
      ((CostructuredArrow.w g₁).trans (CostructuredArrow.w g₂).symm)
    exact ⟨k, a, by aesop⟩

instance [IsCardinalAccessibleCategory C κ] :
    (isCardinalPresentable C κ).ι.IsDense where
  isDenseAt X := by
    obtain ⟨J, _, _, ⟨p⟩⟩ :=
      (isCardinalFilteredGenerator_isCardinalPresentable C κ).exists_colimitsOfShape X
    have : EssentiallySmall.{w} J := essentiallySmallSelf _ -- FIXME
    have := final_toCostructuredArrow p
    exact ⟨(Functor.Final.isColimitWhiskerEquiv (F := p.toCostructuredArrow) _).1
      (IsColimit.ofIsoColimit p.isColimit (Cocones.ext (Iso.refl _)))⟩

end IsCardinalAccessibleCategory

end CategoryTheory
