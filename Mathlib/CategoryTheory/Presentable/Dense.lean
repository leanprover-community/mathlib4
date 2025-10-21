/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Presentable.LocallyPresentable
import Mathlib.CategoryTheory.Functor.KanExtension.Dense
import Mathlib.CategoryTheory.Filtered.Final

/-!
# `κ`-presentable objects form a dense subcategory

In a `κ`-accessible category `C`, `isCardinalPresentable C κ` is
a dense subcategory.

-/

universe w v u

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C]

-- to be moved
@[simps]
def ObjectProperty.ColimitOfShape.toCostructuredArrow
    {P : ObjectProperty C} {J : Type*} [Category J]
    {X : C} (p : P.ColimitOfShape J X) :
    J ⥤ CostructuredArrow P.ι X where
  obj j := CostructuredArrow.mk (Y := ⟨_, p.prop_diag_obj j⟩) (by exact p.ι.app j)
  map f := CostructuredArrow.homMk (by exact p.diag.map f)

variable {κ : Cardinal.{w}} [Fact κ.IsRegular]

-- to be moved
instance (X : (isCardinalPresentable C κ).FullSubcategory) : IsCardinalPresentable X.obj κ :=
  X.property

instance (X) : IsCardinalPresentable ((isCardinalPresentable C κ).ι.obj X) κ := by
  dsimp
  infer_instance

namespace IsCardinalAccessibleCategory

section

variable {J : Type w} [SmallCategory J] [IsCardinalFiltered J κ] {X : C}
  (p : (isCardinalPresentable C κ).ColimitOfShape J X)

lemma final_toCostructuredArrow : p.toCostructuredArrow.Final := by
  have : EssentiallySmall.{w} J := essentiallySmallSelf _ -- FIXME
  have := isFiltered_of_isCardinalFiltered J κ
  rw [Functor.final_iff_of_isFiltered]
  refine ⟨fun f ↦ ?_, fun {f j} g₁ g₂ ↦ ?_⟩
  · obtain ⟨j, g, hg⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit f.hom
    exact ⟨j, ⟨CostructuredArrow.homMk g⟩⟩
  · obtain ⟨k, a, h⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ p.isColimit g₁.left g₂.left
      ((CostructuredArrow.w g₁).trans (CostructuredArrow.w g₂).symm)
    exact ⟨k, a, by aesop⟩

end

variable [IsCardinalAccessibleCategory C κ]

instance : (isCardinalPresentable C κ).ι.IsDense where
  isDenseAt X := by
    let E := (Functor.LeftExtension.mk (𝟭 _)
      (isCardinalPresentable C κ).ι.rightUnitor.inv)
    have := E.coconeAt X
    -- use `final_toCostructuredArrow`
    sorry

end IsCardinalAccessibleCategory

end CategoryTheory
