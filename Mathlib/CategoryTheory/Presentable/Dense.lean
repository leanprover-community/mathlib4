/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Functor.KanExtension.Dense
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable

/-!
# `κ`-presentable objects form a dense subcategory

In a `κ`-accessible category `C`, the inclusion of the full subcategory
of `κ`-presentable objects is a dense functor. This expresses canonically
any object `X : C` as a colimit of `κ`-presentable objects, and we show
that this is a `κ`-filtered colimit.

-/

@[expose] public section

universe w v' v u' u

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C] {κ : Cardinal.{w}} [Fact κ.IsRegular]

variable (C κ) in
lemma isCardinalFilteredGenerator_isCardinalPresentable
    [IsCardinalAccessibleCategory C κ] :
    (isCardinalPresentable C κ).IsCardinalFilteredGenerator κ := by
  obtain ⟨P, _, hP⟩ := HasCardinalFilteredGenerator.exists_generator C κ
  refine hP.of_le_isoClosure ?_ le_rfl
  rw [ObjectProperty.isoClosure_eq_self]
  exact hP.le_isCardinalPresentable

namespace IsCardinalAccessibleCategory

instance final_toCostructuredArrow
    {J : Type u'} [Category.{v'} J] [EssentiallySmall.{w} J]
    [IsCardinalFiltered J κ] {X : C}
    (p : (isCardinalPresentable C κ).ColimitOfShape J X) :
    p.toCostructuredArrow.Final := by
  have := isFiltered_of_isCardinalFiltered J κ
  rw [Functor.final_iff_of_isFiltered]
  refine ⟨fun f ↦ ?_, fun {f j} g₁ g₂ ↦ ?_⟩
  · obtain ⟨j, g, hg⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit f.hom
    exact ⟨j, ⟨CostructuredArrow.homMk (ObjectProperty.homMk g)⟩⟩
  · obtain ⟨k, a, h⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ p.isColimit
      g₁.left.hom g₂.left.hom ((CostructuredArrow.w g₁).trans (CostructuredArrow.w g₂).symm)
    exact ⟨k, a, by cat_disch⟩

instance [IsCardinalAccessibleCategory C κ] :
    (isCardinalPresentable C κ).ι.IsDense where
  isDenseAt X := by
    obtain ⟨J, _, _, ⟨p⟩⟩ :=
      (isCardinalFilteredGenerator_isCardinalPresentable C κ).exists_colimitsOfShape X
    exact ⟨(Functor.Final.isColimitWhiskerEquiv (F := p.toCostructuredArrow) _).1
      (IsColimit.ofIsoColimit p.isColimit (Cocones.ext (Iso.refl _)))⟩

instance [IsCardinalAccessibleCategory C κ] (X : C) :
    IsCardinalFiltered (CostructuredArrow (isCardinalPresentable C κ).ι X) κ := by
  obtain ⟨J, _, _, ⟨p⟩⟩ :=
    (isCardinalFilteredGenerator_isCardinalPresentable C κ).exists_colimitsOfShape X
  exact IsCardinalFiltered.of_final p.toCostructuredArrow κ

end IsCardinalAccessibleCategory

end CategoryTheory
