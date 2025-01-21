/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Filtered.CostructuredArrow
import Mathlib.CategoryTheory.Functor.Flat

/-!
# Transfering filteredness along representably flat functors

We show that if `F : C ⥤ D` is a representably flat functor between two small categories,
filteredness of `C` implies filtereness of `D` and cofilteredness of `D` implies cofilteredness of
`C`.

Dually, if `F` is representably coflat, filteredness of `D` implies filteredness of `C` and
cofilteredness of `C` implies cofilteredness of `D`.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (F : C ⥤ D)

attribute [local instance] final_of_representablyFlat in
lemma isFiltered_of_representablyFlat [IsFiltered C] [RepresentablyFlat F] : IsFiltered D :=
  isFiltered_of_isFiltered_costructuredArrow (𝟭 _) F

lemma isFiltered_of_representablyCoflat [IsFiltered D] [RepresentablyCoflat F] : IsFiltered C :=
  isFiltered_of_isFiltered_costructuredArrow F (𝟭 _)

lemma isCofiltered_of_representablyCoflat [IsCofiltered C] [RepresentablyCoflat F] :
    IsCofiltered D := by
  have := isFiltered_of_representablyFlat F.op
  exact isCofiltered_of_isFiltered_op D

lemma isCofiltered_of_representablyFlat [IsCofiltered D] [RepresentablyFlat F] :
    IsCofiltered C := by
  have := isFiltered_of_representablyCoflat F.op
  exact isCofiltered_of_isFiltered_op C

end CategoryTheory
