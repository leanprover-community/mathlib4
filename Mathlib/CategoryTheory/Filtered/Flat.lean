/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Filtered.CostructuredArrow
import Mathlib.CategoryTheory.Functor.Flat

/-!
# Pulling back filteredness along representably flat functors

We show that if `F : C ⥤ D` is a representably coflat functor between two categories,
filteredness of `D` implies filteredness of `C`. Dually, if `F` is representably flat,
cofilteredness of `D` implies cofilteredness of `C`.

Transferring (co)filteredness *along* representably (co)flat functors is given by
`IsFiltered.of_final` and its dual, since every representably flat functor is final and every
representably coflat functor is initial.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (F : C ⥤ D)

lemma isFiltered_of_representablyCoflat [IsFiltered D] [RepresentablyCoflat F] : IsFiltered C :=
  isFiltered_of_isFiltered_costructuredArrow F (𝟭 _)

lemma isCofiltered_of_representablyFlat [IsCofiltered D] [RepresentablyFlat F] :
    IsCofiltered C := by
  have := isFiltered_of_representablyCoflat F.op
  exact isCofiltered_of_isFiltered_op C

end CategoryTheory
