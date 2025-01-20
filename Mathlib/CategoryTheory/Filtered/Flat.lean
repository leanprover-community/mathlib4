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
filteredness of `C` implies filtereness of `D`.
-/

universe u

namespace CategoryTheory

open Limits

variable {C : Type u} [SmallCategory C]
variable {D : Type u} [SmallCategory D]
variable (F : C ⥤ D)

lemma isFiltered_of_representablyFlat [IsFiltered C] [RepresentablyFlat F] : IsFiltered D :=
  haveI : PreservesFiniteLimits F := preservesFiniteLimits_of_flat F
  isFiltered_of_isFiltered_costructuredArrow (𝟭 _) F

lemma isCofiltered_of_representablyCoflat [IsCofiltered C] [RepresentablyCoflat F] :
    IsCofiltered D := by
  have := isFiltered_of_representablyFlat F.op
  exact isCofiltered_of_isFiltered_op D

end CategoryTheory
