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

universe v₁ u₁

namespace CategoryTheory

open Limits

instance {C : Type u₁} [Category.{v₁} C] [IsFilteredOrEmpty C] : IsPreconnected C :=
  zigzag_isPreconnected fun c₁ c₂ =>
    .trans (.of_hom (IsFiltered.leftToMax c₁ c₂)) (.of_inv (IsFiltered.rightToMax c₁ c₂))

instance {C : Type u₁} [Category.{v₁} C] [IsCofilteredOrEmpty C] : IsPreconnected C :=
  zigzag_isPreconnected fun c₁ c₂ =>
    .trans (.of_inv (IsCofiltered.minToLeft c₁ c₂)) (.of_hom (IsCofiltered.minToRight c₁ c₂))

instance {C : Type u₁} [Category.{v₁} C] [IsFiltered C] : IsConnected C where
  is_nonempty := IsFiltered.nonempty

instance {C : Type u₁} [Category.{v₁} C] [IsCofiltered C] : IsConnected C where
  is_nonempty := IsCofiltered.nonempty

variable {C : Type u₁} [SmallCategory C]
variable {D : Type u₁} [SmallCategory D]
variable (F : C ⥤ D)

instance [h : RepresentablyFlat F] : F.Final := ⟨inferInstance⟩

lemma isFiltered_of_representablyFlat [IsFiltered C] [RepresentablyFlat F] : IsFiltered D :=
  haveI : PreservesFiniteLimits F := preservesFiniteLimits_of_flat F
  isFiltered_of_isFiltered_costructuredArrow (𝟭 _) F

lemma isCofiltered_of_representablyCoflat [IsCofiltered C] [RepresentablyCoflat F] :
    IsCofiltered D := by
  have := isFiltered_of_representablyFlat F.op
  exact isCofiltered_of_isFiltered_op D

end CategoryTheory
