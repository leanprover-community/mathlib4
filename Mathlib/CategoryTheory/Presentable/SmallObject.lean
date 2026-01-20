/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.CategoryTheory.SmallObject.Basic

/-!
# The small object argument in locally presentable categories

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

namespace IsLocallyPresentable

variable {C : Type u} [Category.{v} C] [IsLocallyPresentable.{w} C]

-- to be moved
instance : LocallySmall.{w} C := by
  obtain ⟨κ, _, _⟩ := IsLocallyPresentable.exists_cardinal C
  infer_instance

-- to be moved
instance : HasColimitsOfSize.{w, w} C := by
  obtain ⟨κ, _, _⟩ := IsLocallyPresentable.exists_cardinal C
  infer_instance

instance (W : MorphismProperty C) [MorphismProperty.IsSmall.{w} W] :
    MorphismProperty.HasSmallObjectArgument.{w} W where
  exists_cardinal := by
    choose κ' _ hκ' using fun (w : W.toSet) ↦ IsPresentable.exists_cardinal.{w} w.1.left
    obtain ⟨κ, _, hκ⟩ :=
      HasCardinalLT.exists_regular_cardinal_forall (fun w ↦ (κ' w).ord.ToType)
    have : Fact κ.IsRegular := ⟨by assumption⟩
    replace hκ (w : W.toSet) : IsCardinalPresentable w.1.left κ :=
      isCardinalPresentable_of_le _ (by simpa using (hκ w).le)
    haveI : OrderBot κ.ord.ToType :=
      Cardinal.toTypeOrderBot (Cardinal.IsRegular.ne_zero Fact.out)
    exact ⟨κ, inferInstance, inferInstance,
      { preservesColimit {A _ _ _} i hi _ _ := by
          have : IsCardinalPresentable A κ := hκ ⟨i, hi⟩
          have := preservesColimitsOfShape_of_isCardinalPresentable A κ κ.ord.ToType
          infer_instance }⟩

end IsLocallyPresentable

end CategoryTheory
