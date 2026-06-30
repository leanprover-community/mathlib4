/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.Presentable.Presheaf
public import Mathlib.CategoryTheory.Presentable.Type

/-!
# `Discrete PUnit` is locally presentable

-/

universe u w

public section

namespace CategoryTheory

set_option backward.defeqAttrib.useBackward true in
instance (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    IsCardinalLocallyPresentable (Discrete PUnit.{u + 1}) κ := by
  let e : ((Discrete PEmpty.{w + 1})ᵒᵖ ⥤ Type w) ≌ Discrete PUnit.{u + 1} :=
    { functor := (Functor.const _).obj ⟨⟨⟩⟩
      inverse := Discrete.functor (fun _ ↦ (Discrete.functor (by rintro ⟨⟩)).leftOp)
      unitIso := NatIso.ofComponents
        (fun F ↦ NatIso.ofComponents (by rintro ⟨⟨⟨⟩⟩⟩) (by rintro ⟨⟨⟨⟩⟩⟩))
        (fun _ ↦ by ext ⟨⟨⟨⟩⟩⟩)
      counitIso := Iso.refl _ }
  exact e.isCardinalLocallyPresentable κ

instance : IsLocallyPresentable.{w} (Discrete PUnit.{u + 1}) where
  exists_cardinal := ⟨.aleph0, Cardinal.fact_isRegular_aleph0, inferInstance⟩

end CategoryTheory
