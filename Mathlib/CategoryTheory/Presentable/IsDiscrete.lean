/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Presentable.LocallyPresentable

/-! # Presentable objects in discrete categories

The purpose of this file is to show that a category with a single
object and a single morphism is locally presentable.

-/

@[expose] public section

universe w

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] [IsDiscrete C]

namespace IsDiscrete

attribute [local instance] IsFiltered.nonempty

protected instance (priority := low) isCardinalPresentable
    (X : C) (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    IsCardinalPresentable X κ :=
  .mk (fun J _ _ F c hc ↦ by
    have := isFiltered_of_isCardinalFiltered J κ
    refine ⟨fun g ↦ ?_, fun j f₁ f₂ _ ↦ ⟨j, 𝟙 j, by subsingleton⟩⟩
    obtain rfl := IsDiscrete.eq_of_hom g
    let j : J := Classical.arbitrary _
    exact ⟨j, eqToHom (IsDiscrete.eq_of_hom (c.ι.app j)).symm, by subsingleton⟩)

set_option backward.defeqAttrib.useBackward true in
protected instance (priority := low) isCardinalAccessible
    {D : Type*} [Category* D]
    (F : C ⥤ D) (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    F.IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := ⟨fun {K} ↦ ⟨fun {c} hc ↦ ⟨by
    have := isFiltered_of_isCardinalFiltered J κ
    let j : J := Classical.arbitrary _
    have : IsIso ((F.mapCocone c).ι.app j) := by
      dsimp; infer_instance
    exact Functor.IsEventuallyConstantFrom.isColimitOfIsIso (i₀ := j)
      (fun _ _ ↦ by dsimp; infer_instance) _⟩⟩⟩

instance (priority := low)
    {D : Type*} [Category* D] (F : C ⥤ D) :
    Functor.IsAccessible.{w} F :=
  ⟨.aleph0, Cardinal.fact_isRegular_aleph0, inferInstance⟩

instance (priority := low) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [Subsingleton C] [Nonempty C] :
    IsCardinalFiltered C κ where
  nonempty_cocone F _ :=
    ⟨Cocone.mk (Classical.arbitrary _)
      { app _ := eqToHom (by subsingleton) }⟩

instance (α : Type*) [Preorder α] [Subsingleton α] : IsDiscrete α where
  eq_of_hom _ := by subsingleton

instance (priority := low) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [Subsingleton C] [Nonempty C] :
    IsCardinalLocallyPresentable C κ where
  has_colimits_of_shape J := ⟨fun F ↦
    ⟨Cocone.mk (Classical.arbitrary C)
      { app _ := eqToHom (by subsingleton) },
      { desc _ := eqToHom (by subsingleton) }⟩ ⟩
  exists_generator := by
    let X : C := Classical.arbitrary _
    refine ⟨.ofObj (fun (_ : PUnit.{w + 1}) ↦ X), inferInstance,
      fun _ _ ↦ IsDiscrete.isCardinalPresentable _ _,
      fun Y ↦ ?_⟩
    obtain rfl := Subsingleton.elim X Y
    exact ⟨PUnit.{w + 1}, inferInstance, inferInstance,
      { diag := (Functor.const _).obj X
        ι := 𝟙 _
        isColimit.desc _ := eqToHom (by subsingleton) }, fun _ ↦ ⟨⟨⟩⟩⟩

instance (priority := low) [Subsingleton C] [Nonempty C] :
    IsLocallyPresentable.{w} C :=
  ⟨.aleph0, Cardinal.fact_isRegular_aleph0, inferInstance⟩

end IsDiscrete

end CategoryTheory
