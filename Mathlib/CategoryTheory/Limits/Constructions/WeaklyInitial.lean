/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.WideEqualizers
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Constructions related to weakly initial objects

This file gives constructions related to weakly initial objects, namely:
* If a category has small products and a small weakly initial set of objects, then it has a weakly
  initial object.
* If a category has wide equalizers and a weakly initial object, then it has an initial object.

These are primarily useful to show the General Adjoint Functor Theorem.
-/
set_option backward.defeqAttrib.useBackward true

public section


universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

/--
If `C` has (small) products and a small weakly initial set of objects, then it has a weakly initial
object.
-/
theorem has_weakly_initial_of_weakly_initial_set_and_hasProducts [HasProducts.{v} C] {ι : Type v}
    {B : ι → C} (hB : ∀ A : C, ∃ i, Nonempty (B i ⟶ A)) : ∃ T : C, ∀ X, Nonempty (T ⟶ X) :=
  ⟨∏ᶜ B, fun X => ⟨Pi.π _ _ ≫ (hB X).choose_spec.some⟩⟩

/-- If `C` has (small) wide equalizers and a weakly initial object, then it has an initial object.

The initial object is constructed as the wide equalizer of all endomorphisms on the given weakly
initial object.
-/
theorem hasInitial_of_weakly_initial_and_hasWideEqualizers [HasWideEqualizers.{v} C] {T : C}
    (hT : ∀ X, Nonempty (T ⟶ X)) : HasInitial C := by
  let endos := T ⟶ T
  let i := wideEqualizer.ι (id : endos → endos)
  haveI : Nonempty endos := ⟨𝟙 _⟩
  have : ∀ X : C, Unique (wideEqualizer (id : endos → endos) ⟶ X) := by
    intro X
    refine ⟨⟨i ≫ Classical.choice (hT X)⟩, fun a => ?_⟩
    let E := equalizer a (i ≫ Classical.choice (hT _))
    let e : E ⟶ wideEqualizer id := equalizer.ι _ _
    let h : T ⟶ E := Classical.choice (hT E)
    have : ((i ≫ h) ≫ e) ≫ i = i ≫ 𝟙 _ := by
      rw [Category.assoc, Category.assoc]
      apply wideEqualizer.condition (id : endos → endos) (h ≫ e ≫ i)
    rw [Category.comp_id, cancel_mono_id i] at this
    haveI : IsSplitEpi e := IsSplitEpi.mk' ⟨i ≫ h, this⟩
    rw [← cancel_epi e]
    apply equalizer.condition
  exact hasInitial_of_unique (wideEqualizer (id : endos → endos))

end CategoryTheory
