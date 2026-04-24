/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Traced monoidal categories

## References

* [A. Joyal and R. Street and D. R. Verity, *Traced monoidal categories*][JoyalStreet1996]

-/

@[expose] public section



universe u v

namespace CategoryTheory

open Category MonoidalCategory

/-- A traced symmetric monoidal category. -/
class TracedCategory
    (C : Type u)
    [Category.{v} C]
    [MonoidalCategory.{v} C]
    [SymmetricCategory.{v} C] where
  /-- The trace operator. -/
  trace : ∀ {A B : C} (W : C), (A ⊗ W ⟶ B ⊗ W) → (A ⟶ B)
  /-- Left tightening: sliding a morphism past the trace on the left. -/
  trace_naturality_left : ∀ {A A' B : C} (W : C) (f : A' ⟶ A) (g : A ⊗ W ⟶ B ⊗ W),
      trace W (f ▷ W ≫ g) = f ≫ trace W g := by cat_disch
  /-- Right tightening: sliding a morphism past the trace on the right. -/
  trace_naturality_right : ∀ {A B B' : C} (W : C) (f : A ⊗ W ⟶ B ⊗ W) (g : B ⟶ B'),
      trace W (f ≫ g ▷ W) = trace W f ≫ g := by cat_disch
  /-- Sliding: an endomorphism on the feedback wire slides past the trace. -/
  trace_dinaturality : ∀ {A B W : C} (f : A ⊗ W ⟶ B ⊗ W) (h : W ⟶ W),
      trace W (f ≫ B ◁ h) = trace W (A ◁ h ≫ f) := by cat_disch
  /-- Superposing: trace commutes with left tensoring by a bystander object. -/
  trace_superposing : ∀ {A B : C} (C' W : C) (f : A ⊗ W ⟶ B ⊗ W),
      C' ◁ trace W f = trace W ((α_ C' A W).hom ≫ C' ◁ f ≫ (α_ C' B W).inv) := by cat_disch
  /-- Vanishing I: trace over the tensor unit is the morphism itself (up to unitors). -/
  trace_vanishing_one : ∀ {A B : C} (f : A ⊗ 𝟙_ C ⟶ B ⊗ 𝟙_ C),
      trace (𝟙_ C) f = (ρ_ A).inv ≫ f ≫ (ρ_ B).hom := by cat_disch
  /-- Vanishing II: trace over a tensor product equals iterated trace. -/
  trace_vanishing_two : ∀ {A B X Y : C} (f : A ⊗ (X ⊗ Y) ⟶ B ⊗ (X ⊗ Y)),
      trace (X ⊗ Y) f = trace X (trace Y ((α_ A X Y).hom ≫ f ≫ (α_ B X Y).inv)) := by cat_disch
  /-- Yanking: the trace of the braiding is the identity. -/
  trace_yanking : ∀ (W : C), trace W (β_ W W).hom = 𝟙 W := by cat_disch

end CategoryTheory
