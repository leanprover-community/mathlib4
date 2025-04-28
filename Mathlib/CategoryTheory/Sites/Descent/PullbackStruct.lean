/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

/-!
# Chosen pullbacks

-/

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Limits

structure ChosenPullback {X₁ X₂ S : C} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S) where
  pullback : C
  p₁ : pullback ⟶ X₁
  p₂ : pullback ⟶ X₂
  isPullback : IsPullback p₁ p₂ f₁ f₂

namespace ChosenPullback

section

variable {X₁ X₂ S : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S}
  (h : ChosenPullback f₁ f₂)

@[reassoc]
lemma w : h.p₁ ≫ f₁ = h.p₂ ≫ f₂ :=
  h.isPullback.w

structure LiftStruct {Y : C} (g₁ : Y ⟶ X₁) (g₂ : Y ⟶ X₂) where
  f : Y ⟶ h.pullback
  f_p₁ : f ≫ h.p₁ = g₁
  f_p₂ : f ≫ h.p₂ = g₂

namespace LiftStruct

attribute [reassoc (attr := simp)] f_p₁ f_p₂

variable {h} {Y : C} {g₁ : Y ⟶ X₁} {g₂ : Y ⟶ X₂} (l : h.LiftStruct g₁ g₂)

include l in
@[reassoc]
lemma w : g₁ ≫ f₁ = g₂ ≫ f₂ := by
  simp only [← l.f_p₁, ← l.f_p₂, Category.assoc, h.w]

end LiftStruct

end

variable {X S : C} {f : X ⟶ S} (h : ChosenPullback f f)

abbrev Diagonal := h.LiftStruct (𝟙 X) (𝟙 X)

end ChosenPullback

end Limits

end CategoryTheory
