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
  p : pullback ⟶ S := p₁ ≫ f₁
  hp₁ : p₁ ≫ f₁ = p := by aesop_cat

namespace ChosenPullback

section

variable {X₁ X₂ S : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S}
  (h : ChosenPullback f₁ f₂)

@[reassoc]
lemma w : h.p₁ ≫ f₁ = h.p₂ ≫ f₂ :=
  h.isPullback.w

attribute [reassoc (attr := simp)] hp₁

@[reassoc (attr := simp)]
lemma hp₂ : h.p₂ ≫ f₂ = h.p := by rw [← h.w, hp₁]

structure LiftStruct {Y : C} (g₁ : Y ⟶ X₁) (g₂ : Y ⟶ X₂) (b : Y ⟶ S) where
  f : Y ⟶ h.pullback
  f_p₁ : f ≫ h.p₁ = g₁
  f_p₂ : f ≫ h.p₂ = g₂
  f_p : f ≫ h.p = b

namespace LiftStruct

attribute [reassoc (attr := simp)] f_p₁ f_p₂ f_p

variable {h} {Y : C} {g₁ : Y ⟶ X₁} {g₂ : Y ⟶ X₂} {b : Y ⟶ S} (l : h.LiftStruct g₁ g₂ b)

include l in
@[reassoc]
lemma w : g₁ ≫ f₁ = g₂ ≫ f₂ := by
  simp only [← l.f_p₁, ← l.f_p₂, Category.assoc, h.w]

end LiftStruct

end

variable {X S : C} {f : X ⟶ S} (h : ChosenPullback f f)

abbrev Diagonal := h.LiftStruct (𝟙 X) (𝟙 X) f

end ChosenPullback

variable {X₁ X₂ X₃ S : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S} {f₃ : X₃ ⟶ S}
  (h₁₂ : ChosenPullback f₁ f₂) (h₂₃ : ChosenPullback f₂ f₃) (h₁₃ : ChosenPullback f₁ f₃)

structure ChosenPullback₃ where
  chosenPullback : ChosenPullback h₁₂.p₂ h₂₃.p₁
  p : chosenPullback.pullback ⟶ S := chosenPullback.p₁ ≫ h₁₂.p
  -- should this be a `LiftStruct` on `p₁` and `p₃`?
  l : h₁₃.LiftStruct (chosenPullback.p₁ ≫ h₁₂.p₁) (chosenPullback.p₂ ≫ h₂₃.p₂) p
  p₁ : chosenPullback.pullback ⟶ X₁ := chosenPullback.p₁ ≫ h₁₂.p₁
  p₃ : chosenPullback.pullback ⟶ X₃ := chosenPullback.p₂ ≫ h₂₃.p₂
  hp₁ : chosenPullback.p₁ ≫ h₁₂.p₁ = p₁ := by aesop_cat
  hp₃ : chosenPullback.p₂ ≫ h₂₃.p₂ = p₃ := by aesop_cat

namespace ChosenPullback₃

variable {h₁₂ h₂₃ h₁₃} (h : ChosenPullback₃ h₁₂ h₂₃ h₁₃)

def p₁₃ : h.chosenPullback.pullback ⟶ h₁₃.pullback := h.l.f
def p₁₂ : h.chosenPullback.pullback ⟶ h₁₂.pullback := h.chosenPullback.p₁
def p₂₃ : h.chosenPullback.pullback ⟶ h₂₃.pullback := h.chosenPullback.p₂
def p₂ : h.chosenPullback.pullback ⟶ X₂ := h.chosenPullback.p

@[reassoc (attr := simp)]
lemma p₁₂_p₁ : h.p₁₂ ≫ h₁₂.p₁ = h.p₁ := by simp [p₁₂, hp₁]

@[reassoc (attr := simp)]
lemma p₁₂_p₂ : h.p₁₂ ≫ h₁₂.p₂ = h.p₂ := by simp [p₁₂, p₂]

@[reassoc (attr := simp)]
lemma p₂₃_p₂ : h.p₂₃ ≫ h₂₃.p₁ = h.p₂ := by simp [p₂₃, p₂]

@[reassoc (attr := simp)]
lemma p₂₃_p₃ : h.p₂₃ ≫ h₂₃.p₂ = h.p₃ := by simp [p₂₃, hp₃]

@[reassoc (attr := simp)]
lemma p₁₃_p₁ : h.p₁₃ ≫ h₁₃.p₁ = h.p₁ := by simp [p₁₃, hp₁]

@[reassoc (attr := simp)]
lemma p₁₃_p₃ : h.p₁₃ ≫ h₁₃.p₂ = h.p₃ := by simp [p₁₃, hp₃]

@[reassoc (attr := simp)]
lemma w₁ : h.p₁ ≫ f₁ = h.p := by
  simpa only [← hp₁, Category.assoc, h₁₃.hp₁, h.l.f_p] using h.l.f_p₁.symm =≫ f₁

@[reassoc (attr := simp)]
lemma w₃ : h.p₃ ≫ f₃ = h.p := by
  simpa only [← hp₃, Category.assoc, h₁₃.hp₂, h.l.f_p] using h.l.f_p₂.symm =≫ f₃

@[reassoc (attr := simp)]
lemma w₂ : h.p₂ ≫ f₂ = h.p := by
  rw [← p₂₃_p₂_assoc, h₂₃.w, ← w₃, p₂₃_p₃_assoc]

lemma exists_lift {Y : C} (g₁ : Y ⟶ X₁) (g₂ : Y ⟶ X₂) (g₃ : Y ⟶ X₃) (b : Y ⟶ S)
    (hg₁ : g₁ ≫ f₁ = b) (hg₂ : g₂ ≫ f₂ = b) (hg₃ : g₃ ≫ f₃ = b) :
    ∃ (φ : Y ⟶ h.chosenPullback.pullback), φ ≫ h.p₁ = g₁ ∧ φ ≫ h.p₂ = g₂ ∧ φ ≫ h.p₃ = g₃ := by
  obtain ⟨φ₁₂, w₁, w₂⟩ := h₁₂.isPullback.exists_lift g₁ g₂ (by aesop)
  obtain ⟨φ₂₃, w₂', w₃⟩ := h₂₃.isPullback.exists_lift g₂ g₃ (by aesop)
  obtain ⟨φ, w₁₂, w₂₃⟩ := h.chosenPullback.isPullback.exists_lift φ₁₂ φ₂₃ (by aesop)
  refine ⟨φ, ?_, ?_, ?_⟩
  · rw [← w₁, ← w₁₂, Category.assoc, ← p₁₂, p₁₂_p₁]
  · rw [← w₂, ← w₁₂, Category.assoc, ← p₁₂, p₁₂_p₂]
  · rw [← w₃, ← w₂₃, Category.assoc, ← p₂₃, p₂₃_p₃]

end ChosenPullback₃

end Limits

end CategoryTheory
