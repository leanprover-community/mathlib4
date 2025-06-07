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

open Limits in
lemma IsPullback.mk' {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (w : fst ≫ f = snd ≫ g) (hom_ext : ∀ ⦃T : C⦄ ⦃φ φ' : T ⟶ P⦄ (_ : φ ≫ fst = φ' ≫ fst)
    (_ : φ ≫ snd = φ' ≫ snd), φ = φ') (exists_lift : ∀ ⦃T : C⦄ (a : T ⟶ X) (b : T ⟶ Y)
    (_ : a ≫ f = b ≫ g), ∃ (l : T ⟶ P), l ≫ fst = a ∧ l ≫ snd = b) :
    IsPullback fst snd f g where
  w := w
  isLimit' := by
    let l (s : PullbackCone f g) : s.pt ⟶ P := (exists_lift _ _ s.condition).choose
    exact ⟨Limits.PullbackCone.IsLimit.mk _
      (fun s ↦ (exists_lift _ _ s.condition).choose)
      (fun s ↦ (exists_lift _ _ s.condition).choose_spec.1)
      (fun s ↦ (exists_lift _ _ s.condition).choose_spec.2)
      (fun s m h₁ h₂ ↦ hom_ext
        (h₁.trans (exists_lift _ _ s.condition).choose_spec.1.symm)
        (h₂.trans (exists_lift _ _ s.condition).choose_spec.2.symm))⟩

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

lemma commSq : CommSq h.p₁ h.p₂ f₁ f₂ where
  w := h.w

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

instance : Subsingleton (h.LiftStruct g₁ g₂ b) where
  allEq := by
    rintro ⟨f, f_p₁, f_p₂, _⟩ ⟨f', f'_p₁, f'_p₂, _⟩
    obtain rfl : f = f' := by
      apply h.isPullback.hom_ext
      · rw [f_p₁, f'_p₁]
      · rw [f_p₂, f'_p₂]
    rfl

lemma nonempty (w : g₁ ≫ f₁ = g₂ ≫ f₂) (hf₁ : g₁ ≫ f₁ = b) :
    Nonempty (h.LiftStruct g₁ g₂ b) := by
  obtain ⟨l, h₁, h₂⟩ := h.isPullback.exists_lift g₁ g₂ w
  exact ⟨{
    f := l
    f_p₁ := h₁
    f_p₂ := h₂
    f_p := by
      rw [← h.hp₁, ← hf₁, reassoc_of% h₁]
  }⟩

end LiftStruct

end

variable {X S : C} {f : X ⟶ S} (h : ChosenPullback f f)

abbrev Diagonal := h.LiftStruct (𝟙 X) (𝟙 X) f

instance : Nonempty h.Diagonal := by apply LiftStruct.nonempty <;> aesop

end ChosenPullback

variable {X₁ X₂ X₃ S : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S} {f₃ : X₃ ⟶ S}
  (h₁₂ : ChosenPullback f₁ f₂) (h₂₃ : ChosenPullback f₂ f₃) (h₁₃ : ChosenPullback f₁ f₃)

structure ChosenPullback₃ where
  chosenPullback : ChosenPullback h₁₂.p₂ h₂₃.p₁
  p : chosenPullback.pullback ⟶ S := chosenPullback.p₁ ≫ h₁₂.p
  p₁ : chosenPullback.pullback ⟶ X₁ := chosenPullback.p₁ ≫ h₁₂.p₁
  p₃ : chosenPullback.pullback ⟶ X₃ := chosenPullback.p₂ ≫ h₂₃.p₂
  l : h₁₃.LiftStruct p₁ p₃ p
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

@[reassoc (attr := simp)]
lemma p₁₂_p : h.p₁₂ ≫ h₁₂.p = h.p := by
  rw [← h₁₂.hp₂, p₁₂_p₂_assoc, w₂]

@[reassoc (attr := simp)]
lemma p₂₃_p : h.p₂₃ ≫ h₂₃.p = h.p := by
  rw [← h₂₃.hp₂, p₂₃_p₃_assoc, w₃]

@[reassoc (attr := simp)]
lemma p₁₃_p : h.p₁₃ ≫ h₁₃.p = h.p := by
  rw [← h₁₃.hp₁, p₁₃_p₁_assoc, w₁]

lemma p₁₂_eq_lift : h.p₁₂ = h₁₂.isPullback.lift h.p₁ h.p₂ (by simp) := by
  apply h₁₂.isPullback.hom_ext <;> simp

lemma p₂₃_eq_lift : h.p₂₃ = h₂₃.isPullback.lift h.p₂ h.p₃ (by simp) := by
  apply h₂₃.isPullback.hom_ext <;> simp

lemma p₁₃_eq_lift : h.p₁₃ = h₁₃.isPullback.lift h.p₁ h.p₃ (by simp) := by
  apply h₁₃.isPullback.hom_ext <;> simp

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

lemma isPullback₂ : IsPullback h.p₁₂ h.p₂₃ h₁₂.p₂ h₂₃.p₁ := h.chosenPullback.isPullback

lemma hom_ext {Y : C} {φ φ' : Y ⟶ h.chosenPullback.pullback}
    (h₁ : φ ≫ h.p₁ = φ' ≫ h.p₁) (h₂ : φ ≫ h.p₂ = φ' ≫ h.p₂)
    (h₃ : φ ≫ h.p₃ = φ' ≫ h.p₃) : φ = φ' := by
  apply h.isPullback₂.hom_ext
  · apply h₁₂.isPullback.hom_ext <;> simpa
  · apply h₂₃.isPullback.hom_ext <;> simpa

lemma isPullback₁ : IsPullback h.p₁₂ h.p₁₃ h₁₂.p₁ h₁₃.p₁ :=
  .mk' (by simp) (fun _ _ _ h₁ h₂ ↦ by
    apply h.hom_ext
    · simpa using h₁ =≫ h₁₂.p₁
    · simpa using h₁ =≫ h₁₂.p₂
    · simpa using h₂ =≫ h₁₃.p₂)
    (fun _ a b w ↦ by
      obtain ⟨φ, hφ₁, hφ₂, hφ₃⟩ :=
        h.exists_lift (a ≫ h₁₂.p₁) (a ≫ h₁₂.p₂) (b ≫ h₁₃.p₂) _ rfl
          (by simp) (by simpa using w.symm =≫ f₁)
      refine ⟨φ, ?_, ?_⟩
      · apply h₁₂.isPullback.hom_ext <;> simpa
      · apply h₁₃.isPullback.hom_ext <;> aesop)

lemma isPullback₃ : IsPullback h.p₁₃ h.p₂₃ h₁₃.p₂ h₂₃.p₂ :=
  .mk' (by simp) (fun _ _ _ h₁ h₂ ↦ by
    apply h.hom_ext
    · simpa using h₁ =≫ h₁₃.p₁
    · simpa using h₂ =≫ h₂₃.p₁
    · simpa using h₁ =≫ h₁₃.p₂)
    (fun _ a b w ↦ by
      obtain ⟨φ, hφ₁, hφ₂, hφ₃⟩ :=
        h.exists_lift (a ≫ h₁₃.p₁) (b ≫ h₂₃.p₁) (a ≫ h₁₃.p₂) _ rfl
          (by simpa using w.symm =≫ f₃) (by simp)
      refine ⟨φ, ?_, ?_⟩
      · apply h₁₃.isPullback.hom_ext <;> simpa
      · apply h₂₃.isPullback.hom_ext <;> aesop)

end ChosenPullback₃

end Limits

end CategoryTheory
