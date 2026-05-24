/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Chosen pullbacks

Given two morphisms `f₁ : X₁ ⟶ S` and `f₂ : X₂ ⟶ S`, we introduce
a structure `ChosenPullback f₁ f₂` which contains the data of
pullback of `f₁` and `f₂`.

## TODO
* relate this to `ChosenPullbacksAlong` which is defined in
`LocallyCartesianClosed.ChosenPullbacksAlong`.

-/

@[expose] public section

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

/-- Given two morphisms `f₁ : X₁ ⟶ S` and `f₂ : X₂ ⟶ S`, this is the choice
of a pullback of `f₁` and `f₂`. -/
structure ChosenPullback {X₁ X₂ S : C} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S) where
  /-- the pullback -/
  pullback : C
  /-- the first projection -/
  p₁ : pullback ⟶ X₁
  /-- the second projection -/
  p₂ : pullback ⟶ X₂
  condition : p₁ ≫ f₁ = p₂ ≫ f₂
  /-- `pullback` is a pullback of `f₁` and `f₂` -/
  isLimit : IsLimit (PullbackCone.mk _ _ condition)
  /-- the projection `pullback ⟶ S` -/
  p : pullback ⟶ S := p₁ ≫ f₁
  hp₁ : p₁ ≫ f₁ = p := by cat_disch

namespace ChosenPullback

section

variable {X₁ X₂ S : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S}
  (h : ChosenPullback f₁ f₂)

attribute [reassoc] condition

lemma isPullback : IsPullback h.p₁ h.p₂ f₁ f₂ where
  w := h.condition
  isLimit' := ⟨h.isLimit⟩

attribute [reassoc (attr := simp, grind =)] hp₁

@[reassoc (attr := simp, grind =)]
lemma hp₂ : h.p₂ ≫ f₂ = h.p := by rw [← h.condition, hp₁]

@[ext]
lemma hom_ext {Y : C} {f g : Y ⟶ h.pullback}
    (h₁ : f ≫ h.p₁ = g ≫ h.p₁) (h₂ : f ≫ h.p₂ = g ≫ h.p₂) :
    f = g :=
  h.isPullback.hom_ext h₁ h₂

/-- Given `f₁ : X₁ ⟶ S`, `f₂ : X₂ ⟶ S`, `h : ChosenPullback f₁ f₂` and morphisms
`g₁ : Y ⟶ X₁`, `g₂ : Y ⟶ X₂` and `b : Y ⟶ S`, this structure contains a morphism
`Y ⟶ h.pullback` such that `f ≫ h.p₁ = g₁`, `f ≫ h.p₂ = g₂` and `f ≫ h.p = b`.
(This is nonempty only when `g₁ ≫ f₁ = g₂ ≫ f₂ = b`.) -/
structure LiftStruct {Y : C} (g₁ : Y ⟶ X₁) (g₂ : Y ⟶ X₂) (b : Y ⟶ S) where
  /-- a lifting to the pullback -/
  f : Y ⟶ h.pullback
  f_p₁ : f ≫ h.p₁ = g₁ := by cat_disch
  f_p₂ : f ≫ h.p₂ = g₂ := by cat_disch
  f_p : f ≫ h.p = b := by cat_disch

namespace LiftStruct

attribute [reassoc (attr := simp, grind =)] f_p₁ f_p₂ f_p

variable {h} {Y : C} {g₁ : Y ⟶ X₁} {g₂ : Y ⟶ X₂} {b : Y ⟶ S}

@[reassoc]
lemma w (l : h.LiftStruct g₁ g₂ b) : g₁ ≫ f₁ = g₂ ≫ f₂ := by
  simp only [← l.f_p₁, ← l.f_p₂, Category.assoc, h.condition]

instance : Subsingleton (h.LiftStruct g₁ g₂ b) where
  allEq := by
    rintro ⟨f, f_p₁, f_p₂, _⟩ ⟨f', f'_p₁, f'_p₂, _⟩
    obtain rfl : f = f' := by cat_disch
    rfl

lemma nonempty (w : g₁ ≫ f₁ = g₂ ≫ f₂) (hf₁ : g₁ ≫ f₁ = b) :
    Nonempty (h.LiftStruct g₁ g₂ b) := by
  obtain ⟨l, h₁, h₂⟩ := h.isPullback.exists_lift g₁ g₂ w
  exact ⟨{
    f := l
    f_p₁ := h₁
    f_p₂ := h₂
    f_p := by rw [← h.hp₁, ← hf₁, reassoc_of% h₁] }⟩

end LiftStruct

end

variable {X S : C} {f : X ⟶ S} (h : ChosenPullback f f)

/-- Given `f : X ⟶ S` and `h : ChosenPullback f f`, this is the type of
morphisms `l : X ⟶ h.pullback` that are equal to the diagonal map. -/
abbrev Diagonal := h.LiftStruct (𝟙 X) (𝟙 X) f

instance : Nonempty h.Diagonal := by apply LiftStruct.nonempty <;> cat_disch

end ChosenPullback

variable {X₁ X₂ X₃ S : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S} {f₃ : X₃ ⟶ S}
  (h₁₂ : ChosenPullback f₁ f₂) (h₂₃ : ChosenPullback f₂ f₃) (h₁₃ : ChosenPullback f₁ f₃)

/-- Given three morphisms `f₁ : X₁ ⟶ S`, `f₂ : X₂ ⟶ S` and `f₃ : X₃ ⟶ S`, and chosen
pullbacks for `(f₁, f₂)`, `(f₂, f₃)` and `(f₁, f₃)`, this structure contains the data
of a wide pullback of the three morphisms `f₁`, `f₂` and `f₃`. -/
structure ChosenPullback₃ where
  /-- A chosen pullback of `h₁₂.pullback` and `h₂₃.pullback` over `X₂`. -/
  chosenPullback : ChosenPullback h₁₂.p₂ h₂₃.p₁
  /-- The projection from the wide pullback of `(f₁, f₂, f₃)` to `S`. -/
  p : chosenPullback.pullback ⟶ S := chosenPullback.p₁ ≫ h₁₂.p
  /-- The projection from the wide pullback of `(f₁, f₂, f₃)` to `X₁`. -/
  p₁ : chosenPullback.pullback ⟶ X₁ := chosenPullback.p₁ ≫ h₁₂.p₁
  /-- The projection from the wide pullback of `(f₁, f₂, f₃)` to `X₃`. -/
  p₃ : chosenPullback.pullback ⟶ X₃ := chosenPullback.p₂ ≫ h₂₃.p₂
  /-- A morphism from the wide pullback `(f₁, f₂, f₃)` to the pullback of `f₁` and `f₃`
  that is compatible with projections. -/
  l : h₁₃.LiftStruct p₁ p₃ p
  hp₁ : chosenPullback.p₁ ≫ h₁₂.p₁ = p₁ := by cat_disch
  hp₃ : chosenPullback.p₂ ≫ h₂₃.p₂ = p₃ := by cat_disch

namespace ChosenPullback₃

variable {h₁₂ h₂₃ h₁₃} (h : ChosenPullback₃ h₁₂ h₂₃ h₁₃)

/-- The chosen wide pullback of `(f₁, f₂, f₃)`. -/
abbrev pullback := h.chosenPullback.pullback

/-- The projection from the wide pullback of `(f₁, f₂, f₃)` to the pullback of `f₁` and `f₃`. -/
def p₁₃ : h.pullback ⟶ h₁₃.pullback := h.l.f

/-- The projection from the wide pullback of `(f₁, f₂, f₃)` to the pullback of `f₁` and `f₂`. -/
def p₁₂ : h.pullback ⟶ h₁₂.pullback := h.chosenPullback.p₁

/-- The projection from the wide pullback of `(f₁, f₂, f₃)` to the pullback of `f₂` and `f₃`. -/
def p₂₃ : h.pullback ⟶ h₂₃.pullback := h.chosenPullback.p₂

/-- The projection from the wide pullback of `(f₁, f₂, f₃)` to `X₂`. -/
def p₂ : h.pullback ⟶ X₂ := h.chosenPullback.p

@[reassoc (attr := simp)]
lemma p₁₂_p₁ : h.p₁₂ ≫ h₁₂.p₁ = h.p₁ := by simp [p₁₂, hp₁]

@[reassoc (attr := simp)]
lemma p₁₂_p₂ : h.p₁₂ ≫ h₁₂.p₂ = h.p₂ := by simp [p₁₂, p₂]

@[reassoc (attr := simp)]
lemma p₂₃_p₂ : h.p₂₃ ≫ h₂₃.p₁ = h.p₂ := by simp [p₂₃, p₂]

@[reassoc (attr := simp)]
lemma p₂₃_p₃ : h.p₂₃ ≫ h₂₃.p₂ = h.p₃ := by simp [p₂₃, hp₃]

@[reassoc (attr := simp)]
lemma p₁₃_p₁ : h.p₁₃ ≫ h₁₃.p₁ = h.p₁ := by simp [p₁₃]

@[reassoc (attr := simp)]
lemma p₁₃_p₃ : h.p₁₃ ≫ h₁₃.p₂ = h.p₃ := by simp [p₁₃]

@[reassoc (attr := simp)]
lemma w₁ : h.p₁ ≫ f₁ = h.p := by
  simpa only [← hp₁, Category.assoc, h₁₃.hp₁, h.l.f_p] using h.l.f_p₁.symm =≫ f₁

@[reassoc (attr := simp)]
lemma w₃ : h.p₃ ≫ f₃ = h.p := by
  simpa only [← hp₃, Category.assoc, h₁₃.hp₂, h.l.f_p] using h.l.f_p₂.symm =≫ f₃

@[reassoc (attr := simp)]
lemma w₂ : h.p₂ ≫ f₂ = h.p := by
  rw [← p₂₃_p₂_assoc, h₂₃.condition, ← w₃, p₂₃_p₃_assoc]

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
  cat_disch

lemma p₂₃_eq_lift : h.p₂₃ = h₂₃.isPullback.lift h.p₂ h.p₃ (by simp) := by
  cat_disch

lemma p₁₃_eq_lift : h.p₁₃ = h₁₃.isPullback.lift h.p₁ h.p₃ (by simp) := by
  cat_disch

lemma exists_lift {Y : C} (g₁ : Y ⟶ X₁) (g₂ : Y ⟶ X₂) (g₃ : Y ⟶ X₃) (b : Y ⟶ S)
    (hg₁ : g₁ ≫ f₁ = b) (hg₂ : g₂ ≫ f₂ = b) (hg₃ : g₃ ≫ f₃ = b) :
    ∃ (φ : Y ⟶ h.pullback), φ ≫ h.p₁ = g₁ ∧ φ ≫ h.p₂ = g₂ ∧ φ ≫ h.p₃ = g₃ := by
  obtain ⟨φ₁₂, w₁, w₂⟩ := h₁₂.isPullback.exists_lift g₁ g₂ (by cat_disch)
  obtain ⟨φ₂₃, w₂', w₃⟩ := h₂₃.isPullback.exists_lift g₂ g₃ (by cat_disch)
  obtain ⟨φ, w₁₂, w₂₃⟩ := h.chosenPullback.isPullback.exists_lift φ₁₂ φ₂₃ (by cat_disch)
  refine ⟨φ, ?_, ?_, ?_⟩
  · rw [← w₁, ← w₁₂, Category.assoc, ← p₁₂, p₁₂_p₁]
  · rw [← w₂, ← w₁₂, Category.assoc, ← p₁₂, p₁₂_p₂]
  · rw [← w₃, ← w₂₃, Category.assoc, ← p₂₃, p₂₃_p₃]

lemma isPullback₂ : IsPullback h.p₁₂ h.p₂₃ h₁₂.p₂ h₂₃.p₁ := h.chosenPullback.isPullback

@[ext]
lemma hom_ext {Y : C} {φ φ' : Y ⟶ h.pullback}
    (h₁ : φ ≫ h.p₁ = φ' ≫ h.p₁) (h₂ : φ ≫ h.p₂ = φ' ≫ h.p₂)
    (h₃ : φ ≫ h.p₃ = φ' ≫ h.p₃) : φ = φ' := by
  apply h.isPullback₂.hom_ext <;> cat_disch

lemma isPullback₁ : IsPullback h.p₁₂ h.p₁₃ h₁₂.p₁ h₁₃.p₁ :=
  .mk' (by simp) (fun _ _ _ h₁ h₂ ↦ h.hom_ext (by simpa using h₁ =≫ h₁₂.p₁)
      (by simpa using h₁ =≫ h₁₂.p₂) (by simpa using h₂ =≫ h₁₃.p₂))
    (fun _ a b w ↦ by
      obtain ⟨φ, hφ₁, hφ₂, hφ₃⟩ :=
        h.exists_lift (a ≫ h₁₂.p₁) (a ≫ h₁₂.p₂) (b ≫ h₁₃.p₂) _ rfl
          (by simp) (by simpa using w.symm =≫ f₁)
      exact ⟨φ, by cat_disch, by cat_disch⟩)

lemma isPullback₃ : IsPullback h.p₁₃ h.p₂₃ h₁₃.p₂ h₂₃.p₂ :=
  .mk' (by simp) (fun _ _ _ h₁ h₂ ↦ h.hom_ext (by simpa using h₁ =≫ h₁₃.p₁)
      (by simpa using h₂ =≫ h₂₃.p₁) (by simpa using h₁ =≫ h₁₃.p₂))
    (fun _ a b w ↦ by
      obtain ⟨φ, hφ₁, hφ₂, hφ₃⟩ :=
        h.exists_lift (a ≫ h₁₃.p₁) (b ≫ h₂₃.p₁) (a ≫ h₁₃.p₂) _ rfl
          (by simpa using w.symm =≫ f₃) (by simp)
      exact ⟨φ, by cat_disch, by cat_disch⟩)

end ChosenPullback₃

end CategoryTheory.Limits
