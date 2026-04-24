/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# API for compositions of two arrows

Given morphisms `f : i ⟶ j`, `g : j ⟶ k`, and `fg : i ⟶ k` in a category `C`
such that `f ≫ g = fg`, we define maps `twoδ₂Toδ₁ : mk₁ f ⟶ mk₁ fg` and
`twoδ₁Toδ₀ : mk₁ fg ⟶ mk₁ g` in the category `ComposableArrows C 1`.
The names are justified by the fact that `ComposableArrow.mk₂ f g`
can be thought of as a `2`-simplex in the simplicial set `nerve C`,
and its faces (numbered from `0` to `2`) are respectively `mk₁ g`,
`mk₁ fg` and `mk₁ f`.

-/

@[expose] public section

namespace CategoryTheory

namespace ComposableArrows

section

variable {C : Type*} [Category* C]
  {i j k : C} (f : i ⟶ j) (g : j ⟶ k) (fg : i ⟶ k)

set_option backward.isDefEq.respectTransparency false in
/-- The morphism `mk₁ f ⟶ mk₁ fg` when `f ≫ g = fg` for some morphism `g`. -/
def twoδ₂Toδ₁ (h : f ≫ g = fg := by cat_disch) :
    mk₁ f ⟶ mk₁ fg :=
  homMk₁ (𝟙 _) g

set_option backward.isDefEq.respectTransparency false in
/-- The morphism `mk₁ fg ⟶ mk₁ g` when `f ≫ g = fg` for some morphism `f`. -/
def twoδ₁Toδ₀ (h : f ≫ g = fg := by cat_disch) :
    mk₁ fg ⟶ mk₁ g :=
  homMk₁ f (𝟙 _)

variable (h : f ≫ g = fg)

@[simp]
lemma twoδ₂Toδ₁_app_zero :
    (twoδ₂Toδ₁ f g fg h).app 0 = 𝟙 _ := by with_unfolding_all rfl

@[simp]
lemma twoδ₂Toδ₁_app_one :
    (twoδ₂Toδ₁ f g fg h).app 1 = g := by with_unfolding_all rfl

@[simp]
lemma twoδ₁Toδ₀_app_zero :
    (twoδ₁Toδ₀ f g fg h).app 0 = f := by with_unfolding_all rfl

@[simp]
lemma twoδ₁Toδ₀_app_one :
    (twoδ₁Toδ₀ f g fg h).app 1 = 𝟙 _ := by with_unfolding_all rfl

#adaptation_note /-- Proof repaired after leanprover/lean4#13363.
The proof body used to be just
```
rw [isIso_iff₁]
constructor <;> dsimp <;> infer_instance
```
The replacement proof is a short-term fix, and we request that the authors/maintainers of
this file review the proof, and either approve it by removing this adaptation note, revise
the proof or the prerequisites appropriately, or minimize a problem in lean4 that still
needs addressing. -/
set_option backward.isDefEq.respectTransparency false in
instance [IsIso g] : IsIso (twoδ₂Toδ₁ f g fg h) := by
  rw [isIso_iff₁, twoδ₂Toδ₁_app_zero, twoδ₂Toδ₁_app_one]
  exact ⟨inferInstance, ‹_›⟩

#adaptation_note /-- Proof repaired after leanprover/lean4#13363.
The proof body used to be just
```
rw [isIso_iff₁]
constructor <;> dsimp <;> infer_instance
```
The replacement proof is a short-term fix, and we request that the authors/maintainers of
this file review the proof, and either approve it by removing this adaptation note, revise
the proof or the prerequisites appropriately, or minimize a problem in lean4 that still
needs addressing. -/
set_option backward.isDefEq.respectTransparency false in
instance [IsIso f] : IsIso (twoδ₁Toδ₀ f g fg h) := by
  rw [isIso_iff₁, twoδ₁Toδ₀_app_zero, twoδ₁Toδ₀_app_one]
  exact ⟨‹_›, inferInstance⟩

end

section

variable {ι : Type*} [Preorder ι] (i₀ i₁ i₂ : ι) (hi₀₁ : i₀ ≤ i₁) (hi₁₂ : i₁ ≤ i₂)

/-- Variant of `twoδ₁Toδ₀` for preorders. -/
abbrev twoδ₁Toδ₀' :
    mk₁ (homOfLE (hi₀₁.trans hi₁₂)) ⟶ mk₁ (homOfLE hi₁₂) :=
  twoδ₁Toδ₀ (homOfLE hi₀₁) _ _ rfl

/-- Variant of `twoδ₂Toδ₁` for preorders. -/
abbrev twoδ₂Toδ₁' :
     mk₁ (homOfLE hi₀₁) ⟶ mk₁ (homOfLE (hi₀₁.trans hi₁₂)) :=
  twoδ₂Toδ₁ _ (homOfLE hi₁₂) _ rfl

end

end ComposableArrows

end CategoryTheory
