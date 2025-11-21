/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Presentable.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Retract

/-!
# Presentable objects are stable under retracts

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

lemma Retract.isCardinalPresentable
    {X Y : C} (h : Retract Y X) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalPresentable X κ] :
    IsCardinalPresentable Y κ where
  preservesColimitOfShape J _ _ := ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨by
    have := essentiallySmallSelf J
    have := isFiltered_of_isCardinalFiltered J κ
    refine Types.FilteredColimit.isColimitOf' _ _ (fun f ↦ ?_) (fun j f₁ f₂ hf ↦ ?_)
    · obtain ⟨i, g, hg⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hc (h.r ≫ f)
      exact ⟨i, h.i ≫ g, by simp [hg]⟩
    · dsimp at f₁ f₂ hf ⊢
      obtain ⟨k, u, hj⟩ := IsCardinalPresentable.exists_eq_of_isColimit'
        κ hc (h.r ≫ f₁) (h.r ≫ f₂) (by simp [hf])
      exact ⟨k, u, by simpa [← cancel_epi h.r] using hj⟩⟩⟩⟩

instance (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    (isCardinalPresentable C κ).IsStableUnderRetracts where
  of_retract {Y X} h hX := by
    rw [isCardinalPresentable_iff] at hX ⊢
    exact h.isCardinalPresentable κ

end CategoryTheory
