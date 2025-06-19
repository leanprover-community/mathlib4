/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.ShortComplexFour
import Mathlib.Algebra.Homology.ShortComplex.Refinements
import Mathlib.CategoryTheory.Abelian.Opposite

/-!
# Four lemma

-/

namespace CategoryTheory

open Category Limits Preadditive

variable {C : Type _} [Category C] [Abelian C]
  {K L : ShortComplex₄ C} (φ : K ⟶ L)

namespace ShortComplex₄

lemma four_lemma_mono (hK : K.Exact) (hL : L.shortComplex₁.Exact)
    (hf₁ : Epi φ.τ₁) (hf₂ : Mono φ.τ₂) (hf₄ : Mono φ.τ₄) : Mono φ.τ₃ := by
  rw [mono_iff_cancel_zero]
  intro A₀ x₃ hx₃
  have hx₃' : x₃ ≫ K.h = 0 := by
    rw [← cancel_mono φ.τ₄, assoc, ← φ.commh, reassoc_of% hx₃, zero_comp, zero_comp]
  obtain ⟨A₁, π₁, hπ₁, x₂ : A₁ ⟶ K.X₂, hx₂⟩ := hK.exact₃.exact_up_to_refinements x₃ hx₃'
  dsimp at hx₂
  have hx₂' : (x₂ ≫ φ.τ₂) ≫ L.g = 0 := by
    rw [assoc, φ.commg, ← reassoc_of% hx₂, hx₃, comp_zero]
  obtain ⟨A₂, π₂, hπ₂, y₁ : A₂ ⟶ L.X₁, hy₁⟩ := hL.exact_up_to_refinements (x₂ ≫ φ.τ₂) hx₂'
  dsimp at hy₁
  obtain ⟨A₃, π₃, hπ₃, x₁, hx₁⟩ := surjective_up_to_refinements_of_epi φ.τ₁ y₁
  have hx₁' : x₁ ≫ K.f = π₃ ≫ π₂ ≫ x₂ := by
    simp only [← cancel_mono φ.τ₂, assoc, ← φ.commf, ← reassoc_of% hx₁, hy₁]
  simp only [← cancel_epi π₁, ← cancel_epi π₂, ← cancel_epi π₃, comp_zero, hx₂,
    ← reassoc_of% hx₁', K.zero₁]

lemma four_lemma_epi (hL : L.Exact) (hK : K.shortComplex₂.Exact)
    (hf₁ : Epi φ.τ₁) (hf₃ : Epi φ.τ₃) (hf₄ : Mono φ.τ₄) : Epi φ.τ₂ := by
  have : Mono φ.τ₂.op := by
    exact four_lemma_mono (opMap φ) hL.op hK.op (inferInstance : Epi φ.τ₄.op)
      (inferInstance : Mono φ.τ₃.op) (inferInstance : Mono φ.τ₁.op)
  exact unop_epi_of_mono φ.τ₂.op

end ShortComplex₄

end CategoryTheory
