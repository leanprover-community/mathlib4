/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ExactSequence

/-!
# Connect two exact sequences

-/

@[expose] public section

namespace CategoryTheory

namespace ShortComplex

open ComposableArrows

variable {C : Type*} [Category C] [Abelian C] (S₁ S₂ : ShortComplex C)
  (hS₁ : S₁.Exact) (hS₂ : S₂.Exact)
  (e : S₁.X₃ ≅ S₂.X₁) (f : S₁.X₂ ⟶ S₂.X₂) (hf : f = S₁.g ≫ e.hom ≫ S₂.f)
  (h₁ : Epi S₁.g) (h₂ : Mono S₂.f)

@[simp]
def connect (e : S₁.X₃ ≅ S₂.X₁) (f : S₁.X₂ ⟶ S₂.X₂) (_ : f = S₁.g ≫ e.hom ≫ S₂.f) :
    ComposableArrows C 3 :=
  mk₃ S₁.f f S₂.g

include h₁ h₂ hS₁ hS₂

set_option backward.isDefEq.respectTransparency false in
lemma connect_exact :
    (connect S₁ S₂ e f hf).Exact :=
  exact_of_δ₀
    (exact₂_mk _ (by simp [Precomp.map, hf]) (by
      let φ : S₁ ⟶ ShortComplex.mk S₁.f f (by simp [hf]) :=
        { τ₁ := 𝟙 _
          τ₂ := 𝟙 _
          τ₃ := e.hom ≫ S₂.f }
      exact (exact_iff_of_epi_of_isIso_of_mono φ).1 hS₁))
    (exact₂_mk _ (by simp [Precomp.map, hf]) (by
      dsimp
      let φ : ShortComplex.mk f S₂.g (by simp [hf]) ⟶ S₂ :=
        { τ₁ := S₁.g ≫ e.hom
          τ₂ := 𝟙 _
          τ₃ := 𝟙 _ }
      have : Epi φ.τ₁ := epi_comp _ _
      exact (exact_iff_of_epi_of_isIso_of_mono φ).2 hS₂))

end ShortComplex

end CategoryTheory
