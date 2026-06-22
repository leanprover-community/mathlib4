/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.IsSmall

/-!
# The solution set condition

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

variable (W : MorphismProperty C)

def solutionSetCondition : MorphismProperty C :=
  fun _ _ m ↦ ∃ (Wm : MorphismProperty C) (_ : IsSmall.{w} Wm) (_ : Wm ≤ W),
    ∀ ⦃X Y : C⦄ (g : X ⟶ Y) (_ : W g) (γ : Arrow.mk m ⟶ Arrow.mk g),
      ∃ (X' Y' : C) (g' : X' ⟶ Y') (_ : Wm g') (α : Arrow.mk m ⟶ Arrow.mk g')
        (β : Arrow.mk g' ⟶ Arrow.mk g), α ≫ β = γ

namespace solutionSetCondition

variable {W} {A B : C} {m : A ⟶ B} (hm : solutionSetCondition.{w} W m)

include hm

def morphismProperty : MorphismProperty C := hm.choose

instance : IsSmall.{w} hm.morphismProperty := hm.choose_spec.choose

lemma morphismProperty_le : hm.morphismProperty ≤ W :=
    hm.choose_spec.choose_spec.choose

variable {X Y : C} (g : X ⟶ Y) (hg : W g) (γ : Arrow.mk m ⟶ Arrow.mk g)

include hg

lemma exists_fac :
    ∃ (X' Y' : C) (g' : X' ⟶ Y') (_ : hm.morphismProperty g')
      (α : Arrow.mk m ⟶ Arrow.mk g') (β : Arrow.mk g' ⟶ Arrow.mk g), α ≫ β = γ :=
  hm.choose_spec.choose_spec.choose_spec g hg γ

noncomputable def src : C := (hm.exists_fac g hg γ).choose

noncomputable def tgt : C := (hm.exists_fac g hg γ).choose_spec.choose

noncomputable def hom : hm.src g hg γ ⟶ hm.tgt g hg γ :=
  (hm.exists_fac g hg γ).choose_spec.choose_spec.choose

lemma prop_hom : hm.morphismProperty (hm.hom g hg γ) :=
  (hm.exists_fac g hg γ).choose_spec.choose_spec.choose_spec.choose

noncomputable def α : Arrow.mk m ⟶ Arrow.mk (hm.hom g hg γ) :=
  (hm.exists_fac g hg γ).choose_spec.choose_spec.choose_spec.choose_spec.choose

noncomputable def β : Arrow.mk (hm.hom g hg γ) ⟶ Arrow.mk g :=
  (hm.exists_fac g hg γ).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

@[reassoc (attr := simp)]
lemma fac : hm.α g hg γ ≫ hm.β g hg γ = γ :=
  (hm.exists_fac g hg γ).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

end solutionSetCondition

end MorphismProperty

end CategoryTheory
