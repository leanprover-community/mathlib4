/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.CategoryTheory.CopyDiscardCategory.Basic

/-!
# Deterministic Morphisms in Copy-Discard Categories

Morphisms that preserve the copy operation perfectly.

A morphism `f : X → Y` is deterministic if copying then applying `f` to both copies equals applying
`f` then copying: `f ≫ Δ[Y] = Δ[X] ≫ (f ⊗ f)`.

In probabilistic settings, these are morphisms without randomness. In cartesian categories, all
morphisms are deterministic.

## Main definitions

* `Deterministic` - Type class for morphisms that preserve copying

## Main results

* Identity morphisms are deterministic
* Composition of deterministic morphisms is deterministic

## Tags

deterministic, copy-discard category, comonoid morphism
-/

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [CopyDiscardCategory.{v} C]

/-- A morphism is deterministic if it preserves the comonoid structure.

In probabilistic contexts, these are morphisms without randomness. -/
abbrev Deterministic {X Y : C} (f : X ⟶ Y) := IsComonHom f

namespace Deterministic

variable {X Y Z : C}

/-- Deterministic morphisms commute with copying. -/
lemma copy_natural (f : X ⟶ Y) [Deterministic f] : f ≫ Δ[Y] = Δ[X] ≫ (f ⊗ₘ f) :=
  IsComonHom.hom_comul f

/-- Deterministic morphisms commute with discarding. -/
lemma discard_natural (f : X ⟶ Y) [Deterministic f] : f ≫ ε[Y] = ε[X] :=
  IsComonHom.hom_counit f

end Deterministic

end CategoryTheory
