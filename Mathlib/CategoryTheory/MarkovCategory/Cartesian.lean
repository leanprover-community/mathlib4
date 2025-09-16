/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.CategoryTheory.MarkovCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Cartesian Categories as Markov Categories

Shows that cartesian monoidal categories are Markov categories where morphisms are deterministic.

Cartesian categories represent deterministic computation where functions have unique outputs
and information can be duplicated freely. In this setting:
- Copying is the diagonal morphism `Δ : X → X × X`
- Deletion is the unique morphism to the terminal object
- Every morphism preserves copying perfectly (is deterministic)

This shows that Markov categories generalize from deterministic to probabilistic settings,
with cartesian categories as the "zero randomness" case.

## Main definitions

* `diagonalCopy` - The diagonal morphism as copy operation
* `terminalDelete` - The unique morphism to terminal as delete operation

## Main results

* `instMarkovCategoryOfCartesian` - Cartesian monoidal categories are Markov categories
* `deterministic_of_cartesian` - Every morphism in a cartesian category is deterministic
* `copy_eq_diagonal` - The copy operation equals the diagonal
* `del_eq_terminal` - The delete operation equals the terminal morphism

## Tags

Markov category, cartesian category, finite products, deterministic
-/

universe u v

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory

open CopyDiscardCategory

variable {C : Type u} [Category.{v} C]

/-- The diagonal morphism `⟨id, id⟩ : X → X × X` as the copy operation.

In sets, this sends `x ↦ (x, x)`. -/
def diagonalCopy [CartesianMonoidalCategory C] (X : C) : X ⟶ X ⊗ X :=
  CartesianMonoidalCategory.lift (𝟙 X) (𝟙 X)

/-- The unique morphism to the terminal object as the delete operation. -/
def terminalDelete [CartesianMonoidalCategory C] (X : C) : X ⟶ 𝟙_ C :=
  CartesianMonoidalCategory.toUnit X

/-- Cartesian monoidal categories are Markov categories.

This shows that Markov categories include deterministic computation:
all axioms hold when there's no randomness. -/
instance instMarkovCategoryOfCartesian [CartesianMonoidalCategory C] : MarkovCategory C where
  braiding X Y := ⟨CartesianMonoidalCategory.lift (CartesianMonoidalCategory.snd X Y)
                     (CartesianMonoidalCategory.fst X Y),
                   CartesianMonoidalCategory.lift (CartesianMonoidalCategory.snd Y X)
                     (CartesianMonoidalCategory.fst Y X),
                   by ext <;> simp [CartesianMonoidalCategory.lift_fst,
                                    CartesianMonoidalCategory.lift_snd],
                   by ext <;> simp [CartesianMonoidalCategory.lift_fst,
                                    CartesianMonoidalCategory.lift_snd]⟩
  copyMor := diagonalCopy
  delMor := terminalDelete
  copy_comm X := by
    -- Diagonal is symmetric: swapping (x,x) gives (x,x)
    unfold diagonalCopy
    ext <;> simp [CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd]
  counit_comul X := by
    -- Delete first of (x,x) gives x
    unfold diagonalCopy terminalDelete
    ext
    simp
  comul_counit X := by
    -- Delete second of (x,x) gives x
    unfold diagonalCopy terminalDelete
    ext
    simp
  coassoc X := by
    -- Copy either component of (x,x) gives (x,x,x)
    unfold diagonalCopy
    ext <;> simp [CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd]
  copy_tensor X Y := by
    -- Rearrange ((x,y), (x,y)) to ((x,x), (y,y))
    unfold diagonalCopy
    ext <;> simp [middleFourInterchange]
  del_tensor X Y := by
    -- Morphism to terminal is unique
    unfold terminalDelete
    apply CartesianMonoidalCategory.toUnit_unique
  del_natural f := by
    -- Morphism to terminal is unique
    unfold terminalDelete
    apply CartesianMonoidalCategory.toUnit_unique

namespace CartesianMarkov

open MarkovCategory

variable [CartesianMonoidalCategory C]

/-- Every morphism in a cartesian category is deterministic.

All morphisms preserve copying perfectly since there's no randomness. -/
instance deterministic_of_cartesian {X Y : C} (f : X ⟶ Y) : Deterministic f where
  preserves_copy := by
    -- Products preserve: f(x,x) = (f(x), f(x))
    simp only [copyMor, diagonalCopy]
    ext <;> simp [CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd]

/-- The copy operation equals the diagonal. -/
@[simp]
lemma copy_eq_diagonal (X : C) :
    copyMor X = CartesianMonoidalCategory.lift (𝟙 X) (𝟙 X) := rfl

/-- The delete operation equals the terminal morphism. -/
@[simp]
lemma del_eq_terminal (X : C) :
    delMor X = CartesianMonoidalCategory.toUnit X := rfl

/-- First projection after copy gives identity. -/
@[simp, reassoc]
lemma copy_fst (X : C) : copyMor X ≫ CartesianMonoidalCategory.fst X X = 𝟙 X := by
  simp [copy_eq_diagonal, CartesianMonoidalCategory.lift_fst]

/-- Second projection after copy gives identity. -/
@[simp, reassoc]
lemma copy_snd (X : C) : copyMor X ≫ CartesianMonoidalCategory.snd X X = 𝟙 X := by
  simp [copy_eq_diagonal, CartesianMonoidalCategory.lift_snd]

/-- The copy operation satisfies the universal property of products.

Two morphisms are equal if and only if they agree after copying
(true only in deterministic settings). -/
lemma copy_universal {X Y : C} (f g : Y ⟶ X) :
    f = g ↔ f ≫ copyMor X = g ≫ copyMor X := by
  constructor
  · intro h; rw [h]
  · intro h
    rw [copy_eq_diagonal] at h
    have h1 := congr_arg (· ≫ CartesianMonoidalCategory.fst X X) h
    simp [CartesianMonoidalCategory.lift_fst] at h1
    exact h1

end CartesianMarkov

end CategoryTheory
