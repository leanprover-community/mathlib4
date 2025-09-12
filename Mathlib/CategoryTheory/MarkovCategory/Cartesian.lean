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

This file shows that cartesian monoidal categories (categories with finite products)
are Markov categories where every morphism is deterministic.

## Mathematical significance

Cartesian categories represent deterministic computation, e.g., the "classical" world where
functions have unique outputs and information can be freely duplicated. By showing these
form Markov categories, we see that:

1. Markov categories generalize from deterministic to probabilistic settings
2. The axioms of Markov categories, when specialized to the deterministic case,
   recover the structure of products
3. Probabilistic and deterministic computation share the same compositional structure

In a cartesian setting, copying is the diagonal morphism
`Δ : X → X × X` (which duplicates data) and deletion is the unique morphism
to the terminal object (which discards data). There is no probabilistic
branching. Every morphism preserves the copy operation perfectly.

## Main definitions

* `diagonalCopy` - The diagonal morphism as copy operation
* `terminalDelete` - The unique morphism to terminal as delete operation

## Main results

* `instMarkovCategoryOfCartesian` - Cartesian monoidal categories are Markov categories
* `deterministic_of_cartesian` - Every morphism in a cartesian category is deterministic
* `copy_eq_diagonal` - The copy operation equals the diagonal
* `del_eq_terminal` - The delete operation equals the terminal morphism

## Implementation notes

We use the existing `CartesianMonoidalCategory` structure which provides
the monoidal structure from finite products. The braiding is constructed from
the product projections and pairing: `swap(x,y) = (y,x)` using `⟨snd, fst⟩`.

The proofs are straightforward because products naturally satisfy the comonoid
axioms; this is the "canonical comonoid" that exists in any cartesian category.
The use of `ext` (extensionality for products) reduces most proofs to the
universal property of products.

## Design rationale

We define this as an instance rather than just a theorem because:
1. It allows cartesian categories to automatically inherit all Markov category theory
2. It provides the canonical test case; any construction or theorem in Markov
   category theory MUST reduce to the correct classical result when specialized to
   cartesian categories. If it doesn't, the construction is wrong.
3. It validates the framework: Shows that Markov categories generalize
   classical categories by including them as the "zero randomness" special case

## Tags

Markov category, cartesian category, finite products, deterministic
-/

universe u v

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- In a cartesian monoidal category, the diagonal provides the copy operation.

This is `⟨id, id⟩ : X → X × X`, which duplicates the value.
In the category of sets/types, this sends `x ↦ (x, x)`. -/
def diagonalCopy [CartesianMonoidalCategory C] (X : C) : X ⟶ X ⊗ X :=
  CartesianMonoidalCategory.lift (𝟙 X) (𝟙 X)

/-- In a cartesian monoidal category, the unique morphism to terminal provides delete.

This discards information; there's no way to recover X from the terminal object.
The uniqueness of this morphism is what makes the unit terminal. -/
def terminalDelete [CartesianMonoidalCategory C] (X : C) : X ⟶ 𝟙_ C :=
  CartesianMonoidalCategory.toUnit X

/-- A cartesian monoidal category forms a Markov category.

This is the key example showing that Markov categories include classical
deterministic computation. All the probabilistic axioms hold when
there's no randomness. -/
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
    -- The diagonal is symmetric: (x,x) and (x,x) are the same regardless of swap
    unfold diagonalCopy
    ext <;> simp [CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd]
  counit_comul X := by
    -- (x,x) then delete first component gives x, matching the left unitor
    unfold diagonalCopy terminalDelete
    ext
    simp
  comul_counit X := by
    -- (x,x) then delete second component gives x, matching the right unitor
    unfold diagonalCopy terminalDelete
    ext
    simp
  coassoc X := by
    -- (x,x) then copy first vs copy second both give (x,x,x)
    unfold diagonalCopy
    ext <;> simp [CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd]
  copy_tensor X Y := by
    -- ((x,y), (x,y)) rearranges to ((x,x), (y,y)) via middleFourInterchange
    unfold diagonalCopy
    ext <;> simp [middleFourInterchange]
  del_tensor X Y := by
    -- Unique morphism to terminal factors through product of terminals
    unfold terminalDelete
    apply CartesianMonoidalCategory.toUnit_unique
  del_natural f := by
    -- Terminal object has exactly one morphism from any object
    unfold terminalDelete
    apply CartesianMonoidalCategory.toUnit_unique

namespace CartesianMarkov

variable [CartesianMonoidalCategory C]

/-- In a cartesian category, every morphism is deterministic.

This is the key property that characterizes cartesian categories as Markov
categories: all morphisms preserve copying perfectly, meaning there's no randomness. -/
instance deterministic_of_cartesian {X Y : C} (f : X ⟶ Y) : Deterministic f where
  preserves_copy := by
    -- f(x,x) = (f(x), f(x)) by the universal property of products
    simp only [MarkovCategory.copyMor, diagonalCopy]
    ext <;> simp [CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd]

/-- The copy operation in a cartesian category is the diagonal -/
@[simp]
lemma copy_eq_diagonal (X : C) :
    MarkovCategory.copyMor X = CartesianMonoidalCategory.lift (𝟙 X) (𝟙 X) := rfl

/-- The delete operation in a cartesian category is the terminal morphism -/
@[simp]
lemma del_eq_terminal (X : C) :
    MarkovCategory.delMor X = CartesianMonoidalCategory.toUnit X := rfl

/-- First projection composed with copy gives identity -/
@[simp, reassoc]
lemma copy_fst (X : C) : MarkovCategory.copyMor X ≫ CartesianMonoidalCategory.fst X X = 𝟙 X := by
  simp [copy_eq_diagonal, CartesianMonoidalCategory.lift_fst]

/-- Second projection composed with copy gives identity -/
@[simp, reassoc]
lemma copy_snd (X : C) : MarkovCategory.copyMor X ≫ CartesianMonoidalCategory.snd X X = 𝟙 X := by
  simp [copy_eq_diagonal, CartesianMonoidalCategory.lift_snd]

/-- The copy operation satisfies the universal property of the product.

This shows that in the cartesian setting, the Markov category copy operation
is the categorical product structure. Two morphisms are equal if and
only if they agree after copying (this is true only in deterministic settings). -/
lemma copy_universal {X Y : C} (f g : Y ⟶ X) :
    f = g ↔ f ≫ MarkovCategory.copyMor X = g ≫ MarkovCategory.copyMor X := by
  constructor
  · intro h; rw [h]
  · intro h
    rw [copy_eq_diagonal] at h
    have h1 := congr_arg (· ≫ CartesianMonoidalCategory.fst X X) h
    simp [CartesianMonoidalCategory.lift_fst] at h1
    exact h1

end CartesianMarkov

end CategoryTheory
