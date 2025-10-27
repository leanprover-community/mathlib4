/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.CategoryTheory.Monoidal.Comon_

/-!
# Copy-Discard Categories

Symmetric monoidal categories where every object has a commutative
comonoid structure compatible with tensor products.

## Main definitions

* `CopyDiscardCategory` - Category with coherent copy and delete

## Notations

* `Δ[X]` - Copy morphism for X (from `ComonObj`)
* `ε[X]` - Delete morphism for X (from `ComonObj`)

## Implementation notes

We use `ComonObj` instances to provide the comonoid structure.
The key axioms ensure tensor products respect the comonoid structure.

## References

* [Cho and Jacobs, *Disintegration and Bayesian inversion via string diagrams*][cho_jacobs_2019]
* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]

## Tags

copy-discard, comonoid, symmetric monoidal
-/

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

/-- Category where objects have compatible copy and discard operations. -/
class CopyDiscardCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]
    extends SymmetricCategory C where
  /-- Every object has commutative comonoid structure. -/
  [comonObj : (X : C) → ComonObj X]
  /-- Every object's comonoid structure is commutative. -/
  [isCommComonObj : (X : C) → IsCommComonObj X]
  /-- Tensor products of copies equal copies of tensor products. -/
  copy_tensor (X Y : C) : Δ[X ⊗ Y] = (Δ[X] ⊗ₘ Δ[Y]) ≫ tensorμ X X Y Y := by cat_disch
  /-- Discard distributes over tensor. -/
  discard_tensor (X Y : C) : ε[X ⊗ Y] = (ε[X] ⊗ₘ ε[Y]) ≫ (λ_ (𝟙_ C)).hom := by cat_disch
    /-- Copy on the unit object. -/
  copy_unit : Δ[𝟙_ C] = (λ_ (𝟙_ C)).inv := by cat_disch
    /-- Discard on the unit object. -/
  discard_unit : ε[𝟙_ C] = 𝟙 (𝟙_ C) := by cat_disch

attribute [instance] CopyDiscardCategory.comonObj CopyDiscardCategory.isCommComonObj

end CategoryTheory
