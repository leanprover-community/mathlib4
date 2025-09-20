/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.CategoryTheory.Monoidal.CommComon_

/-!
# Copy-Discard Categories

Symmetric monoidal categories where every object has commutative
comonoid structure compatible with tensor products.

## Main definitions

* `CopyDiscardCategory` - Category with coherent copy and delete

## Notations

* `Δ[X]` - Copy morphism for X (from ComonObj)
* `ε[X]` - Delete morphism for X (from ComonObj)

## Implementation notes

We use CommComonObj instances to provide the comonoid structure.
The key axioms ensure tensor products respect the comonoid structure.

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]

## Tags

copy-discard, comonoid, symmetric monoidal
-/

namespace CategoryTheory

open MonoidalCategory ComonObj CommComonObj

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- Category where objects have compatible copy and discard operations. -/
class CopyDiscardCategory (C : Type*) [Category C] [MonoidalCategory C]
    extends SymmetricCategory C where
  /-- Every object has commutative comonoid structure. -/
  commComonObj (X : C) : CommComonObj X := by infer_instance
  /-- Tensor products of copies equal copies of tensor products. -/
  copy_tensor (X Y : C) : Δ[X ⊗ Y] = (Δ[X] ⊗ₘ Δ[Y]) ≫ tensorμ X X Y Y := by cat_disch
  /-- Discard distributes over tensor. -/
  discard_tensor (X Y : C) : ε[X ⊗ Y] = (ε[X] ⊗ₘ ε[Y]) ≫ (λ_ (𝟙_ C)).hom := by cat_disch
  /-- Unit axioms. -/
  copy_unit : Δ[𝟙_ C] = (λ_ (𝟙_ C)).inv := by cat_disch
  discard_unit : ε[𝟙_ C] = 𝟙 (𝟙_ C) := by cat_disch

-- This gives access to the CommComonObj instances
attribute [instance] CopyDiscardCategory.commComonObj

open scoped ComonObj

namespace CopyDiscardCategory

variable [CopyDiscardCategory C]

/-! ### Tensor product lemmas -/

-- Note: copy_tensor_simp was removed as it was redundant with copy_tensor

/-- How to discard tensor products. -/
@[simp]
lemma discard_tensor_simp (X Y : C) : ε[X ⊗ Y] = (ε[X] ⊗ₘ ε[Y]) ≫ (λ_ (𝟙_ C)).hom :=
  discard_tensor X Y

end CopyDiscardCategory

end CategoryTheory
