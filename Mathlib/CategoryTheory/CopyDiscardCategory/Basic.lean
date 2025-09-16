/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Comon_
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# Copy-Discard Categories

This file defines copy-discard (CD) categories, which model how we can duplicate
and delete information.

A CD category is a symmetric monoidal category where every object has a fixed
way to copy and delete itself. These operations work well with tensor products.
Copying duplicates information; deletion removes it.

## Key ideas

CD categories model information flow without normalization. Unlike Markov categories
(which require natural deletion), CD categories allow non-normalized processes.

Duplication and deletion make sense without probability. CD categories model:
- Resource management in programs
- Information flow without probability
- Quantum-like systems without normalization
- Computation with explicit resources

## Main definitions

* `CopyDiscardCategory` - Symmetric monoidal category with comonoid structure
* `middleFourInterchange` - Rearranges tensor products for copying
* `CopyDiscardCategory.copyMor` - Copy morphism `X → X ⊗ X`
* `CopyDiscardCategory.delMor` - Delete morphism `X → I`

## Notations

* `Δ[X]` - Copy morphism for object `X`
* `ε[X]` - Delete morphism for object `X`

## Related structures

* **Markov categories**: Add natural deletion (see `MarkovCategory`)
* **Cartesian categories**: All morphisms preserve copying perfectly
* **Comonoid objects**: Every object has fixed comonoid structure

## Design notes

We make the comonoid structure part of the typeclass, not separate.
This ensures each object has exactly one way to copy and delete.

We extend `SymmetricCategory`, not just `BraidedCategory`, because
order rarely matters for independent processes.

## References

* [Coecke and Perdrix,
  *Environment and classical channels in categorical quantum mechanics*][coecke2012]
* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]

## Tags

copy-discard category, garbage-share category, comonoid, information flow
-/

universe u v

namespace CategoryTheory

open MonoidalCategory

section HelperMorphisms

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [BraidedCategory.{v} C]

/-- Rearranges `(W ⊗ X) ⊗ (Y ⊗ Z)` to `(W ⊗ Y) ⊗ (X ⊗ Z)`.

Used to express how copying distributes over tensor products:
copying `X ⊗ Y` gives `(X ⊗ Y) ⊗ (X ⊗ Y)`, which we rearrange to `(X ⊗ X) ⊗ (Y ⊗ Y)`. -/
def middleFourInterchange (W X Y Z : C) : (W ⊗ X) ⊗ (Y ⊗ Z) ⟶ (W ⊗ Y) ⊗ (X ⊗ Z) :=
  (α_ W X (Y ⊗ Z)).hom ≫
  (𝟙 W ⊗ₘ (α_ X Y Z).inv) ≫
  (𝟙 W ⊗ₘ ((β_ X Y).hom ⊗ₘ 𝟙 Z)) ≫
  (𝟙 W ⊗ₘ (α_ Y X Z).hom) ≫
  (α_ W Y (X ⊗ Z)).inv

end HelperMorphisms

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

/-- A symmetric monoidal category where every object has a fixed way to copy and delete itself.

These operations work with tensor products: copying a pair duplicates both components,
and deleting a pair means deleting both parts. -/
class CopyDiscardCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]
extends SymmetricCategory.{v} C where
  /-- Copy morphism that duplicates an object: `X → X ⊗ X`. -/
  copyMor : ∀ X : C, X ⟶ X ⊗ X
  /-- Delete morphism that discards an object: `X → 𝟙`. -/
  delMor : ∀ X : C, X ⟶ 𝟙_ C
  /-- Copying is symmetric: swapping the two copies gives the same result. -/
  copy_comm : ∀ X, copyMor X ≫ (β_ X X).hom = copyMor X
  /-- Copying then deleting the first copy recovers the original. -/
  counit_comul : ∀ X, copyMor X ≫ (delMor X ▷ X) = (λ_ X).inv
  /-- Copying then deleting the second copy recovers the original. -/
  comul_counit : ∀ X, copyMor X ≫ (X ◁ delMor X) = (ρ_ X).inv
  /-- Copying twice (either copy first) gives three copies arranged the same way. -/
  coassoc : ∀ X, copyMor X ≫ (copyMor X ▷ X) = copyMor X ≫ (X ◁ copyMor X) ≫ (α_ X X X).inv
  /-- Copying a tensor product: `copy(X ⊗ Y)` rearranges to `(X ⊗ X) ⊗ (Y ⊗ Y)`. -/
  copy_tensor : ∀ X Y, copyMor (X ⊗ Y) =
    (copyMor X ⊗ₘ copyMor Y) ≫ middleFourInterchange X X Y Y
  /-- Deleting a tensor product means deleting both components. -/
  del_tensor : ∀ X Y, delMor (X ⊗ Y) = (delMor X ⊗ₘ delMor Y) ≫ (λ_ (𝟙_ C)).hom

namespace CopyDiscardCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [CopyDiscardCategory C]

/-- Notation for the copy morphism in a copy-discard category -/
scoped notation "Δ[" X "]" => copyMor X

/-- Notation for the delete morphism in a copy-discard category -/
scoped notation "ε[" X "]" => delMor X

/-- Every object in a copy-discard category forms a comonoid using its copy and delete morphisms. -/
instance instComonObj (X : C) : ComonObj X where
  counit := ε[X]
  comul := Δ[X]
  counit_comul := by simp only [counit_comul]
  comul_counit := by simp only [comul_counit]
  comul_assoc := by
    -- Convert between conventions: we use (α_)⁻¹, Comon_ uses α
    have h := coassoc X
    calc Δ[X] ≫ X ◁ Δ[X]
      = Δ[X] ≫ X ◁ Δ[X] ≫ 𝟙 _ := by rw [Category.comp_id]
      _ = Δ[X] ≫ X ◁ Δ[X] ≫ ((α_ X X X).inv ≫ (α_ X X X).hom) := by rw [Iso.inv_hom_id]
      _ = (Δ[X] ≫ X ◁ Δ[X] ≫ (α_ X X X).inv) ≫ (α_ X X X).hom := by
        rw [Category.assoc, Category.assoc]
      _ = (Δ[X] ≫ Δ[X] ▷ X) ≫ (α_ X X X).hom := by rw [← h]
      _ = Δ[X] ≫ Δ[X] ▷ X ≫ (α_ X X X).hom := by rw [Category.assoc]

/-- The identity morphism preserves copying. -/
@[simp]
lemma id_copy (X : C) : 𝟙 X ≫ Δ[X] = Δ[X] := Category.id_comp _

/-- The identity morphism preserves deletion. -/
@[simp]
lemma id_del (X : C) : 𝟙 X ≫ ε[X] = ε[X] := Category.id_comp _

/-- Copying then deleting the first copy recovers the original. -/
@[simp, reassoc]
lemma copy_comp_del_left (X : C) : Δ[X] ≫ (ε[X] ▷ X) = (λ_ X).inv := counit_comul X

/-- Copying then deleting the second copy recovers the original. -/
@[simp, reassoc]
lemma copy_comp_del_right (X : C) : Δ[X] ≫ (X ◁ ε[X]) = (ρ_ X).inv := comul_counit X

/-- Copying is symmetric: swapping the copies gives the same result. -/
@[simp, reassoc]
lemma copy_comp_braiding (X : C) : Δ[X] ≫ (β_ X X).hom = Δ[X] := copy_comm X

/-- Copying then copying the first output equals copying then copying the second output. -/
@[simp, reassoc]
lemma copy_comp_copy_left (X : C) :
    Δ[X] ≫ (Δ[X] ▷ X) = Δ[X] ≫ (X ◁ Δ[X]) ≫ (α_ X X X).inv := coassoc X

/-- Copying a tensor product: `copy(X ⊗ Y)` rearranges to `(X ⊗ X) ⊗ (Y ⊗ Y)`. -/
@[simp]
lemma copy_tensor_eq (X Y : C) :
    Δ[X ⊗ Y] = (Δ[X] ⊗ₘ Δ[Y]) ≫ middleFourInterchange X X Y Y := copy_tensor X Y

/-- Deleting a tensor product means deleting both components. -/
@[simp]
lemma del_tensor_eq (X Y : C) :
    ε[X ⊗ Y] = (ε[X] ⊗ₘ ε[Y]) ≫ (λ_ (𝟙_ C)).hom := del_tensor X Y

end CopyDiscardCategory

end CategoryTheory
