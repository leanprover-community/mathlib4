/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Comon_
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# Markov Categories

This file defines Markov categories, which give a categorical approach to
probability theory and information flow.

A Markov category is a symmetric monoidal category where every object carries a
canonical commutative comonoid structure that is compatible with the tensor product.
Copying (comultiplication) represents perfect correlation
while deletion (counit) represents marginalization.

## Mathematical intuition

Markov categories capture how conditional probabilities compose.
Morphisms `f : X → Y` represent stochastic processes that transform states of type `X`
into distributions over `Y`. The tensor product models parallel composition of
independent processes, while sequential composition follows the Chapman-Kolmogorov
equation. The copy and delete operations capture key information operations:
duplication creates correlation, while deletion marginalizes.

## Main definitions

* `MarkovCategory` - A symmetric monoidal category with canonical comonoid structure
* `middleFourInterchange` - Helper morphism for tensor-copy compatibility
* `MarkovCategory.copyMor` - The canonical copy morphism `X → X ⊗ X`
* `MarkovCategory.delMor` - The canonical delete morphism `X → I`
* `Deterministic` - Morphisms that preserve the copy operation

## Notations

* `Δ[X]` - Copy morphism for object `X`
* `ε[X]` - Delete morphism for object `X`

## Examples

* Finite stochastic matrices (`FinStoch`) - morphisms are conditional probability tables
* Cartesian categories - every morphism is deterministic, copying is the diagonal
* Kleisli categories of probability monads - e.g., distributions, measures
* Quantum channels (completely positive maps) - with suitable restrictions

## Implementation notes

We implement the comonoid structure as fields of the MarkovCategory typeclass rather
than using separate Comon structures. This design ensures the comonoid is canonical
(every object has exactly one way to be copied/deleted) rather than merely chosen,
which is essential for the probabilistic interpretation.

The condition `del_natural` forces the monoidal unit to be terminal, separating
Markov categories from more general copy-discard categories. Without this, we could
have "information sinks" that aren't true marginalization. This property ensures
that deleting information is independent of how it was processed, matching the
probabilistic idea that marginalization discards all information uniformly.

The choice to extend `SymmetricCategory` rather than just `BraidedCategory` reflects
that in probability theory, the order of independent events doesn't matter.

## Historical context

The categorical approach to probability traces back to Lawvere's work on probabilistic
theories. The modern formulation as Markov categories was developed by Fritz (2020),
unifying earlier work on categorical probability, quantum information, and graphical models.

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]

## Tags

Markov category, probability, categorical probability, comonoid, stochastic
-/

universe u v

namespace CategoryTheory

open MonoidalCategory

section HelperMorphisms

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [BraidedCategory.{v} C]

/-- The middle four interchange morphism, rearranging (W ⊗ X) ⊗ (Y ⊗ Z) to (W ⊗ Y) ⊗ (X ⊗ Z).

This morphism is needed to express how copying distributes over
tensor products. When we copy a pair of independent objects, we get two pairs where
the first components are correlated and the second components are correlated, but
the pairs remain independent. This morphism rearranges the tensor products to group
the correlated components together. -/
def middleFourInterchange (W X Y Z : C) : (W ⊗ X) ⊗ (Y ⊗ Z) ⟶ (W ⊗ Y) ⊗ (X ⊗ Z) :=
  (α_ W X (Y ⊗ Z)).hom ≫
  (𝟙 W ⊗ₘ (α_ X Y Z).inv) ≫
  (𝟙 W ⊗ₘ ((β_ X Y).hom ⊗ₘ 𝟙 Z)) ≫
  (𝟙 W ⊗ₘ (α_ Y X Z).hom) ≫
  (α_ W Y (X ⊗ Z)).inv

end HelperMorphisms

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

/-- A Markov category is a symmetric monoidal category where every object
carries a canonical commutative comonoid structure compatible with the tensor product.

This captures the key structure of probabilistic computations:
morphisms represent conditional probabilities or stochastic processes, while the
comonoid structure provides copying (creating correlation) and deletion (marginalization).
The monoidal unit being terminal ensures a true probabilistic interpretation. -/
class MarkovCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]
extends SymmetricCategory.{v} C where
  /-- The canonical copy morphism for each object.
  In deterministic settings, this is duplication/cloning. In probabilistic settings,
  it creates perfect correlation: both outputs always have the same value. -/
  copyMor : ∀ X : C, X ⟶ X ⊗ X
  /-- The canonical delete morphism for each object.
  In probability theory, this is marginalization, i.e., summing/integrating out a variable.
  In computation, it's discarding a value. -/
  delMor : ∀ X : C, X ⟶ 𝟙_ C
  /-- The copy operation is commutative: swapping the copies gives the same result.
  This shows that correlation is symmetric. If A and B are perfectly correlated,
  which one is "first" doesn't matter. -/
  copy_comm : ∀ X, copyMor X ≫ (β_ X X).hom = copyMor X
  /-- Left counit law: copying then deleting the first copy recovers the original.
  This ensures marginalization is the inverse of creating correlation. -/
  counit_comul : ∀ X, copyMor X ≫ (delMor X ▷ X) = (λ_ X).inv
  /-- Right counit law: copying then deleting the second copy recovers the original.
  Together with `counit_comul`, this ensures both marginals equal the original distribution. -/
  comul_counit : ∀ X, copyMor X ≫ (X ◁ delMor X) = (ρ_ X).inv
  /-- Coassociativity: copying then copying the first output equals copying then
  copying the second output (up to reassociation). This means we can unambiguously
  create multiple correlated copies. -/
  coassoc : ∀ X, copyMor X ≫ (copyMor X ▷ X) = copyMor X ≫ (X ◁ copyMor X) ≫ (α_ X X X).inv
  /-- Compatibility of copy with tensor product: copying a pair creates two pairs
  where corresponding components are correlated. The rearrangement via
  `middleFourInterchange` groups the correlated components. -/
  copy_tensor : ∀ X Y, copyMor (X ⊗ Y) =
    (copyMor X ⊗ₘ copyMor Y) ≫ middleFourInterchange X X Y Y
  /-- Compatibility of delete with tensor product: marginalizing over a product
  equals marginalizing over each component independently. -/
  del_tensor : ∀ X Y, delMor (X ⊗ Y) = (delMor X ⊗ₘ delMor Y) ≫ (λ_ (𝟙_ C)).hom
  /-- Delete is natural: marginalization commutes with all morphisms.
  This forces the monoidal unit to be terminal, ensuring that "deleting" truly
  discards all information regardless of how it was processed. This is the key
  difference from general copy-discard categories. -/
  del_natural : ∀ {X Y} (f : X ⟶ Y), f ≫ delMor Y = delMor X

namespace MarkovCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [MarkovCategory C]

/-- Notation for the copy morphism in a Markov category -/
scoped notation "Δ[" X "]" => copyMor X

/-- Notation for the delete morphism in a Markov category -/
scoped notation "ε[" X "]" => delMor X

/-- Every object in a Markov category has a canonical comonoid structure.

This automatic instance shows that copyability is built into the structure
of a Markov category; we don't choose how to copy objects, there's exactly
one way prescribed by the category structure. This canonicity is essential
for the probabilistic interpretation. -/
instance instComonObj (X : C) : ComonObj X where
  counit := ε[X]
  comul := Δ[X]
  counit_comul := by simp only [counit_comul]
  comul_counit := by simp only [comul_counit]
  comul_assoc := by
    -- We need to reconcile our coassociativity convention with Comon_'s.
    -- MarkovCategory uses (α_)⁻¹ while Comon_ uses α
    have h := coassoc X
    calc Δ[X] ≫ X ◁ Δ[X]
      = Δ[X] ≫ X ◁ Δ[X] ≫ 𝟙 _ := by rw [Category.comp_id]
      _ = Δ[X] ≫ X ◁ Δ[X] ≫ ((α_ X X X).inv ≫ (α_ X X X).hom) := by rw [Iso.inv_hom_id]
      _ = (Δ[X] ≫ X ◁ Δ[X] ≫ (α_ X X X).inv) ≫ (α_ X X X).hom := by
        rw [Category.assoc, Category.assoc]
      _ = (Δ[X] ≫ Δ[X] ▷ X) ≫ (α_ X X X).hom := by rw [← h]
      _ = Δ[X] ≫ Δ[X] ▷ X ≫ (α_ X X X).hom := by rw [Category.assoc]

/-- The copy morphism is natural for deterministic morphisms -/
lemma copy_natural_of_deterministic {X Y : C} (f : X ⟶ Y)
    (h : f ≫ Δ[Y] = Δ[X] ≫ (f ⊗ₘ f)) : f ≫ Δ[Y] = Δ[X] ≫ (f ⊗ₘ f) := h

/-- The identity morphism preserves the comonoid structure -/
@[simp]
lemma id_copy (X : C) : 𝟙 X ≫ Δ[X] = Δ[X] := Category.id_comp _

/-- The identity morphism preserves the delete operation -/
@[simp]
lemma id_del (X : C) : 𝟙 X ≫ ε[X] = ε[X] := Category.id_comp _

/-- **Left counit law**: Copying then deleting the first copy recovers the original.
This is a fundamental property of the comonoid structure, ensuring that marginalization
is the inverse of creating correlation. -/
@[simp, reassoc]
lemma copy_comp_del_left (X : C) : Δ[X] ≫ (ε[X] ▷ X) = (λ_ X).inv := counit_comul X

/-- **Right counit law**: Copying then deleting the second copy recovers the original.
Together with `copy_comp_del_left`, this ensures both marginals equal the original
distribution. -/
@[simp, reassoc]
lemma copy_comp_del_right (X : C) : Δ[X] ≫ (X ◁ ε[X]) = (ρ_ X).inv := comul_counit X

/-- Copying is commutative: swapping the copies gives the same result.
This shows that correlation is symmetric. -/
@[simp, reassoc]
lemma copy_comp_braiding (X : C) : Δ[X] ≫ (β_ X X).hom = Δ[X] := copy_comm X

/-- **Coassociativity**: Copying then copying the first output equals copying then
copying the second output (up to reassociation). This means we can create multiple
correlated copies without ambiguity. -/
@[simp, reassoc]
lemma copy_comp_copy_left (X : C) :
    Δ[X] ≫ (Δ[X] ▷ X) = Δ[X] ≫ (X ◁ Δ[X]) ≫ (α_ X X X).inv := coassoc X

/-- Copying distributes over tensor products via the middle four interchange.
This shows how copying preserves the independence structure. -/
@[simp]
lemma copy_tensor_eq (X Y : C) :
    Δ[X ⊗ Y] = (Δ[X] ⊗ₘ Δ[Y]) ≫ middleFourInterchange X X Y Y := copy_tensor X Y

/-- Deletion distributes over tensor products.
Marginalizing over a product equals marginalizing over each component. -/
@[simp]
lemma del_tensor_eq (X Y : C) :
    ε[X ⊗ Y] = (ε[X] ⊗ₘ ε[Y]) ≫ (λ_ (𝟙_ C)).hom := del_tensor X Y

/-- Deletion is natural: it commutes with all morphisms.
This forces the monoidal unit to be terminal. -/
@[simp, reassoc]
lemma del_natural_simp {X Y : C} (f : X ⟶ Y) : f ≫ ε[Y] = ε[X] := del_natural f

end MarkovCategory

/-- A morphism in a Markov category is deterministic if it preserves the copy operation.

Deterministic morphisms are the "pure" functions that preserve correlations perfectly.
In truly probabilistic categories, these are the non-randomized morphisms.
All morphisms in cartesian categories are deterministic, but a Markov category
can have both deterministic and truly stochastic morphisms. -/
class Deterministic {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [MarkovCategory C]
{X Y : C} (f : X ⟶ Y) : Prop where
  preserves_copy : f ≫ MarkovCategory.copyMor Y = MarkovCategory.copyMor X ≫ (f ⊗ₘ f)

namespace Deterministic

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
  [MarkovCategory C] {X Y Z : C}

/-- The identity morphism is deterministic -/
instance : Deterministic (𝟙 X) where
  preserves_copy := by simp

/-- Composition of deterministic morphisms is deterministic -/
instance (f : X ⟶ Y) (g : Y ⟶ Z) [Deterministic f] [Deterministic g] :
    Deterministic (f ≫ g) where
  preserves_copy := by
    rw [Category.assoc, Deterministic.preserves_copy, ← Category.assoc,
        Deterministic.preserves_copy, Category.assoc]
    simp only [← MonoidalCategory.tensor_comp]

/-- Deterministic morphisms preserve the delete operation.

Note that ALL morphisms preserve delete (by `del_natural`), not just deterministic ones.
This lemma exists for convenience when working with deterministic morphisms. -/
lemma preserves_del {f : X ⟶ Y} [Deterministic f] :
    f ≫ MarkovCategory.delMor Y = MarkovCategory.delMor X :=
  MarkovCategory.del_natural f

end Deterministic

end CategoryTheory
