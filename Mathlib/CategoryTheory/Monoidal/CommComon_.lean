/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.CategoryTheory.Monoidal.Comon_
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Commutative Comonoid Objects

Comonoids where comultiplication is symmetric: swapping outputs gives the same result.

## Main definitions

* `CommComonObj X` - Commutative comonoid structure on X

## Main results

* `swap_comul` - Swapping the two copies does nothing

## Implementation notes

We extend ComonObj and add the commutativity axiom. This requires
a braided monoidal category for the braiding isomorphism.

In cartesian monoidal categories, every object has a unique
commutative comonoid structure (diagonal and terminal morphisms).

## Tags

comonoid, commutative, braided
-/

namespace CategoryTheory

open MonoidalCategory ComonObj

variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]

/-- A comonoid where swapping outputs gives the same result: Δ ≫ σ = Δ. -/
class CommComonObj (X : C) extends ComonObj X where
  /-- Comultiplication commutes with braiding. -/
  isComm : comul ≫ (β_ X X).hom = comul

namespace CommComonObj

variable {X : C} [CommComonObj X]

/-- Swapping the two copies does nothing. -/
@[simp]
lemma swap_comul : Δ[X] ≫ (β_ X X).hom = Δ[X] := isComm

end CommComonObj

end CategoryTheory
