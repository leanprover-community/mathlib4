/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.CategoryTheory.MarkovCategory.Basic
import Mathlib.CategoryTheory.MarkovCategory.Cartesian
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.CopyDiscardCategory.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Tests for Markov Categories

This file contains tests and examples for the Markov category implementation.

## Tests included

* Basic axiom verification for Type*
* Examples of deterministic morphisms
* Verification of comonoid laws

-/

universe u

open CategoryTheory MarkovCategory CopyDiscardCategory ComonObj

section BasicTests

/-- Type* forms a Markov category via its cartesian structure -/
example : MarkovCategory (Type u) := inferInstance

/-- CartesianMonoidalCategory instance exists for Type* -/
example : CartesianMonoidalCategory (Type u) := inferInstance

end BasicTests

section ComonoidLaws

variable {C : Type u} [Category.{u} C] [MonoidalCategory.{u} C] [MarkovCategory C]

open MonoidalCategory CopyDiscardCategory

/-- The copy operation is commutative -/
example (X : C) : Δ[X] ≫ (β_ X X).hom = Δ[X] := CommComonObj.swap_comul

/-- Left counit law -/
example (X : C) : Δ[X] ≫ (ε[X] ▷ X) = (λ_ X).inv := ComonObj.counit_comul X

/-- Right counit law -/
example (X : C) : Δ[X] ≫ (X ◁ ε[X]) = (ρ_ X).inv := ComonObj.comul_counit X

/-- Coassociativity -/
example (X : C) :
    Δ[X] ≫ (X ◁ Δ[X]) = Δ[X] ≫ (Δ[X] ▷ X) ≫ (α_ X X X).hom :=
  ComonObj.comul_assoc X

/-- Delete is natural -/
example {X Y : C} (f : X ⟶ Y) : f ≫ ε[Y] = ε[X] := MarkovCategory.discard_natural f

end ComonoidLaws

section SimpLemmas

variable {C : Type u} [Category.{u} C] [MonoidalCategory C] [MarkovCategory C]

open MonoidalCategory CopyDiscardCategory

/-- Test that simp lemmas work for counit laws -/
example (X : C) : Δ[X] ≫ (ε[X] ▷ X) = (λ_ X).inv := by simp

/-- Test that simp lemmas work for naturality of delete -/
example {X Y : C} (f : X ⟶ Y) : f ≫ ε[Y] = ε[X] := by simp

/-- Test that simp lemmas work for copy commutativity -/
example (X : C) : Δ[X] ≫ (β_ X X).hom = Δ[X] := by simp

end SimpLemmas
