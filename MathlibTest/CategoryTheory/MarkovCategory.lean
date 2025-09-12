/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.CategoryTheory.MarkovCategory.Basic
import Mathlib.CategoryTheory.MarkovCategory.Cartesian
import Mathlib.CategoryTheory.MarkovCategory.FinStoch.Basic
import Mathlib.CategoryTheory.MarkovCategory.FinStoch.Monoidal
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.Tactic.FinCases

/-!
# Tests for Markov Categories

This file contains tests and examples for the Markov category implementation.

## Tests included

* Basic axiom verification for Type*
* Examples of deterministic morphisms
* Stochastic matrix examples in FinStoch
* Verification of comonoid laws

-/

universe u

open CategoryTheory MarkovCategory

section BasicTests

/-- Type* forms a Markov category via its cartesian structure -/
example : MarkovCategory (Type u) := inferInstance

/-- Every function between types is deterministic -/
example {X Y : Type u} (f : X → Y) : @Deterministic (Type u) _ _ _ X Y f :=
  @CartesianMarkov.deterministic_of_cartesian (Type u) _ _ X Y f

/-- CartesianMonoidalCategory instance exists for Type* -/
example : CartesianMonoidalCategory (Type u) := inferInstance

end BasicTests

section ComonoidLaws

variable {C : Type u} [Category.{u} C] [MonoidalCategory.{u} C] [MarkovCategory C]

open MonoidalCategory

/-- The copy operation is commutative -/
example (X : C) : copyMor X ≫ (β_ X X).hom = copyMor X := copy_comm X

/-- Left counit law -/
example (X : C) : copyMor X ≫ (delMor X ▷ X) = (λ_ X).inv := counit_comul X

/-- Right counit law -/
example (X : C) : copyMor X ≫ (X ◁ delMor X) = (ρ_ X).inv := comul_counit X

/-- Coassociativity -/
example (X : C) :
    copyMor X ≫ (copyMor X ▷ X) =
    copyMor X ≫ (X ◁ copyMor X) ≫ (α_ X X X).inv := coassoc X

/-- Delete is natural -/
example {X Y : C} (f : X ⟶ Y) : f ≫ delMor Y = delMor X := del_natural f

end ComonoidLaws

section FinStochExamples

open FinStoch StochasticMatrix

/-- A simple 2x2 stochastic matrix representing a coin flip -/
noncomputable def coinFlip : StochasticMatrix (Fin 2) (Fin 2) where
  toMatrix := ![
    ![1/2, 1/2],  -- From state 0: 50% chance to stay, 50% to flip
    ![1/3, 2/3]   -- From state 1: 33% to flip, 67% to stay
  ]
  row_sum := by
    intro i
    fin_cases i <;> simp only [Finset.sum] <;> norm_num

/-- The identity matrix is stochastic -/
def identityStochastic : StochasticMatrix (Fin 3) (Fin 3) :=
  StochasticMatrix.id (Fin 3)

/-- Composition of stochastic matrices preserves the stochastic property -/
noncomputable example : StochasticMatrix (Fin 2) (Fin 2) :=
  StochasticMatrix.comp coinFlip coinFlip

/-- FinStoch has Category structure -/
example : Category FinStoch := inferInstance

/-- FinStoch has MonoidalCategory structure -/
example : MonoidalCategory FinStoch := inferInstance

end FinStochExamples

section DeterministicMorphisms

variable {C : Type u} [Category.{u} C] [MonoidalCategory C] [MarkovCategory C]

/-- Identity morphisms are deterministic -/
example (X : C) : Deterministic (𝟙 X) := inferInstance

/-- Composition of deterministic morphisms is deterministic -/
example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Deterministic f] [Deterministic g] : Deterministic (f ≫ g) := inferInstance

end DeterministicMorphisms

section CartesianDeterministic

variable {C : Type u} [Category.{u} C] [CartesianMonoidalCategory C]

/-- In a cartesian category, all morphisms are deterministic -/
example {X Y : C} (f : X ⟶ Y) : Deterministic f :=
  CartesianMarkov.deterministic_of_cartesian f

end CartesianDeterministic

section SimpLemmas

variable {C : Type u} [Category.{u} C] [MonoidalCategory C] [MarkovCategory C]

open MonoidalCategory

/-- Test that simp lemmas work for counit laws -/
example (X : C) : copyMor X ≫ (delMor X ▷ X) = (λ_ X).inv := by simp

/-- Test that simp lemmas work for naturality of delete -/
example {X Y : C} (f : X ⟶ Y) : f ≫ delMor Y = delMor X := by simp

/-- Test that simp lemmas work for copy commutativity -/
example (X : C) : copyMor X ≫ (β_ X X).hom = copyMor X := by simp

end SimpLemmas
