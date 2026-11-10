/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
module
import Mathlib.CategoryTheory.MarkovCategory.Basic
import Mathlib.CategoryTheory.CopyDiscardCategory.Cartesian
import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# Tests for Markov Categories

Tests for the Markov category and copy-discard category implementation.

## Tests included

* Instance inference for cartesian and copy-discard structures
* Comonoid laws: comultiplication and counit axioms
* Markov category laws: naturality of discard and terminal unit
* Simp automation for comonoid and discard naturality
-/

universe u

open CategoryTheory MonoidalCategory CopyDiscardCategory ComonObj IsCommComonObj

section BasicTests

/-- CartesianMonoidalCategory instance exists for Type* -/
example : CartesianMonoidalCategory (Type u) := inferInstance

/-- CopyDiscardCategory instance for Type* via cartesian structure -/
example : CopyDiscardCategory (Type u) := CartesianCopyDiscard.ofCartesianMonoidalCategory

end BasicTests

section ComonoidLaws

variable {C : Type u} [Category.{u} C] [MonoidalCategory.{u} C] [CopyDiscardCategory C]

/-- Comultiplication is commutative -/
example (X : C) : Δ[X] ≫ (β_ X X).hom = Δ[X] := comul_comm X

/-- Left counit law: copy then discard left component recovers object -/
example (X : C) : Δ[X] ≫ (ε[X] ▷ X) = (λ_ X).inv := ComonObj.counit_comul X

/-- Right counit law: copy then discard right component recovers object -/
example (X : C) : Δ[X] ≫ (X ◁ ε[X]) = (ρ_ X).inv := ComonObj.comul_counit X

/-- Comultiplication is coassociative -/
example (X : C) :
    Δ[X] ≫ (X ◁ Δ[X]) = Δ[X] ≫ (Δ[X] ▷ X) ≫ (α_ X X X).hom :=
  ComonObj.comul_assoc X

end ComonoidLaws

section MarkovLaws

variable {C : Type u} [Category.{u} C] [MonoidalCategory.{u} C] [MarkovCategory C]

/-- Discard is natural -/
example {X Y : C} (f : X ⟶ Y) : f ≫ ε[Y] = ε[X] := MarkovCategory.discard_natural f

/-- Any morphism to the unit equals discard -/
example (X : C) (f : X ⟶ 𝟙_ C) : f = ε[X] := MarkovCategory.eq_discard X f

/-- The monoidal unit is terminal -/
example : Limits.IsTerminal (𝟙_ C : C) := MarkovCategory.isTerminalUnit

/-- Any two morphisms to the unit are equal (subsingleton instance) -/
example (X : C) (f g : X ⟶ 𝟙_ C) : f = g := Subsingleton.elim f g

end MarkovLaws

section SimpLemmas

variable {C : Type u} [Category.{u} C] [MonoidalCategory C] [CopyDiscardCategory C]

/-- Simp automation for counit laws -/
example (X : C) : Δ[X] ≫ (ε[X] ▷ X) = (λ_ X).inv := by simp

/-- Simp automation for comultiplication commutativity -/
example (X : C) : Δ[X] ≫ (β_ X X).hom = Δ[X] := by simp

end SimpLemmas

section MarkovSimpLemmas

variable {C : Type u} [Category.{u} C] [MonoidalCategory.{u} C] [MarkovCategory C]

/-- Simp automation for naturality of discard -/
example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ g ≫ ε[Z] = f ≫ ε[Y] := by simp

end MarkovSimpLemmas
