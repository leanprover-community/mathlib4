/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak, Eric Wieser
-/
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-!

# Linear programming

Minimizing a linear function on a region defined by linear inequalities (technically speaking,
they are affine inequalities and an affine function to be minized).

## Main definitions

 * `LinearProgram` defines a linear program in a form that generalizes "A x ≥ b".
 * `LinearProgram.feasibles` is the set of all admissible solutions to given linear program.
 * `LinearProgram.MinAt` defines an optimum solution of given linear program.

-/

/-- Linear program in the form of inequalities with general variables. -/
structure LinearProgram (R : Type*) {V : Type*} (P : Type*)
    [LinearOrderedRing R] [AddCommGroup V] [Module R V] [AddTorsor V P] where
  /-- Inequality constraints (values must be nonnegative) -/
  constraints : List (P →ᵃ[R] R)
  /-- The objective function (an affine map) -/
  objective : P →ᵃ[R] R

variable {R V P : Type*} [LinearOrderedRing R] [AddCommGroup V] [Module R V] [AddTorsor V P]

/-- Constructs a linear program given a list of equalities, a list of inequalities,
    and an objective function. -/
def LinearProgram.mkOfEqs
    (equalities inequalities : List (P →ᵃ[R] R)) (objective : P →ᵃ[R] R) :
    LinearProgram R P :=
  { constraints := inequalities ++ equalities ++ equalities.map Neg.neg, objective }

/-- The set of all admissible solutions to given linear program. -/
def LinearProgram.feasibles (lp : LinearProgram R P) : Set P :=
  {x | ∀ ⦃a⦄, a ∈ lp.constraints → 0 ≤ a x}

@[simp] lemma LinearProgram.mem_feasibles {lp : LinearProgram R P} {x : P} :
    x ∈ lp.feasibles ↔ ∀ ⦃a⦄, a ∈ lp.constraints → 0 ≤ a x :=
  Iff.rfl

/-- Given linear program is minimized at given point. -/
def LinearProgram.MinAt (lp : LinearProgram R P) (x : P) : Prop :=
  IsLeast (lp.objective '' lp.feasibles) (lp.objective x)

/-- Feasible solutions are exactly those that satisfy all equalities and all inequalities. -/
lemma LinearProgram.feasibles_mkOfEqs
    (equalities inequalities : List (P →ᵃ[R] R)) (objective : P →ᵃ[R] R) :
    (mkOfEqs equalities inequalities objective).feasibles =
      {x : P | (∀ a ∈ inequalities, 0 ≤ a x) ∧ (∀ a ∈ equalities, a x = 0)} := by
  ext x
  simp only [mem_feasibles, LinearProgram.mkOfEqs, Set.mem_setOf]
  have hiff : (∀ a ∈ equalities, a x = 0) ↔ (∀ a, a ∈ equalities ∨ -a ∈ equalities → 0 ≤ a x)
  · simp_rw [le_antisymm_iff, ←neg_nonneg, and_comm, or_imp, imp_and, forall_and]
    apply and_congr_right'
    rw [Iff.comm, neg_involutive.surjective.forall]
    simp_rw [neg_neg, AffineMap.coe_neg, Pi.neg_apply]
  simp_rw [List.mem_append, List.mem_map_of_involutive neg_involutive, or_assoc,
    @or_imp (_ ∈ inequalities), forall_and, hiff]

/-- Adding more constraints cannot enlarge the set of feasible solutions. -/
lemma LinearProgram.feasibles_superset_of_constraints_subset {lp₁ lp₂ : LinearProgram R P}
    (constrss : lp₁.constraints ⊆ lp₂.constraints) :
    lp₂.feasibles ⊆ lp₁.feasibles := by
  intro x hx
  rw [mem_feasibles] at hx ⊢
  intro a ha
  apply hx
  exact constrss ha

/-- Adding more constraints cannot decrease the minimum. -/
lemma LinearProgram.min_le_of_constraints_subset {lp₁ lp₂ : LinearProgram R P} {x₁ x₂ : P}
    (constrss : lp₁.constraints ⊆ lp₂.constraints)
    (hobj : lp₁.objective = lp₂.objective) (opt₁ : lp₁.MinAt x₁) (opt₂ : lp₂.MinAt x₂) :
    lp₁.objective x₁ ≤ lp₂.objective x₂ := by
  unfold LinearProgram.MinAt at opt₁ opt₂
  apply IsLeast.mono opt₂ opt₁
  rw [hobj]
  apply Set.image_subset
  exact feasibles_superset_of_constraints_subset constrss
