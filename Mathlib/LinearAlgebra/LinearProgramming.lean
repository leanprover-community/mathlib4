/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-! # Linear programming

Minimizing a linear function on a region defined by linear inequalities.

## Main definitions

 * `LinearProgram` defines a linear program in a form that generalizes "A x ≥ b".
 * `LinearProgram.feasibles` is the set of all admissible solutions to given linear program.
 * `LinearProgram.MinAt` defines an optimum solution of given linear program.

-/

/-- Linear program in the form of inequalities with general variables. -/
structure LinearProgram (K : Type*) {V : Type*} (P : Type*)
    [LinearOrderedField K] [AddCommGroup V] [Module K V] [AddTorsor V P] where
  /-- Inequality constraints (given in the form "aᵀx - b ≥ 0") -/
  constraints : List (P →ᵃ[K] K)
  /-- The objective function (affine map) -/
  objective : P →ᵃ[K] K

variable {K V P : Type*} [LinearOrderedField K] [AddCommGroup V] [Module K V] [AddTorsor V P]

/-- Constructs a linear program given a list of equalities, a list of inequalities,
    and an objective function. -/
def LinearProgram.mkOfEqs
    (equalities inequalities : List (P →ᵃ[K] K)) (objective : P →ᵃ[K] K) :
    LinearProgram K P :=
  { constraints := inequalities ++ equalities ++ equalities.map Neg.neg, objective }

/-- The set of all admissible solutions to given linear program. -/
def LinearProgram.feasibles (lp : LinearProgram K P) : Set P :=
  { x : P | ∀ a ∈ lp.constraints, 0 ≤ a x }

/-- Given linear program is minimized at given point. -/
def LinearProgram.MinAt (lp : LinearProgram K P) (x : P) : Prop :=
  IsLeast (lp.objective '' lp.feasibles) (lp.objective x)

lemma LinearProgram.feasibles_mkOfEqs
    (equalities inequalities : List (P →ᵃ[K] K)) (objective : P →ᵃ[K] K) :
    (mkOfEqs equalities inequalities objective).feasibles =
    { x : P | (∀ a ∈ equalities, a x = 0) ∧ (∀ a ∈ inequalities, 0 ≤ a x) } := by
  ext x
  constructor
  · intro hyp
    rw [Set.mem_setOf_eq]
    simp only [LinearProgram.feasibles, LinearProgram.mkOfEqs,
      List.append_assoc, List.mem_append, List.mem_map, Set.mem_setOf_eq,
      Function.Involutive.exists_mem_and_apply_eq_iff, neg_involutive] at hyp
    constructor
    · intro constr_eq mem_equalities
      have hyp_pos := hyp constr_eq (by simp [mem_equalities])
      have hyp_neg := hyp (-constr_eq) (by simp [mem_equalities])
      simp only [AffineMap.coe_neg, Pi.neg_apply, Left.nonneg_neg_iff] at hyp_neg
      exact le_antisymm hyp_neg hyp_pos
    · intro constr_le mem_inequalities
      exact hyp constr_le (by simp [mem_inequalities])
  · intro hyp
    simp only [Set.mem_setOf_eq, LinearProgram.feasibles] at hyp
    simp only [LinearProgram.feasibles, LinearProgram.mkOfEqs]
    intro constraint constraint_mem
    rw [List.mem_append, List.mem_append] at constraint_mem
    cases constraint_mem with
    | inl normal =>
      cases normal with
      | inl mem_les => exact hyp.2 constraint mem_les
      | inr mem_eqs => exact Eq.ge (hyp.1 constraint mem_eqs)
    | inr negated =>
      rw [List.mem_map] at negated
      rcases negated with ⟨orig, orig_mem, neg_orig⟩
      rw [← neg_orig]
      simp [hyp.1 orig orig_mem]

/-- Adding more constraints cannot enlarge the set of feasible solutions. -/
lemma feasiblesLinearProgram_superset_of_contraints_subset {lp₁ lp₂ : LinearProgram K P}
    (hconstrs : lp₁.constraints ⊆ lp₂.constraints) :
    lp₂.feasibles ⊆ lp₁.feasibles := by
  intro x hx
  simp only [LinearProgram.feasibles, Set.mem_setOf_eq] at hx ⊢
  intro a ha
  apply hx
  exact hconstrs ha

/-- Adding more constraints cannot decrease the minimum. -/
lemma minLinearProgram_le_of_contraints_subset {lp₁ lp₂ : LinearProgram K P} {x₁ x₂ : P}
    (hconstrs : lp₁.constraints ⊆ lp₂.constraints)
    (hobj : lp₁.objective = lp₂.objective) (opt₁ : lp₁.MinAt x₁) (opt₂ : lp₂.MinAt x₂) :
    lp₁.objective x₁ ≤ lp₂.objective x₂ := by
  unfold LinearProgram.MinAt at opt₁ opt₂
  apply IsLeast.mono opt₂ opt₁
  rw [hobj]
  apply Set.image_subset
  exact feasiblesLinearProgram_superset_of_contraints_subset hconstrs
