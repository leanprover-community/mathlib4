/-
Copyright (c) 2020 Kevin Lacker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Heather Macbeth
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic.Polyrith

/-!
# IMO 1962 Q4

Solve the equation `cos x ^ 2 + cos (2 * x) ^ 2 + cos (3 * x) ^ 2 = 1`.

Since Lean does not have a concept of "simplest form", we just express what is
in fact the simplest form of the set of solutions, and then prove it equals the set of solutions.
-/

open Real

open scoped Real

namespace Imo1962Q4

noncomputable section

def ProblemEquation (x : ℝ) : Prop :=
  cos x ^ 2 + cos (2 * x) ^ 2 + cos (3 * x) ^ 2 = 1

def solutionSet : Set ℝ :=
  {x : ℝ | ∃ k : ℤ, x = (2 * ↑k + 1) * π / 4 ∨ x = (2 * ↑k + 1) * π / 6}

/-
The key to solving this problem simply is that we can rewrite the equation as
a product of terms, shown in `alt_formula`, being equal to zero.
-/
def altFormula (x : ℝ) : ℝ :=
  cos x * (cos x ^ 2 - 1 / 2) * cos (3 * x)

theorem cos_sum_equiv {x : ℝ} :
    (cos x ^ 2 + cos (2 * x) ^ 2 + cos (3 * x) ^ 2 - 1) / 4 = altFormula x := by
  simp only [Real.cos_two_mul, cos_three_mul, altFormula]
  ring

theorem alt_equiv {x : ℝ} : ProblemEquation x ↔ altFormula x = 0 := by
  rw [ProblemEquation, ← cos_sum_equiv, div_eq_zero_iff, sub_eq_zero]
  norm_num

theorem finding_zeros {x : ℝ} : altFormula x = 0 ↔ cos x ^ 2 = 1 / 2 ∨ cos (3 * x) = 0 := by
  simp only [altFormula, mul_assoc, mul_eq_zero, sub_eq_zero]
  constructor
  · rintro (h1 | h2)
    · right
      rw [cos_three_mul, h1]
      ring
    · exact h2
  · exact Or.inr

/-
Now we can solve for `x` using basic-ish trigonometry.
-/
theorem solve_cos2_half {x : ℝ} : cos x ^ 2 = 1 / 2 ↔ ∃ k : ℤ, x = (2 * ↑k + 1) * π / 4 := by
  rw [cos_sq]
  simp only [add_eq_left, div_eq_zero_iff]
  norm_num
  rw [cos_eq_zero_iff]
  constructor <;>
    · rintro ⟨k, h⟩
      use k
      linarith

theorem solve_cos3x_0 {x : ℝ} : cos (3 * x) = 0 ↔ ∃ k : ℤ, x = (2 * ↑k + 1) * π / 6 := by
  rw [cos_eq_zero_iff]
  refine exists_congr fun k => ?_
  constructor <;> intro <;> linarith

end

end Imo1962Q4

open Imo1962Q4

/-
The final theorem is now just gluing together our lemmas.
-/
theorem imo1962_q4 {x : ℝ} : ProblemEquation x ↔ x ∈ solutionSet := by
  rw [alt_equiv, finding_zeros, solve_cos3x_0, solve_cos2_half]
  exact exists_or.symm

namespace Imo1962Q4

/-
We now present a second solution.  The key to this solution is that, when the identity is
converted to an identity which is polynomial in `a` := `cos x`, it can be rewritten as a product of
terms, `a ^ 2 * (2 * a ^ 2 - 1) * (4 * a ^ 2 - 3)`, being equal to zero.
-/
theorem formula {R : Type*} [CommRing R] [IsDomain R] [CharZero R] (a : R) :
    a ^ 2 + ((2 : R) * a ^ 2 - (1 : R)) ^ 2 + ((4 : R) * a ^ 3 - 3 * a) ^ 2 = 1 ↔
      ((2 : R) * a ^ 2 - (1 : R)) * ((4 : R) * a ^ 3 - 3 * a) = 0 := by
  constructor <;> intro h
  · apply pow_eq_zero (n := 2)
    apply mul_left_injective₀ (b := 2) (by simp)
    linear_combination (8 * a ^ 4 - 10 * a ^ 2 + 3) * h
  · linear_combination 2 * a * h

/-
Again, we now can solve for `x` using basic-ish trigonometry.
-/
theorem solve_cos2x_0 {x : ℝ} : cos (2 * x) = 0 ↔ ∃ k : ℤ, x = (2 * ↑k + 1) * π / 4 := by
  rw [cos_eq_zero_iff]
  refine exists_congr fun k => ?_
  constructor <;> intro <;> linarith

end Imo1962Q4

open Imo1962Q4

/-
Again, the final theorem is now just gluing together our lemmas.
-/
theorem imo1962_q4' {x : ℝ} : ProblemEquation x ↔ x ∈ solutionSet :=
  calc
    ProblemEquation x ↔ cos x ^ 2 + cos (2 * x) ^ 2 + cos (3 * x) ^ 2 = 1 := by rfl
    _ ↔ cos (2 * x) = 0 ∨ cos (3 * x) = 0 := by simp [cos_two_mul, cos_three_mul, formula]
    _ ↔ x ∈ solutionSet := by rw [solve_cos2x_0, solve_cos3x_0, ← exists_or]; rfl
