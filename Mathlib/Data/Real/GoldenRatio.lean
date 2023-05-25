/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Alexey Soloyev, Junyan Xu

! This file was ported from Lean 3 source module data.real.golden_ratio
! leanprover-community/mathlib commit 2196ab363eb097c008d4497125e0dde23fb36db2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Real.Irrational
import Mathbin.Data.Nat.Fib
import Mathbin.Data.Nat.PrimeNormNum
import Mathbin.Data.Fin.VecNotation
import Mathbin.Tactic.RingExp
import Mathbin.Algebra.LinearRecurrence

/-!
# The golden ratio and its conjugate

This file defines the golden ratio `φ := (1 + √5)/2` and its conjugate
`ψ := (1 - √5)/2`, which are the two real roots of `X² - X - 1`.

Along with various computational facts about them, we prove their
irrationality, and we link them to the Fibonacci sequence by proving
Binet's formula.
-/


noncomputable section

open Polynomial

/-- The golden ratio `φ := (1 + √5)/2`. -/
@[reducible]
def goldenRatio :=
  (1 + Real.sqrt 5) / 2
#align golden_ratio goldenRatio

/-- The conjugate of the golden ratio `ψ := (1 - √5)/2`. -/
@[reducible]
def goldenConj :=
  (1 - Real.sqrt 5) / 2
#align golden_conj goldenConj

-- mathport name: golden_ratio
scoped[Real] notation "φ" => goldenRatio

-- mathport name: golden_conj
scoped[Real] notation "ψ" => goldenConj

/-- The inverse of the golden ratio is the opposite of its conjugate. -/
theorem inv_gold : φ⁻¹ = -ψ :=
  by
  have : 1 + Real.sqrt 5 ≠ 0 := ne_of_gt (add_pos (by norm_num) <| real.sqrt_pos.mpr (by norm_num))
  field_simp [sub_mul, mul_add]
  norm_num
#align inv_gold inv_gold

/-- The opposite of the golden ratio is the inverse of its conjugate. -/
theorem inv_gold_conj : ψ⁻¹ = -φ :=
  by
  rw [inv_eq_iff_eq_inv, ← neg_inv, ← neg_eq_iff_eq_neg]
  exact inv_gold.symm
#align inv_gold_conj inv_gold_conj

@[simp]
theorem gold_mul_gold_conj : φ * ψ = -1 := by
  field_simp
  rw [← sq_sub_sq]
  norm_num
#align gold_mul_gold_conj gold_mul_gold_conj

@[simp]
theorem gold_conj_mul_gold : ψ * φ = -1 := by
  rw [mul_comm]
  exact gold_mul_gold_conj
#align gold_conj_mul_gold gold_conj_mul_gold

@[simp]
theorem gold_add_gold_conj : φ + ψ = 1 :=
  by
  rw [goldenRatio, goldenConj]
  ring
#align gold_add_gold_conj gold_add_gold_conj

theorem one_sub_gold_conj : 1 - φ = ψ := by linarith [gold_add_gold_conj]
#align one_sub_gold_conj one_sub_gold_conj

theorem one_sub_gold : 1 - ψ = φ := by linarith [gold_add_gold_conj]
#align one_sub_gold one_sub_gold

@[simp]
theorem gold_sub_gold_conj : φ - ψ = Real.sqrt 5 :=
  by
  rw [goldenRatio, goldenConj]
  ring
#align gold_sub_gold_conj gold_sub_gold_conj

@[simp]
theorem gold_sq : φ ^ 2 = φ + 1 :=
  by
  rw [goldenRatio, ← sub_eq_zero]
  ring
  rw [Real.sq_sqrt] <;> norm_num
#align gold_sq gold_sq

@[simp]
theorem gold_conj_sq : ψ ^ 2 = ψ + 1 :=
  by
  rw [goldenConj, ← sub_eq_zero]
  ring
  rw [Real.sq_sqrt] <;> norm_num
#align gold_conj_sq gold_conj_sq

theorem gold_pos : 0 < φ :=
  mul_pos (by apply add_pos <;> norm_num) <| inv_pos.2 zero_lt_two
#align gold_pos gold_pos

theorem gold_ne_zero : φ ≠ 0 :=
  ne_of_gt gold_pos
#align gold_ne_zero gold_ne_zero

theorem one_lt_gold : 1 < φ :=
  by
  refine' lt_of_mul_lt_mul_left _ (le_of_lt gold_pos)
  simp [← sq, gold_pos, zero_lt_one]
#align one_lt_gold one_lt_gold

theorem gold_conj_neg : ψ < 0 := by linarith [one_sub_gold_conj, one_lt_gold]
#align gold_conj_neg gold_conj_neg

theorem gold_conj_ne_zero : ψ ≠ 0 :=
  ne_of_lt gold_conj_neg
#align gold_conj_ne_zero gold_conj_ne_zero

theorem neg_one_lt_gold_conj : -1 < ψ :=
  by
  rw [neg_lt, ← inv_gold]
  exact inv_lt_one one_lt_gold
#align neg_one_lt_gold_conj neg_one_lt_gold_conj

/-!
## Irrationality
-/


/-- The golden ratio is irrational. -/
theorem gold_irrational : Irrational φ :=
  by
  have := Nat.Prime.irrational_sqrt (show Nat.Prime 5 by norm_num)
  have := this.rat_add 1
  have := this.rat_mul (show (0.5 : ℚ) ≠ 0 by norm_num)
  convert this
  field_simp
#align gold_irrational gold_irrational

/-- The conjugate of the golden ratio is irrational. -/
theorem gold_conj_irrational : Irrational ψ :=
  by
  have := Nat.Prime.irrational_sqrt (show Nat.Prime 5 by norm_num)
  have := this.rat_sub 1
  have := this.rat_mul (show (0.5 : ℚ) ≠ 0 by norm_num)
  convert this
  field_simp
#align gold_conj_irrational gold_conj_irrational

/-!
## Links with Fibonacci sequence
-/


section Fibrec

variable {α : Type _} [CommSemiring α]

/-- The recurrence relation satisfied by the Fibonacci sequence. -/
def fibRec : LinearRecurrence α where
  order := 2
  coeffs := ![1, 1]
#align fib_rec fibRec

section Poly

open Polynomial

/-- The characteristic polynomial of `fib_rec` is `X² - (X + 1)`. -/
theorem fibRec_charPoly_eq {β : Type _} [CommRing β] : fibRec.charPoly = X ^ 2 - (X + (1 : β[X])) :=
  by
  rw [fibRec, LinearRecurrence.charPoly]
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ', ← smul_X_eq_monomial]
#align fib_rec_char_poly_eq fibRec_charPoly_eq

end Poly

/-- As expected, the Fibonacci sequence is a solution of `fib_rec`. -/
theorem fib_is_sol_fibRec : fibRec.IsSolution (fun x => x.fib : ℕ → α) :=
  by
  rw [fibRec]
  intro n
  simp only
  rw [Nat.fib_add_two, add_comm]
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ']
#align fib_is_sol_fib_rec fib_is_sol_fibRec

/-- The geometric sequence `λ n, φ^n` is a solution of `fib_rec`. -/
theorem geom_gold_is_sol_fibRec : fibRec.IsSolution (pow φ) :=
  by
  rw [fib_rec.geom_sol_iff_root_char_poly, fibRec_charPoly_eq]
  simp [sub_eq_zero]
#align geom_gold_is_sol_fib_rec geom_gold_is_sol_fibRec

/-- The geometric sequence `λ n, ψ^n` is a solution of `fib_rec`. -/
theorem geom_gold_conj_is_sol_fibRec : fibRec.IsSolution (pow ψ) :=
  by
  rw [fib_rec.geom_sol_iff_root_char_poly, fibRec_charPoly_eq]
  simp [sub_eq_zero]
#align geom_gold_conj_is_sol_fib_rec geom_gold_conj_is_sol_fibRec

end Fibrec

/-- Binet's formula as a function equality. -/
theorem Real.coe_fib_eq' : (fun n => Nat.fib n : ℕ → ℝ) = fun n => (φ ^ n - ψ ^ n) / Real.sqrt 5 :=
  by
  rw [fib_rec.sol_eq_of_eq_init]
  · intro i hi
    fin_cases hi
    · simp
    · simp only [goldenRatio, goldenConj]
      ring
      rw [mul_inv_cancel] <;> norm_num
  · exact fib_is_sol_fibRec
  · ring_nf
    exact
      (@fibRec ℝ _).solSpace.sub_mem
        (Submodule.smul_mem fib_rec.sol_space (Real.sqrt 5)⁻¹ geom_gold_is_sol_fibRec)
        (Submodule.smul_mem fib_rec.sol_space (Real.sqrt 5)⁻¹ geom_gold_conj_is_sol_fibRec)
#align real.coe_fib_eq' Real.coe_fib_eq'

/-- Binet's formula as a dependent equality. -/
theorem Real.coe_fib_eq : ∀ n, (Nat.fib n : ℝ) = (φ ^ n - ψ ^ n) / Real.sqrt 5 := by
  rw [← Function.funext_iff, Real.coe_fib_eq']
#align real.coe_fib_eq Real.coe_fib_eq

