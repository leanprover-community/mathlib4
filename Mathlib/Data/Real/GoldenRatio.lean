/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Alexey Soloyev, Junyan Xu, Kamila Szewczyk
-/
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.LinearRecurrence
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.Prime

#align_import data.real.golden_ratio from "leanprover-community/mathlib"@"2196ab363eb097c008d4497125e0dde23fb36db2"

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
abbrev goldenRatio : ℝ := (1 + √5) / 2
#align golden_ratio goldenRatio

/-- The conjugate of the golden ratio `ψ := (1 - √5)/2`. -/
abbrev goldenConj : ℝ := (1 - √5) / 2
#align golden_conj goldenConj

@[inherit_doc goldenRatio] scoped[goldenRatio] notation "φ" => goldenRatio
@[inherit_doc goldenConj] scoped[goldenRatio] notation "ψ" => goldenConj
open Real goldenRatio

/-- The inverse of the golden ratio is the opposite of its conjugate. -/
theorem inv_gold : φ⁻¹ = -ψ := by
  have : 1 + √5 ≠ 0 := ne_of_gt (add_pos (by norm_num) <| Real.sqrt_pos.mpr (by norm_num))
  field_simp [sub_mul, mul_add]
  norm_num
#align inv_gold inv_gold

/-- The opposite of the golden ratio is the inverse of its conjugate. -/
theorem inv_goldConj : ψ⁻¹ = -φ := by
  rw [inv_eq_iff_eq_inv, ← neg_inv, ← neg_eq_iff_eq_neg]
  exact inv_gold.symm
#align inv_gold_conj inv_goldConj

@[simp]
theorem gold_mul_goldConj : φ * ψ = -1 := by
  field_simp
  rw [← sq_sub_sq]
  norm_num
#align gold_mul_gold_conj gold_mul_goldConj

@[simp]
theorem goldConj_mul_gold : ψ * φ = -1 := by
  rw [mul_comm]
  exact gold_mul_goldConj
#align gold_conj_mul_gold goldConj_mul_gold

@[simp]
theorem gold_add_goldConj : φ + ψ = 1 := by
  rw [goldenRatio, goldenConj]
  ring
#align gold_add_gold_conj gold_add_goldConj

theorem one_sub_goldConj : 1 - φ = ψ := by
  linarith [gold_add_goldConj]
#align one_sub_gold_conj one_sub_goldConj

theorem one_sub_gold : 1 - ψ = φ := by
  linarith [gold_add_goldConj]
#align one_sub_gold one_sub_gold

@[simp]
theorem gold_sub_goldConj : φ - ψ = √5 := by ring
#align gold_sub_gold_conj gold_sub_goldConj

theorem gold_pow_sub_gold_pow (n : ℕ) : φ ^ (n + 2) - φ ^ (n + 1) = φ ^ n := by
  rw [goldenRatio]; ring_nf; norm_num; ring

@[simp 1200]
theorem gold_sq : φ ^ 2 = φ + 1 := by
  rw [goldenRatio, ← sub_eq_zero]
  ring_nf
  rw [Real.sq_sqrt] <;> norm_num
#align gold_sq gold_sq

@[simp 1200]
theorem goldConj_sq : ψ ^ 2 = ψ + 1 := by
  rw [goldenConj, ← sub_eq_zero]
  ring_nf
  rw [Real.sq_sqrt] <;> norm_num
#align gold_conj_sq goldConj_sq

theorem gold_pos : 0 < φ :=
  mul_pos (by apply add_pos <;> norm_num) <| inv_pos.2 zero_lt_two
#align gold_pos gold_pos

theorem gold_ne_zero : φ ≠ 0 :=
  ne_of_gt gold_pos
#align gold_ne_zero gold_ne_zero

theorem one_lt_gold : 1 < φ := by
  refine lt_of_mul_lt_mul_left ?_ (le_of_lt gold_pos)
  simp [← sq, gold_pos, zero_lt_one, - div_pow] -- Porting note: Added `- div_pow`
#align one_lt_gold one_lt_gold

theorem gold_lt_two : φ < 2 := by calc
  (1 + sqrt 5) / 2 < (1 + 3) / 2 := by gcongr; rw [sqrt_lt'] <;> norm_num
  _ = 2 := by norm_num

theorem goldConj_neg : ψ < 0 := by
  linarith [one_sub_goldConj, one_lt_gold]
#align gold_conj_neg goldConj_neg

theorem goldConj_ne_zero : ψ ≠ 0 :=
  ne_of_lt goldConj_neg
#align gold_conj_ne_zero goldConj_ne_zero

theorem neg_one_lt_goldConj : -1 < ψ := by
  rw [neg_lt, ← inv_gold]
  exact inv_lt_one one_lt_gold
#align neg_one_lt_gold_conj neg_one_lt_goldConj

/-!
## Irrationality
-/


/-- The golden ratio is irrational. -/
theorem gold_irrational : Irrational φ := by
  have := Nat.Prime.irrational_sqrt (show Nat.Prime 5 by norm_num)
  have := this.rat_add 1
  have := this.rat_mul (show (0.5 : ℚ) ≠ 0 by norm_num)
  convert this
  norm_num
  field_simp
#align gold_irrational gold_irrational

/-- The conjugate of the golden ratio is irrational. -/
theorem goldConj_irrational : Irrational ψ := by
  have := Nat.Prime.irrational_sqrt (show Nat.Prime 5 by norm_num)
  have := this.rat_sub 1
  have := this.rat_mul (show (0.5 : ℚ) ≠ 0 by norm_num)
  convert this
  norm_num
  field_simp
#align gold_conj_irrational goldConj_irrational

/-!
## Links with Fibonacci sequence
-/

section Fibrec

variable {α : Type*} [CommSemiring α]

/-- The recurrence relation satisfied by the Fibonacci sequence. -/
def fibRec : LinearRecurrence α where
  order := 2
  coeffs := ![1, 1]
#align fib_rec fibRec

section Poly

open Polynomial

/-- The characteristic polynomial of `fibRec` is `X² - (X + 1)`. -/
theorem fibRec_charPoly_eq {β : Type*} [CommRing β] :
    fibRec.charPoly = X ^ 2 - (X + (1 : β[X])) := by
  rw [fibRec, LinearRecurrence.charPoly]
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ', ← smul_X_eq_monomial]
#align fib_rec_char_poly_eq fibRec_charPoly_eq

end Poly

/-- As expected, the Fibonacci sequence is a solution of `fibRec`. -/
theorem fib_isSol_fibRec : fibRec.IsSolution (fun x => x.fib : ℕ → α) := by
  rw [fibRec]
  intro n
  simp only
  rw [Nat.fib_add_two, add_comm]
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ']
#align fib_is_sol_fib_rec fib_isSol_fibRec

/-- The geometric sequence `fun n ↦ φ^n` is a solution of `fibRec`. -/
theorem geom_gold_isSol_fibRec : fibRec.IsSolution (φ ^ ·) := by
  rw [fibRec.geom_sol_iff_root_charPoly, fibRec_charPoly_eq]
  simp [sub_eq_zero, - div_pow] -- Porting note: Added `- div_pow`
#align geom_gold_is_sol_fib_rec geom_gold_isSol_fibRec

/-- The geometric sequence `fun n ↦ ψ^n` is a solution of `fibRec`. -/
theorem geom_goldConj_isSol_fibRec : fibRec.IsSolution (ψ ^ ·) := by
  rw [fibRec.geom_sol_iff_root_charPoly, fibRec_charPoly_eq]
  simp [sub_eq_zero, - div_pow] -- Porting note: Added `- div_pow`
#align geom_gold_conj_is_sol_fib_rec geom_goldConj_isSol_fibRec

end Fibrec

/-- Binet's formula as a function equality. -/
theorem Real.coe_fib_eq' :
    (fun n => Nat.fib n : ℕ → ℝ) = fun n => (φ ^ n - ψ ^ n) / √5 := by
  rw [fibRec.sol_eq_of_eq_init]
  · intro i hi
    norm_cast at hi
    fin_cases hi
    · simp
    · simp only [goldenRatio, goldenConj]
      ring_nf
      rw [mul_inv_cancel]; norm_num
  · exact fib_isSol_fibRec
  · -- Porting note: Rewrote this proof
    suffices LinearRecurrence.IsSolution fibRec
        ((fun n ↦ (√5)⁻¹ * φ ^ n) - (fun n ↦ (√5)⁻¹ * ψ ^ n)) by
      convert this
      rw [Pi.sub_apply]
      ring
    apply (@fibRec ℝ _).solSpace.sub_mem
    · exact Submodule.smul_mem fibRec.solSpace (√5)⁻¹ geom_gold_isSol_fibRec
    · exact Submodule.smul_mem fibRec.solSpace (√5)⁻¹ geom_goldConj_isSol_fibRec
#align real.coe_fib_eq' Real.coe_fib_eq'

/-- Binet's formula as a dependent equality. -/
theorem Real.coe_fib_eq : ∀ n, (Nat.fib n : ℝ) = (φ ^ n - ψ ^ n) / √5 := by
  rw [← Function.funext_iff, Real.coe_fib_eq']
#align real.coe_fib_eq Real.coe_fib_eq

/-- Relationship between the Fibonacci Sequence, Golden Ratio and its conjugate's exponents --/
theorem fib_golden_conj_exp (n : ℕ) : Nat.fib (n + 1) - φ * Nat.fib n = ψ ^ n := by
  repeat rw [coe_fib_eq]
  rw [mul_div, div_sub_div_same, mul_sub, ← pow_succ']
  ring_nf
  have nz : sqrt 5 ≠ 0 := by norm_num
  rw [← (mul_inv_cancel nz).symm, one_mul]

/-- Relationship between the Fibonacci Sequence, Golden Ratio and its exponents --/
theorem fib_golden_exp' (n : ℕ) : φ * Nat.fib (n + 1) + Nat.fib n = φ ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    calc
      _ = φ * (Nat.fib n) + φ ^ 2 * (Nat.fib (n + 1)) := by
        simp only [Nat.fib_add_one (Nat.succ_ne_zero n), Nat.succ_sub_succ_eq_sub, tsub_zero,
          Nat.cast_add, gold_sq]; ring
      _ = φ * ((Nat.fib n) + φ * (Nat.fib (n + 1))) := by ring
      _ = φ ^ (n + 2) := by rw [add_comm, ih]; ring
