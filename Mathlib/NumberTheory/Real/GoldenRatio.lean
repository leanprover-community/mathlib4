/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Alexey Soloyev, Junyan Xu, Kamila Szewczyk
-/
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.LinearRecurrence
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.Prime

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

namespace Real

/-- The golden ratio `φ := (1 + √5)/2`. -/
abbrev goldenRatio : ℝ := (1 + √5) / 2

/-- The conjugate of the golden ratio `ψ := (1 - √5)/2`. -/
abbrev goldenConj : ℝ := (1 - √5) / 2

@[inherit_doc] scoped[goldenRatio] notation "φ" => Real.goldenRatio
@[inherit_doc] scoped[goldenRatio] notation "ψ" => Real.goldenConj

open goldenRatio

/-- The inverse of the golden ratio is the opposite of its conjugate. -/
theorem inv_goldenRatio : φ⁻¹ = -ψ := by
  grind

@[deprecated (since := "2025-08-23")] alias _root_.inv_gold := inv_goldenRatio

/-- The opposite of the golden ratio is the inverse of its conjugate. -/
theorem inv_goldenConj : ψ⁻¹ = -φ := by
  rw [inv_eq_iff_eq_inv, ← neg_inv, ← neg_eq_iff_eq_neg]
  exact inv_goldenRatio.symm

@[deprecated (since := "2025-08-23")] alias _root_.inv_goldConj := inv_goldenConj

@[simp]
theorem goldenRatio_mul_goldenConj : φ * ψ = -1 := by
  grind

@[deprecated (since := "2025-08-23")] alias _root_.gold_mul_goldConj := goldenRatio_mul_goldenConj

@[simp]
theorem goldenConj_mul_goldenRatio : ψ * φ = -1 := by
  rw [mul_comm]
  exact goldenRatio_mul_goldenConj

@[deprecated (since := "2025-08-23")] alias _root_.goldConj_mul_gold := goldenConj_mul_goldenRatio

@[simp]
theorem goldenRatio_add_goldenConj : φ + ψ = 1 := by
  rw [goldenRatio, goldenConj]
  ring

@[deprecated (since := "2025-08-23")] alias _root_.gold_add_goldConj := goldenRatio_add_goldenConj

theorem one_sub_goldenConj : 1 - φ = ψ := by
  linarith [goldenRatio_add_goldenConj]

@[deprecated (since := "2025-08-23")] alias _root_.one_sub_goldConj := one_sub_goldenConj

theorem one_sub_goldenRatio : 1 - ψ = φ := by
  linarith [goldenRatio_add_goldenConj]

@[deprecated (since := "2025-08-23")] alias _root_.one_sub_gold := one_sub_goldenRatio

@[simp]
theorem goldenRatio_sub_goldenConj : φ - ψ = √5 := by ring

@[deprecated (since := "2025-08-23")] alias _root_.gold_sub_goldConj := goldenRatio_sub_goldenConj

theorem goldenRatio_pow_sub_goldenRatio_pow (n : ℕ) : φ ^ (n + 2) - φ ^ (n + 1) = φ ^ n := by
  grind

@[deprecated (since := "2025-08-23")]
alias gold_pow_sub_gold_pow := goldenRatio_pow_sub_goldenRatio_pow

@[simp 1200]
theorem goldenRatio_sq : φ ^ 2 = φ + 1 := by
  grind

@[deprecated (since := "2025-08-23")] alias _root_.gold_sq := goldenRatio_sq

@[simp 1200]
theorem goldenConj_sq : ψ ^ 2 = ψ + 1 := by
  grind

@[deprecated (since := "2025-08-23")] alias _root_.goldConj_sq := goldenConj_sq

theorem goldenRatio_pos : 0 < φ :=
  mul_pos (by apply add_pos <;> norm_num) <| inv_pos.2 zero_lt_two

@[deprecated (since := "2025-08-23")] alias _root_.gold_pos := goldenRatio_pos

theorem goldenRatio_ne_zero : φ ≠ 0 :=
  ne_of_gt goldenRatio_pos

@[deprecated (since := "2025-08-23")] alias _root_.gold_ne_zero := goldenRatio_ne_zero

theorem one_lt_goldenRatio : 1 < φ := by
  refine lt_of_mul_lt_mul_left ?_ (le_of_lt goldenRatio_pos)
  simp [← sq, zero_lt_one]

@[deprecated (since := "2025-08-23")] alias _root_.one_lt_gold := one_lt_goldenRatio

theorem goldenRatio_lt_two : φ < 2 := by calc
  (1 + √5) / 2 < (1 + 3) / 2 := by gcongr; rw [sqrt_lt'] <;> norm_num
  _ = 2 := by norm_num

@[deprecated (since := "2025-08-23")] alias _root_.gold_lt_two := goldenRatio_lt_two

theorem goldenConj_neg : ψ < 0 := by
  linarith [one_sub_goldenConj, one_lt_goldenRatio]

@[deprecated (since := "2025-08-23")] alias _root_.goldConj_neg := goldenConj_neg

theorem goldenConj_ne_zero : ψ ≠ 0 :=
  ne_of_lt goldenConj_neg

@[deprecated (since := "2025-08-23")] alias _root_.goldConj_ne_zero := goldenConj_ne_zero

theorem neg_one_lt_goldenConj : -1 < ψ := by
  rw [neg_lt, ← inv_goldenRatio]
  exact inv_lt_one_of_one_lt₀ one_lt_goldenRatio

@[deprecated (since := "2025-08-23")] alias _root_.neg_one_lt_goldConj := neg_one_lt_goldenConj

/-!
## Irrationality
-/


/-- The golden ratio is irrational. -/
theorem goldenRatio_irrational : Irrational φ := by
  have := Nat.Prime.irrational_sqrt (show Nat.Prime 5 by norm_num)
  have := this.ratCast_add 1
  convert this.ratCast_mul (show (0.5 : ℚ) ≠ 0 by norm_num)
  norm_num
  field_simp

@[deprecated (since := "2025-08-23")] alias _root_.gold_irrational := goldenRatio_irrational

/-- The conjugate of the golden ratio is irrational. -/
theorem goldenConj_irrational : Irrational ψ := by
  have := Nat.Prime.irrational_sqrt (show Nat.Prime 5 by norm_num)
  have := this.ratCast_sub 1
  convert this.ratCast_mul (show (0.5 : ℚ) ≠ 0 by norm_num)
  norm_num
  field_simp

@[deprecated (since := "2025-08-23")] alias _root_.goldConj_irrational := goldenConj_irrational

/-!
## Links with Fibonacci sequence
-/

section Fibrec

variable {α : Type*} [CommSemiring α]

/-- The recurrence relation satisfied by the Fibonacci sequence. -/
def fibRec : LinearRecurrence α where
  order := 2
  coeffs := ![1, 1]

section Poly

open Polynomial

/-- The characteristic polynomial of `fibRec` is `X² - (X + 1)`. -/
theorem fibRec_charPoly_eq {β : Type*} [CommRing β] :
    fibRec.charPoly = X ^ 2 - (X + (1 : β[X])) := by
  rw [fibRec, LinearRecurrence.charPoly]
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ', ← smul_X_eq_monomial]

end Poly

/-- As expected, the Fibonacci sequence is a solution of `fibRec`. -/
theorem fib_isSol_fibRec : fibRec.IsSolution (fun x => x.fib : ℕ → α) := by
  rw [fibRec]
  intro n
  simp only
  rw [Nat.fib_add_two, add_comm]
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ']

/-- The geometric sequence `fun n ↦ φ^n` is a solution of `fibRec`. -/
theorem geom_goldenRatio_isSol_fibRec : fibRec.IsSolution (φ ^ ·) := by
  rw [fibRec.geom_sol_iff_root_charPoly, fibRec_charPoly_eq]
  simp

@[deprecated (since := "2025-08-23")]
alias _root_.geom_gold_isSol_fibRec := geom_goldenRatio_isSol_fibRec

/-- The geometric sequence `fun n ↦ ψ^n` is a solution of `fibRec`. -/
theorem geom_goldenConj_isSol_fibRec : fibRec.IsSolution (ψ ^ ·) := by
  rw [fibRec.geom_sol_iff_root_charPoly, fibRec_charPoly_eq]
  simp

@[deprecated (since := "2025-08-23")]
alias geom_goldConj_isSol_fibRec := geom_goldenConj_isSol_fibRec

end Fibrec

/-- Binet's formula as a function equality. -/
theorem coe_fib_eq' :
    (fun n => Nat.fib n : ℕ → ℝ) = fun n => (φ ^ n - ψ ^ n) / √5 := by
  rw [fibRec.sol_eq_of_eq_init]
  · intro i hi
    norm_cast at hi
    fin_cases hi
    · simp
    · simp only [goldenRatio, goldenConj]
      ring_nf
      rw [mul_inv_cancel₀]; norm_num
  · exact fib_isSol_fibRec
  · suffices LinearRecurrence.IsSolution fibRec
        ((fun n ↦ (√5)⁻¹ * φ ^ n) - (fun n ↦ (√5)⁻¹ * ψ ^ n)) by
      convert this
      rw [Pi.sub_apply]
      ring
    apply (@fibRec ℝ _).solSpace.sub_mem
    · exact Submodule.smul_mem fibRec.solSpace (√5)⁻¹ geom_goldenRatio_isSol_fibRec
    · exact Submodule.smul_mem fibRec.solSpace (√5)⁻¹ geom_goldenConj_isSol_fibRec

/-- **Binet's formula** as a dependent equality. -/
theorem coe_fib_eq : ∀ n, (Nat.fib n : ℝ) = (φ ^ n - ψ ^ n) / √5 := by
  rw [← funext_iff, Real.coe_fib_eq']

/-- Relationship between the Fibonacci Sequence, Golden Ratio and its conjugate's exponents -/
theorem fib_succ_sub_goldenRatio_mul_fib (n : ℕ) : Nat.fib (n + 1) - φ * Nat.fib n = ψ ^ n := by
  repeat rw [coe_fib_eq]
  rw [mul_div, div_sub_div_same, mul_sub, ← pow_succ']
  ring_nf
  have nz : √5 ≠ 0 := by norm_num
  rw [← (mul_inv_cancel₀ nz).symm, one_mul]

@[deprecated (since := "2025-08-23")]
alias _root_.fib_golden_conj_exp := fib_succ_sub_goldenRatio_mul_fib

/-- Relationship between the Fibonacci Sequence, Golden Ratio and its exponents -/
lemma goldenRatio_mul_fib_succ_add_fib (n : ℕ) : φ * Nat.fib (n + 1) + Nat.fib n = φ ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = φ * (Nat.fib n) + φ ^ 2 * (Nat.fib (n + 1)) := by
        simp only [Nat.fib_add_one (Nat.succ_ne_zero n), Nat.succ_sub_succ_eq_sub, tsub_zero,
          Nat.cast_add, goldenRatio_sq]; ring
      _ = φ * ((Nat.fib n) + φ * (Nat.fib (n + 1))) := by ring
      _ = φ ^ (n + 2) := by rw [add_comm, ih]; ring

@[deprecated (since := "2025-08-23")]
alias _root_.fib_golden_exp' := goldenRatio_mul_fib_succ_add_fib

end Real
