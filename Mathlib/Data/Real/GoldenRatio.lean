/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Alexey Soloyev, Junyan Xu
-/
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Nat.Fib
import Mathlib.Data.Nat.PrimeNormNum
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.LinearRecurrence
import Mathlib.Tactic.NormNum.NatFib

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
@[reducible]
def goldenRatio :=
  (1 + Real.sqrt 5) / 2
#align golden_ratio goldenRatio

/-- The conjugate of the golden ratio `ψ := (1 - √5)/2`. -/
@[reducible]
def goldenConj :=
  (1 - Real.sqrt 5) / 2
#align golden_conj goldenConj

@[inherit_doc goldenRatio] scoped[Real] notation "φ" => goldenRatio
@[inherit_doc goldenConj] scoped[Real] notation "ψ" => goldenConj
open Real

/-- The inverse of the golden ratio is the opposite of its conjugate. -/
theorem inv_gold : φ⁻¹ = -ψ := by
  have : 1 + Real.sqrt 5 ≠ 0 := ne_of_gt (add_pos (by norm_num) <| Real.sqrt_pos.mpr (by norm_num))
  -- ⊢ φ⁻¹ = -ψ
  field_simp [sub_mul, mul_add]
  -- ⊢ 2 * 2 = 5 - 1
  norm_num
  -- 🎉 no goals
#align inv_gold inv_gold

/-- The opposite of the golden ratio is the inverse of its conjugate. -/
theorem inv_goldConj : ψ⁻¹ = -φ := by
  rw [inv_eq_iff_eq_inv, ← neg_inv, ← neg_eq_iff_eq_neg]
  -- ⊢ -ψ = φ⁻¹
  exact inv_gold.symm
  -- 🎉 no goals
#align inv_gold_conj inv_goldConj

@[simp]
theorem gold_mul_goldConj : φ * ψ = -1 := by
  field_simp
  -- ⊢ (1 + sqrt 5) * (1 - sqrt 5) = -(2 * 2)
  rw [← sq_sub_sq]
  -- ⊢ 1 ^ 2 - sqrt 5 ^ 2 = -(2 * 2)
  norm_num
  -- 🎉 no goals
#align gold_mul_gold_conj gold_mul_goldConj

@[simp]
theorem goldConj_mul_gold : ψ * φ = -1 := by
  rw [mul_comm]
  -- ⊢ φ * ψ = -1
  exact gold_mul_goldConj
  -- 🎉 no goals
#align gold_conj_mul_gold goldConj_mul_gold

@[simp]
theorem gold_add_goldConj : φ + ψ = 1 := by
  rw [goldenRatio, goldenConj]
  -- ⊢ (1 + sqrt 5) / 2 + (1 - sqrt 5) / 2 = 1
  ring
  -- 🎉 no goals
#align gold_add_gold_conj gold_add_goldConj

theorem one_sub_goldConj : 1 - φ = ψ := by
  linarith [gold_add_goldConj]
  -- 🎉 no goals
#align one_sub_gold_conj one_sub_goldConj

theorem one_sub_gold : 1 - ψ = φ := by
  linarith [gold_add_goldConj]
  -- 🎉 no goals
#align one_sub_gold one_sub_gold

@[simp]
theorem gold_sub_goldConj : φ - ψ = Real.sqrt 5 := by
  rw [goldenRatio, goldenConj]
  -- ⊢ (1 + sqrt 5) / 2 - (1 - sqrt 5) / 2 = sqrt 5
  ring
  -- 🎉 no goals
#align gold_sub_gold_conj gold_sub_goldConj

@[simp 1200]
theorem gold_sq : φ ^ 2 = φ + 1 := by
  rw [goldenRatio, ← sub_eq_zero]
  -- ⊢ ((1 + sqrt 5) / 2) ^ 2 - ((1 + sqrt 5) / 2 + 1) = 0
  ring_nf
  -- ⊢ sqrt 5 ^ 2 * (↑(Int.ofNat 1) / ↑4) + ↑(Int.negOfNat 5) * (↑(Int.ofNat 1) / ↑ …
  rw [Real.sq_sqrt] <;> norm_num
                        -- 🎉 no goals
                        -- 🎉 no goals
#align gold_sq gold_sq

@[simp 1200]
theorem goldConj_sq : ψ ^ 2 = ψ + 1 := by
  rw [goldenConj, ← sub_eq_zero]
  -- ⊢ ((1 - sqrt 5) / 2) ^ 2 - ((1 - sqrt 5) / 2 + 1) = 0
  ring_nf
  -- ⊢ sqrt 5 ^ 2 * (↑(Int.ofNat 1) / ↑4) + ↑(Int.negOfNat 5) * (↑(Int.ofNat 1) / ↑ …
  rw [Real.sq_sqrt] <;> norm_num
                        -- 🎉 no goals
                        -- 🎉 no goals
#align gold_conj_sq goldConj_sq

theorem gold_pos : 0 < φ :=
  mul_pos (by apply add_pos <;> norm_num) <| inv_pos.2 zero_lt_two
              -- ⊢ 0 < 1
                                -- 🎉 no goals
                                -- 🎉 no goals
#align gold_pos gold_pos

theorem gold_ne_zero : φ ≠ 0 :=
  ne_of_gt gold_pos
#align gold_ne_zero gold_ne_zero

theorem one_lt_gold : 1 < φ := by
  refine' lt_of_mul_lt_mul_left _ (le_of_lt gold_pos)
  -- ⊢ φ * 1 < φ * φ
  simp [← sq, gold_pos, zero_lt_one, - div_pow] -- Porting note: Added `- div_pow`
  -- 🎉 no goals
#align one_lt_gold one_lt_gold

theorem goldConj_neg : ψ < 0 := by
  linarith [one_sub_goldConj, one_lt_gold]
  -- 🎉 no goals
#align gold_conj_neg goldConj_neg

theorem goldConj_ne_zero : ψ ≠ 0 :=
  ne_of_lt goldConj_neg
#align gold_conj_ne_zero goldConj_ne_zero

theorem neg_one_lt_goldConj : -1 < ψ := by
  rw [neg_lt, ← inv_gold]
  -- ⊢ φ⁻¹ < 1
  exact inv_lt_one one_lt_gold
  -- 🎉 no goals
#align neg_one_lt_gold_conj neg_one_lt_goldConj

/-!
## Irrationality
-/


/-- The golden ratio is irrational. -/
theorem gold_irrational : Irrational φ := by
  have := Nat.Prime.irrational_sqrt (show Nat.Prime 5 by norm_num)
  -- ⊢ Irrational φ
  have := this.rat_add 1
  -- ⊢ Irrational φ
  have := this.rat_mul (show (0.5 : ℚ) ≠ 0 by norm_num)
  -- ⊢ Irrational φ
  convert this
  -- ⊢ φ = ↑0.5 * (↑1 + sqrt ↑5)
  norm_num
  -- ⊢ φ = 1 / 2 * (1 + sqrt 5)
  field_simp
  -- 🎉 no goals
#align gold_irrational gold_irrational

/-- The conjugate of the golden ratio is irrational. -/
theorem goldConj_irrational : Irrational ψ := by
  have := Nat.Prime.irrational_sqrt (show Nat.Prime 5 by norm_num)
  -- ⊢ Irrational ψ
  have := this.rat_sub 1
  -- ⊢ Irrational ψ
  have := this.rat_mul (show (0.5 : ℚ) ≠ 0 by norm_num)
  -- ⊢ Irrational ψ
  convert this
  -- ⊢ ψ = ↑0.5 * (↑1 - sqrt ↑5)
  norm_num
  -- ⊢ ψ = 1 / 2 * (1 - sqrt 5)
  field_simp
  -- 🎉 no goals
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
  -- ⊢ (↑(monomial { order := 2, coeffs := ![1, 1] }.order) 1 - Finset.sum Finset.u …
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ', ← smul_X_eq_monomial]
  -- 🎉 no goals
#align fib_rec_char_poly_eq fibRec_charPoly_eq

end Poly

/-- As expected, the Fibonacci sequence is a solution of `fibRec`. -/
theorem fib_isSol_fibRec : fibRec.IsSolution (fun x => x.fib : ℕ → α) := by
  rw [fibRec]
  -- ⊢ LinearRecurrence.IsSolution { order := 2, coeffs := ![1, 1] } fun x => ↑(Nat …
  intro n
  -- ⊢ (fun x => ↑(Nat.fib x)) (n + { order := 2, coeffs := ![1, 1] }.order) = Fins …
  simp only
  -- ⊢ ↑(Nat.fib (n + 2)) = Finset.sum Finset.univ fun x => Matrix.vecCons 1 ![1] x …
  rw [Nat.fib_add_two, add_comm]
  -- ⊢ ↑(Nat.fib (n + 1) + Nat.fib n) = Finset.sum Finset.univ fun x => Matrix.vecC …
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ']
  -- 🎉 no goals
#align fib_is_sol_fib_rec fib_isSol_fibRec

/-- The geometric sequence `fun n ↦ φ^n` is a solution of `fibRec`. -/
theorem geom_gold_isSol_fibRec : fibRec.IsSolution (φ ^ ·) := by
  rw [fibRec.geom_sol_iff_root_charPoly, fibRec_charPoly_eq]
  -- ⊢ IsRoot (X ^ 2 - (X + 1)) φ
  simp [sub_eq_zero, - div_pow] -- Porting note: Added `- div_pow`
  -- 🎉 no goals
#align geom_gold_is_sol_fib_rec geom_gold_isSol_fibRec

/-- The geometric sequence `fun n ↦ ψ^n` is a solution of `fibRec`. -/
theorem geom_goldConj_isSol_fibRec : fibRec.IsSolution (ψ ^ ·) := by
  rw [fibRec.geom_sol_iff_root_charPoly, fibRec_charPoly_eq]
  -- ⊢ IsRoot (X ^ 2 - (X + 1)) ψ
  simp [sub_eq_zero, - div_pow] -- Porting note: Added `- div_pow`
  -- 🎉 no goals
#align geom_gold_conj_is_sol_fib_rec geom_goldConj_isSol_fibRec

end Fibrec

/-- Binet's formula as a function equality. -/
theorem Real.coe_fib_eq' :
    (fun n => Nat.fib n : ℕ → ℝ) = fun n => (φ ^ n - ψ ^ n) / Real.sqrt 5 := by
  rw [fibRec.sol_eq_of_eq_init]
  · intro i hi
    -- ⊢ (fun n => ↑(Nat.fib n)) i = (fun n => (φ ^ n - ψ ^ n) / sqrt 5) i
    norm_cast at hi
    -- ⊢ (fun n => ↑(Nat.fib n)) i = (fun n => (φ ^ n - ψ ^ n) / sqrt 5) i
    fin_cases hi
    -- ⊢ (fun n => ↑(Nat.fib n)) 0 = (fun n => (φ ^ n - ψ ^ n) / sqrt 5) 0
    · simp
      -- 🎉 no goals
    · simp only [goldenRatio, goldenConj]
      -- ⊢ ↑(Nat.fib 1) = (((1 + sqrt 5) / 2) ^ 1 - ((1 - sqrt 5) / 2) ^ 1) / sqrt 5
      ring_nf
      -- ⊢ 1 = sqrt 5 * (sqrt 5)⁻¹
      rw [mul_inv_cancel]; norm_num
      -- ⊢ sqrt 5 ≠ 0
                           -- 🎉 no goals
  · exact fib_isSol_fibRec
    -- 🎉 no goals
  · -- Porting note: Rewrote this proof
    suffices LinearRecurrence.IsSolution fibRec
        ((fun n ↦ (sqrt 5)⁻¹ * φ ^ n) - (fun n ↦ (sqrt 5)⁻¹ * ψ ^ n)) by
      convert this
      rw [Pi.sub_apply]
      ring
    apply (@fibRec ℝ _).solSpace.sub_mem
    -- ⊢ (fun n => (sqrt 5)⁻¹ * φ ^ n) ∈ LinearRecurrence.solSpace fibRec
    · exact Submodule.smul_mem fibRec.solSpace (Real.sqrt 5)⁻¹ geom_gold_isSol_fibRec
      -- 🎉 no goals
    · exact Submodule.smul_mem fibRec.solSpace (Real.sqrt 5)⁻¹ geom_goldConj_isSol_fibRec
      -- 🎉 no goals
#align real.coe_fib_eq' Real.coe_fib_eq'

/-- Binet's formula as a dependent equality. -/
theorem Real.coe_fib_eq : ∀ n, (Nat.fib n : ℝ) = (φ ^ n - ψ ^ n) / Real.sqrt 5 := by
  rw [← Function.funext_iff, Real.coe_fib_eq']
  -- 🎉 no goals
#align real.coe_fib_eq Real.coe_fib_eq
