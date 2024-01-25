/-
Copyright (c) 2023 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Polynomial.Monic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Superfactorial

This file defines the [superfactorial](https://en.wikipedia.org/wiki/Superfactorial)
`sf n = 1! * 2! * 3! * ... * n!`.

## Main declarations

* `Nat.superFactorial`: The superfactorial, denoted by `sf`.
-/


namespace Nat

/-- `Nat.superFactorial n` is the superfactorial of `n`. -/
def superFactorial : ℕ → ℕ
  | 0 => 1
  | succ n => factorial n.succ * superFactorial n

/-- `sf` notation for superfactorial -/
scoped notation "sf" n:60 => Nat.superFactorial n

section SuperFactorial

variable {n : ℕ}

@[simp]
theorem superFactorial_zero : sf 0 = 1 :=
  rfl

theorem superFactorial_succ (n : ℕ) : (sf n.succ) = (n + 1)! * sf n :=
  rfl

@[simp]
theorem superFactorial_one : sf 1 = 1 :=
  rfl

@[simp]
theorem superFactorial_two : sf 2 = 2 :=
  rfl

open BigOperators Finset

@[simp]
theorem prod_Icc_factorial : ∀ n : ℕ, ∏ x in Icc 1 n, x ! = sf n
  | 0 => rfl
  | n + 1 => by
    rw [← Ico_succ_right 1 n.succ, prod_Ico_succ_top <| Nat.succ_le_succ <| Nat.zero_le n,
    Nat.factorial_succ, Ico_succ_right 1 n, prod_Icc_factorial n, superFactorial, factorial,
    Nat.succ_eq_add_one, mul_comm]

@[simp]
theorem prod_range_factorial_succ : ∀ n : ℕ, ∏ x in range n, (x + 1)! = sf n :=
  fun n => (prod_Icc_factorial n) ▸ range_eq_Ico ▸ Finset.prod_Ico_add' _ _ _ _

@[simp]
theorem prod_range_succ_factorial : ∀ n : ℕ, ∏ x in range (n + 1), x ! = sf n
  | 0 => rfl
  | n + 1 => by
    rw [prod_range_succ, prod_range_succ_factorial n, mul_comm, superFactorial]

variable {R : Type*} [CommRing R]

theorem det_vandermonde_id_eq_superFactorial (n : ℕ) :
    (Matrix.vandermonde (fun (i : Fin (n + 1)) ↦ (i : R))).det = Nat.superFactorial n := by
  induction' n with n hn
  · simp [Matrix.det_vandermonde]
  · rw [Nat.superFactorial, Matrix.det_vandermonde, Fin.prod_univ_succAbove _ 0]
    push_cast
    congr
    · simp only [Fin.val_zero, Nat.cast_zero, sub_zero]
      norm_cast
      simp [Fin.prod_univ_eq_prod_range (fun i ↦ (↑i + 1)) (n + 1)]
    · rw [Matrix.det_vandermonde] at hn
      simp [hn]
open Finset

theorem superFactorial_eq_square_times_factorial (k : ℕ) :
    ∃ n, IsSquare n ∧ sf (4 * k) = n * (2 * k) ! := by
  by_cases k = 0
  · exact ⟨1, ⟨isSquare_one, h ▸ rfl⟩⟩
  have hk := Nat.sub_add_cancel <| succ_mul_pos 1 <| Nat.pos_of_ne_zero h
  have h_succ : succ (2 * k - 1) = 2 * k := by linarith
  use (∏ x in Ico 0 (2 * k - 1), (x + 1) !) * (∏ x in Ico (2 * k) (4 * k), (x + 1) !)
  have h : sf (4 * k) = (∏ x in Ico 0 (2 * k - 1), (x + 1) !) *
       (∏ x in Ico (2 * k) (4 * k), (x + 1) !) * (2 * k) ! := by
    rw [mul_assoc, mul_comm _ (2 * k) !, ← range_eq_Ico, prod_range_factorial_succ,
        ← mul_assoc, mul_comm _ (2 * k)!]
    have := superFactorial_succ (2 * k - 1)
    simp only [hk] at this
    norm_num at this
    rw [← this, ← prod_range_factorial_succ, range_eq_Ico, ← prod_range_factorial_succ,
        range_eq_Ico, h_succ]
    exact (Finset.prod_Ico_consecutive (fun x => (x + 1) !) (zero_le (2 * k)) (by linarith)).symm
  constructor
  · have h' : sf (4 * k) =
       (2 ^ k * ∏ x in Ico 0 (2 * k), (2 * x + 1)!) ^ 2 * (2 * k)! := by
      calc
        sf (4 * k) = ∏ x in Ico 0 (2 * (2 * k)), (x + 1) ! := by
          rw [←range_eq_Ico, prod_range_factorial_succ, ← mul_assoc]
        _ = ∏ x in Ico 0 (2 * k), ((2 * x + 1) !) * (((1 + 2 * x) + 1) !) := by
          rw [mul_comm]
          have prod_even_oddFin : ∀ (n : ℕ), ∀  (f : ℕ → ℕ),
              ∏ x : Fin (n * 2), f x =  ∏ x : Fin n, (f (2 * x)) * (f (1 + 2 * x)) := by
            intros n f
            rw [(Equiv.prod_comp' finProdFinEquiv (fun i ↦ f ↑(finProdFinEquiv i)) (fun i ↦ f ↑i)
                    (congrFun rfl)).symm, Fintype.prod_prod_type]
            simp only [finProdFinEquiv_apply_val]
            congr
            ext x
            rw [Fin.prod_univ_eq_prod_range (fun x_1 => f (↑x_1 + 2 * ↑x)) 2,
                Finset.prod_range_succ]
            simp
          have prod_even_oddIco : ∀ (n : ℕ), ∀ (f : ℕ → ℕ),
              ∏ x in Ico 0 (n * 2), f x =  ∏ x in Ico 0 n, (f (2 * x)) * (f (1 + 2 * x)) := by
            intros n f
            convert prod_even_oddFin n f
            · rw [Ico_zero_eq_range, ← (Fin.prod_univ_eq_prod_range f (n * 2))]
            · rw [Ico_zero_eq_range, ← (Fin.prod_univ_eq_prod_range _ n)]
          exact prod_even_oddIco (2 * k) (fun x => (x + 1) !)
        _ = ∏ x in Ico 0 (2 * k), (2 * (x + 1)) * (2 * x + 1)! ^ 2 := by
          simp only [pow_two, ← mul_assoc]
          apply Finset.prod_congr rfl
          intro x _
          rw [add_rotate 1 (2 * x) 1, mul_comm]
          rfl
        _ = (2 ^ k) ^ 2 *
            (∏ x in Ico 0 (2 * k), (x + 1)) * (∏ x in Ico 0 (2 * k), (2 * x + 1)!) ^ 2 := by
          rw [prod_mul_distrib, prod_pow, prod_mul_distrib, pow_eq_prod_const 2]
          simp only [prod_const, card_Ico, tsub_zero, card_range]
          rw [← pow_mul 2 k, mul_comm 2 k]
        _ = (2 ^ k * ∏ x in Ico 0 (2 * k), (2 * x + 1)!) ^ 2 * (2 * k)! := by
          rw [mul_assoc, mul_comm (∏ x in Ico 0 (2 * k), (x + 1)), ← mul_assoc, mul_pow]
          simp only [Ico_zero_eq_range, prod_range_add_one_eq_factorial]
    use 2 ^ k * ∏ x in Ico 0 (2 * k), (2 * x + 1)!
    rw [← pow_two]
    exact (mul_right_cancel₀ (factorial_ne_zero (2 * k)) (h' ▸ h)).symm
  · exact h

private theorem matrixOf_eval_descPochhammer_eq_mul_matrixOf_choose {n : ℕ} (v : Fin n → ℕ) :
    (Matrix.of (fun (i j : Fin n) => (descPochhammer ℤ j).eval (v i : ℤ))).det =
    (∏ i : Fin n, Nat.factorial i) *
      (Matrix.of (fun (i j : Fin n) => (Nat.choose (v i) (j : ℕ) : ℤ))).det := by
  convert Matrix.det_mul_row (fun (i : Fin n) => ((Nat.factorial (i : ℕ)):ℤ)) _
  · rw [Matrix.of_apply, descPochhammer_int_eq_descFactorial _ _]
    congr
    exact Nat.descFactorial_eq_factorial_mul_choose _ _
  · rw [Nat.cast_prod]

theorem superFactorial_dvd_vandermonde_det {n : ℕ} (v : Fin (n + 1) → ℤ) :
    ↑(Nat.superFactorial n) ∣ (Matrix.vandermonde v).det := by
  let m := inf' univ ⟨0, mem_univ _⟩ v
  let w' := fun i ↦ (v i - m).toNat
  have hw' : ∀ i, (w' i : ℤ) = v i - m := fun i ↦ Int.toNat_sub_of_le (inf'_le _ (mem_univ _))
  have h := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde (fun i ↦ ↑(w' i))
      (fun i => descPochhammer ℤ i)
      (fun i => descPochhammer_natDegree ℤ i)
      (fun i => monic_descPochhammer ℤ i)
  conv_lhs at h => simp only [hw', Matrix.det_vandermonde_sub]
  use (Matrix.of (fun (i j : Fin (n + 1)) => (Nat.choose (w' i) (j : ℕ) : ℤ))).det
  simp [h, matrixOf_eval_descPochhammer_eq_mul_matrixOf_choose w', Fin.prod_univ_eq_prod_range]

end SuperFactorial

end Nat
