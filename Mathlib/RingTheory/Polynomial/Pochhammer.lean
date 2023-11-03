/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Tactic.Abel
import Mathlib.Data.Polynomial.Degree.Definitions
import Mathlib.Data.Polynomial.Eval
import Mathlib.Data.Polynomial.Monic
import Mathlib.Data.Polynomial.RingDivision

#align_import ring_theory.polynomial.pochhammer from "leanprover-community/mathlib"@"53b216bcc1146df1c4a0a86877890ea9f1f01589"

/-!
# The Pochhammer polynomials

We define and prove some basic relations about
`pochhammer S n : S[X] := X * (X + 1) * ... * (X + n - 1)`
which is also known as the rising factorial. A version of this definition
that is focused on `Nat` can be found in `Data.Nat.Factorial` as `Nat.ascFactorial`.

## Implementation

As with many other families of polynomials, even though the coefficients are always in `ℕ`,
we define the polynomial with coefficients in any `[Semiring S]`.

## TODO

There is lots more in this direction:
* q-factorials, q-binomials, q-Pochhammer.
-/


universe u v

open Polynomial

open Polynomial

section Semiring

variable (S : Type u) [Semiring S]

/-- `pochhammer S n` is the polynomial `X * (X+1) * ... * (X + n - 1)`,
with coefficients in the semiring `S`.
-/
noncomputable def pochhammer : ℕ → S[X]
  | 0 => 1
  | n + 1 => X * (pochhammer n).comp (X + 1)
#align pochhammer pochhammer

@[simp]
theorem pochhammer_zero : pochhammer S 0 = 1 :=
  rfl
#align pochhammer_zero pochhammer_zero

@[simp]
theorem pochhammer_one : pochhammer S 1 = X := by simp [pochhammer]
#align pochhammer_one pochhammer_one

theorem pochhammer_succ_left (n : ℕ) : pochhammer S (n + 1) = X * (pochhammer S n).comp (X + 1) :=
  by rw [pochhammer]
#align pochhammer_succ_left pochhammer_succ_left

theorem monic_pochhammer (n : ℕ) [Nontrivial S] [NoZeroDivisors S] :
    Monic <| pochhammer S n := by
  induction' n with n hn
  · simp
  · have : leadingCoeff (X + 1 : S[X]) = 1 := leadingCoeff_X_add_C 1
    rw [pochhammer_succ_left, Monic.def, leadingCoeff_mul, leadingCoeff_comp (ne_zero_of_eq_one <|
        natDegree_X_add_C 1 : natDegree (X + 1) ≠ 0), hn, monic_X, one_mul, one_mul, this, one_pow]

section

variable {S} {T : Type v} [Semiring T]

@[simp]
theorem pochhammer_map (f : S →+* T) (n : ℕ) : (pochhammer S n).map f = pochhammer T n := by
  induction' n with n ih
  · simp
  · simp [ih, pochhammer_succ_left, map_comp]
#align pochhammer_map pochhammer_map

end

@[simp, norm_cast]
theorem pochhammer_eval_cast (n k : ℕ) :
    (((pochhammer ℕ n).eval k : ℕ) : S) = ((pochhammer S n).eval k : S) := by
  rw [← pochhammer_map (algebraMap ℕ S), eval_map, ← eq_natCast (algebraMap ℕ S), eval₂_at_nat_cast,
    Nat.cast_id, eq_natCast]
#align pochhammer_eval_cast pochhammer_eval_cast

theorem pochhammer_eval_zero {n : ℕ} : (pochhammer S n).eval 0 = if n = 0 then 1 else 0 := by
  cases n
  · simp
  · simp [X_mul, Nat.succ_ne_zero, pochhammer_succ_left]
#align pochhammer_eval_zero pochhammer_eval_zero

theorem pochhammer_zero_eval_zero : (pochhammer S 0).eval 0 = 1 := by simp
#align pochhammer_zero_eval_zero pochhammer_zero_eval_zero

@[simp]
theorem pochhammer_ne_zero_eval_zero {n : ℕ} (h : n ≠ 0) : (pochhammer S n).eval 0 = 0 := by
  simp [pochhammer_eval_zero, h]
#align pochhammer_ne_zero_eval_zero pochhammer_ne_zero_eval_zero

theorem pochhammer_succ_right (n : ℕ) :
    pochhammer S (n + 1) = pochhammer S n * (X + (n : S[X])) := by
  suffices h : pochhammer ℕ (n + 1) = pochhammer ℕ n * (X + (n : ℕ[X]))
  · apply_fun Polynomial.map (algebraMap ℕ S) at h
    simpa only [pochhammer_map, Polynomial.map_mul, Polynomial.map_add, map_X,
      Polynomial.map_nat_cast] using h
  induction' n with n ih
  · simp
  · conv_lhs =>
      rw [pochhammer_succ_left, ih, mul_comp, ← mul_assoc, ← pochhammer_succ_left, add_comp, X_comp,
        nat_cast_comp, add_assoc, add_comm (1 : ℕ[X]), ← Nat.cast_succ]
#align pochhammer_succ_right pochhammer_succ_right

theorem pochhammer_succ_eval {S : Type*} [Semiring S] (n : ℕ) (k : S) :
    (pochhammer S (n + 1)).eval k = (pochhammer S n).eval k * (k + n) := by
  rw [pochhammer_succ_right, mul_add, eval_add, eval_mul_X, ← Nat.cast_comm, ← C_eq_nat_cast,
    eval_C_mul, Nat.cast_comm, ← mul_add]
#align pochhammer_succ_eval pochhammer_succ_eval

theorem pochhammer_succ_comp_X_add_one (n : ℕ) :
    (pochhammer S (n + 1)).comp (X + 1) =
      pochhammer S (n + 1) + (n + 1) • (pochhammer S n).comp (X + 1) := by
  suffices (pochhammer ℕ (n + 1)).comp (X + 1) =
      pochhammer ℕ (n + 1) + (n + 1) * (pochhammer ℕ n).comp (X + 1)
    by simpa [map_comp] using congr_arg (Polynomial.map (Nat.castRingHom S)) this
  nth_rw 2 [pochhammer_succ_left]
  rw [← add_mul, pochhammer_succ_right ℕ n, mul_comp, mul_comm, add_comp, X_comp, nat_cast_comp,
    add_comm, ← add_assoc]
  ring
set_option linter.uppercaseLean3 false in
#align pochhammer_succ_comp_X_add_one pochhammer_succ_comp_X_add_one

theorem Polynomial.mul_X_add_nat_cast_comp {p q : S[X]} {n : ℕ} :
    (p * (X + (n : S[X]))).comp q = p.comp q * (q + n) := by
  rw [mul_add, add_comp, mul_X_comp, ← Nat.cast_comm, nat_cast_mul_comp, Nat.cast_comm, mul_add]
set_option linter.uppercaseLean3 false in
#align polynomial.mul_X_add_nat_cast_comp Polynomial.mul_X_add_nat_cast_comp

theorem pochhammer_mul (n m : ℕ) :
    pochhammer S n * (pochhammer S m).comp (X + (n : S[X])) = pochhammer S (n + m) := by
  induction' m with m ih
  · simp
  · rw [pochhammer_succ_right, Polynomial.mul_X_add_nat_cast_comp, ← mul_assoc, ih,
      Nat.succ_eq_add_one, ← add_assoc, pochhammer_succ_right, Nat.cast_add, add_assoc]
#align pochhammer_mul pochhammer_mul

theorem pochhammer_nat_eq_ascFactorial (n : ℕ) :
    ∀ k, (pochhammer ℕ k).eval (n + 1) = n.ascFactorial k
  | 0 => by rw [pochhammer_zero, eval_one, Nat.ascFactorial_zero]
  | t + 1 => by
    rw [pochhammer_succ_right, eval_mul, pochhammer_nat_eq_ascFactorial n t]
    simp only [eval_add, eval_X, eval_nat_cast, Nat.cast_id]
    rw [Nat.ascFactorial_succ, add_right_comm, mul_comm]
#align pochhammer_nat_eq_asc_factorial pochhammer_nat_eq_ascFactorial

theorem pochhammer_nat_eq_descFactorial (a b : ℕ) :
    (pochhammer ℕ b).eval a = (a + b - 1).descFactorial b := by
  cases' b with b
  · rw [Nat.descFactorial_zero, pochhammer_zero, Polynomial.eval_one]
  rw [Nat.add_succ, Nat.succ_sub_succ, tsub_zero]
  cases a
  · simp only [Nat.zero_eq, ne_eq, Nat.succ_ne_zero, not_false_iff, pochhammer_ne_zero_eval_zero,
    zero_add, Nat.descFactorial_succ, le_refl, tsub_eq_zero_of_le, zero_mul]
  · rw [Nat.succ_add, ← Nat.add_succ, Nat.add_descFactorial_eq_ascFactorial,
      pochhammer_nat_eq_ascFactorial]
#align pochhammer_nat_eq_desc_factorial pochhammer_nat_eq_descFactorial

@[simp]
theorem pochhammer_natDegree (n : ℕ) [NoZeroDivisors S] [Nontrivial S] :
    (pochhammer S n).natDegree = n := by
  induction' n with n hn
  · simp
  · have : natDegree (X + (n : S[X])) = 1 := natDegree_X_add_C (n : S)
    rw [pochhammer_succ_right,
        natDegree_mul _ (ne_zero_of_natDegree_gt <| this.symm ▸ Nat.zero_lt_one), hn, this]
    cases n
    · simp
    · refine' ne_zero_of_natDegree_gt <| hn.symm ▸ Nat.succ_pos _

end Semiring

section StrictOrderedSemiring

variable {S : Type*} [StrictOrderedSemiring S]

theorem pochhammer_pos (n : ℕ) (s : S) (h : 0 < s) : 0 < (pochhammer S n).eval s := by
  induction' n with n ih
  · simp only [Nat.zero_eq, pochhammer_zero, eval_one]
    exact zero_lt_one
  · rw [pochhammer_succ_right, mul_add, eval_add, ← Nat.cast_comm, eval_nat_cast_mul, eval_mul_X,
      Nat.cast_comm, ← mul_add]
    exact mul_pos ih (lt_of_lt_of_le h ((le_add_iff_nonneg_right _).mpr (Nat.cast_nonneg n)))
#align pochhammer_pos pochhammer_pos

end StrictOrderedSemiring

section Factorial

open Nat

variable (S : Type*) [Semiring S] (r n : ℕ)

@[simp]
theorem pochhammer_eval_one (S : Type*) [Semiring S] (n : ℕ) :
    (pochhammer S n).eval (1 : S) = (n ! : S) := by
  rw_mod_cast [pochhammer_nat_eq_ascFactorial, Nat.zero_ascFactorial]
#align pochhammer_eval_one pochhammer_eval_one

theorem factorial_mul_pochhammer (S : Type*) [Semiring S] (r n : ℕ) :
    (r ! : S) * (pochhammer S n).eval (r + 1 : S) = (r + n)! := by
  rw_mod_cast [pochhammer_nat_eq_ascFactorial, Nat.factorial_mul_ascFactorial]
#align factorial_mul_pochhammer factorial_mul_pochhammer

theorem pochhammer_nat_eval_succ (r : ℕ) :
    ∀ n : ℕ, n * (pochhammer ℕ r).eval (n + 1) = (n + r) * (pochhammer ℕ r).eval n
  | 0 => by
    by_cases h : r = 0
    · simp only [h, zero_mul, zero_add]
    · simp only [pochhammer_eval_zero, zero_mul, if_neg h, mul_zero]
  | k + 1 => by simp only [pochhammer_nat_eq_ascFactorial, Nat.succ_ascFactorial, add_right_comm]
#align pochhammer_nat_eval_succ pochhammer_nat_eval_succ

theorem pochhammer_eval_succ (r n : ℕ) :
    (n : S) * (pochhammer S r).eval (n + 1 : S) = (n + r) * (pochhammer S r).eval (n : S) := by
  exact_mod_cast congr_arg Nat.cast (pochhammer_nat_eval_succ r n)
#align pochhammer_eval_succ pochhammer_eval_succ

end Factorial
