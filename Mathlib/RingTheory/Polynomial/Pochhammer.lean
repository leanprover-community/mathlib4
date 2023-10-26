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
`ascPochhammer S n : S[X] := X * (X + 1) * ... * (X + n - 1)`
which is also known as the rising factorial and about
`descPochhammer R n : R[X] := X * (X - 1) * ... * (X - n + 1)`
which is also known as the falling factorial. Versions of this definition
that are focused on `Nat` can be found in `Data.Nat.Factorial` as `Nat.ascFactorial` and
`Nat.descFactorial`.

## Implementation

As with many other families of polynomials, even though the coefficients are always in `ℕ` or `ℤ` ,
we define the polynomial with coefficients in any `[Semiring S]` or `[Ring R]`.

## TODO

There is lots more in this direction:
* q-factorials, q-binomials, q-Pochhammer.
-/


universe u v

open Polynomial

open Polynomial

section Semiring

variable (S : Type u) [Semiring S]

/-- `ascPochhammer S n` is the polynomial `X * (X + 1) * ... * (X + n - 1)`,
with coefficients in the semiring `S`.
-/
noncomputable def ascPochhammer : ℕ → S[X]
  | 0 => 1
  | n + 1 => X * (ascPochhammer n).comp (X + 1)
#align pochhammer ascPochhammer

@[simp]
theorem ascPochhammer_zero : ascPochhammer S 0 = 1 :=
  rfl
#align pochhammer_zero ascPochhammer_zero

@[simp]
theorem ascPochhammer_one : ascPochhammer S 1 = X := by simp [ascPochhammer]
#align pochhammer_one ascPochhammer_one

theorem ascPochhammer_succ_left (n : ℕ) :
    ascPochhammer S (n + 1) = X * (ascPochhammer S n).comp (X + 1) :=
  by rw [ascPochhammer]
#align pochhammer_succ_left ascPochhammer_succ_left

theorem monic_ascPochhammer (n : ℕ) [Nontrivial S] [NoZeroDivisors S] :
    Monic <| ascPochhammer S n := by
  induction' n with n hn
  · simp
  · have : leadingCoeff (X + 1 : S[X]) = 1 := leadingCoeff_X_add_C 1
    rw [ascPochhammer_succ_left, Monic.def, leadingCoeff_mul,
      leadingCoeff_comp (ne_zero_of_eq_one <| natDegree_X_add_C 1 : natDegree (X + 1) ≠ 0), hn,
      monic_X, one_mul, one_mul, this, one_pow]

section

variable {S} {T : Type v} [Semiring T]

@[simp]
theorem ascPochhammer_map (f : S →+* T) (n : ℕ) :
    (ascPochhammer S n).map f = ascPochhammer T n := by
  induction' n with n ih
  · simp
  · simp [ih, ascPochhammer_succ_left, map_comp]
#align pochhammer_map ascPochhammer_map

end

@[simp, norm_cast]
theorem ascPochhammer_eval_cast (n k : ℕ) :
    (((ascPochhammer ℕ n).eval k : ℕ) : S) = ((ascPochhammer S n).eval k : S) := by
  rw [← ascPochhammer_map (algebraMap ℕ S), eval_map, ← eq_natCast (algebraMap ℕ S),
      eval₂_at_nat_cast,Nat.cast_id, eq_natCast]
#align pochhammer_eval_cast ascPochhammer_eval_cast

theorem ascPochhammer_eval_zero {n : ℕ} : (ascPochhammer S n).eval 0 = if n = 0 then 1 else 0 := by
  cases n
  · simp
  · simp [X_mul, Nat.succ_ne_zero, ascPochhammer_succ_left]
#align pochhammer_eval_zero ascPochhammer_eval_zero

theorem ascPochhammer_zero_eval_zero : (ascPochhammer S 0).eval 0 = 1 := by simp
#align pochhammer_zero_eval_zero ascPochhammer_zero_eval_zero

@[simp]
theorem ascPochhammer_ne_zero_eval_zero {n : ℕ} (h : n ≠ 0) : (ascPochhammer S n).eval 0 = 0 := by
  simp [ascPochhammer_eval_zero, h]
#align pochhammer_ne_zero_eval_zero ascPochhammer_ne_zero_eval_zero

theorem ascPochhammer_succ_right (n : ℕ) :
    ascPochhammer S (n + 1) = ascPochhammer S n * (X + (n : S[X])) := by
  suffices h : ascPochhammer ℕ (n + 1) = ascPochhammer ℕ n * (X + (n : ℕ[X]))
  · apply_fun Polynomial.map (algebraMap ℕ S) at h
    simpa only [ascPochhammer_map, Polynomial.map_mul, Polynomial.map_add, map_X,
      Polynomial.map_nat_cast] using h
  induction' n with n ih
  · simp
  · conv_lhs =>
      rw [ascPochhammer_succ_left, ih, mul_comp, ← mul_assoc, ← ascPochhammer_succ_left, add_comp,
          X_comp, nat_cast_comp, add_assoc, add_comm (1 : ℕ[X]), ← Nat.cast_succ]
#align pochhammer_succ_right ascPochhammer_succ_right

theorem ascPochhammer_succ_eval {S : Type*} [Semiring S] (n : ℕ) (k : S) :
    (ascPochhammer S (n + 1)).eval k = (ascPochhammer S n).eval k * (k + n) := by
  rw [ascPochhammer_succ_right, mul_add, eval_add, eval_mul_X, ← Nat.cast_comm, ← C_eq_nat_cast,
    eval_C_mul, Nat.cast_comm, ← mul_add]
#align pochhammer_succ_eval ascPochhammer_succ_eval

theorem ascPochhammer_succ_comp_X_add_one (n : ℕ) :
    (ascPochhammer S (n + 1)).comp (X + 1) =
      ascPochhammer S (n + 1) + (n + 1) • (ascPochhammer S n).comp (X + 1) := by
  suffices (ascPochhammer ℕ (n + 1)).comp (X + 1) =
      ascPochhammer ℕ (n + 1) + (n + 1) * (ascPochhammer ℕ n).comp (X + 1)
    by simpa [map_comp] using congr_arg (Polynomial.map (Nat.castRingHom S)) this
  nth_rw 2 [ascPochhammer_succ_left]
  rw [← add_mul, ascPochhammer_succ_right ℕ n, mul_comp, mul_comm, add_comp, X_comp, nat_cast_comp,
    add_comm, ← add_assoc]
  ring
set_option linter.uppercaseLean3 false in
#align pochhammer_succ_comp_X_add_one ascPochhammer_succ_comp_X_add_one

theorem ascPochhammer_mul (n m : ℕ) :
    ascPochhammer S n * (ascPochhammer S m).comp (X + (n : S[X])) = ascPochhammer S (n + m) := by
  induction' m with m ih
  · simp
  · rw [ascPochhammer_succ_right, Polynomial.mul_X_add_nat_cast_comp, ← mul_assoc, ih,
      Nat.succ_eq_add_one, ← add_assoc, ascPochhammer_succ_right, Nat.cast_add, add_assoc]
#align pochhammer_mul ascPochhammer_mul

theorem ascPochhammer_nat_eq_ascFactorial (n : ℕ) :
    ∀ k, (ascPochhammer ℕ k).eval n = n.ascFactorial k
  | 0 => by rw [ascPochhammer_zero, eval_one, Nat.ascFactorial_zero]
  | t + 1 => by
    rw [ascPochhammer_succ_right, eval_mul, ascPochhammer_nat_eq_ascFactorial n t, eval_add, eval_X,
      eval_nat_cast, Nat.cast_id, Nat.ascFactorial_succ, mul_comm]
#align pochhammer_nat_eq_asc_factorial ascPochhammer_nat_eq_ascFactorial

theorem ascPochhammer_nat_eq_descFactorial (a b : ℕ) :
    (ascPochhammer ℕ b).eval a = (a + b - 1).descFactorial b := by
  rw [ascPochhammer_nat_eq_ascFactorial, Nat.add_descFactorial_eq_ascFactorial]
#align pochhammer_nat_eq_desc_factorial ascPochhammer_nat_eq_descFactorial

@[simp]
theorem ascPochhammer_natDegree (n : ℕ) [NoZeroDivisors S] [Nontrivial S] :
    (ascPochhammer S n).natDegree = n := by
  induction' n with n hn
  · simp
  · have : natDegree (X + (n : S[X])) = 1 := natDegree_X_add_C (n : S)
    rw [ascPochhammer_succ_right,
        natDegree_mul _ (ne_zero_of_natDegree_gt <| this.symm ▸ Nat.zero_lt_one), hn, this]
    cases n
    · simp
    · refine' ne_zero_of_natDegree_gt <| hn.symm ▸ Nat.succ_pos _

end Semiring

section StrictOrderedSemiring

variable {S : Type*} [StrictOrderedSemiring S]

theorem ascPochhammer_pos (n : ℕ) (s : S) (h : 0 < s) : 0 < (ascPochhammer S n).eval s := by
  induction' n with n ih
  · simp only [Nat.zero_eq, ascPochhammer_zero, eval_one]
    exact zero_lt_one
  · rw [ascPochhammer_succ_right, mul_add, eval_add, ← Nat.cast_comm, eval_nat_cast_mul, eval_mul_X,
      Nat.cast_comm, ← mul_add]
    exact mul_pos ih (lt_of_lt_of_le h ((le_add_iff_nonneg_right _).mpr (Nat.cast_nonneg n)))
#align pochhammer_pos ascPochhammer_pos

end StrictOrderedSemiring

section Factorial

open Nat

variable (S : Type*) [Semiring S] (r n : ℕ)

@[simp]
theorem ascPochhammer_eval_one (S : Type*) [Semiring S] (n : ℕ) :
    (ascPochhammer S n).eval (1 : S) = (n ! : S) := by
  rw_mod_cast [ascPochhammer_nat_eq_ascFactorial, Nat.one_ascFactorial]
#align pochhammer_eval_one ascPochhammer_eval_one

theorem factorial_mul_ascPochhammer (S : Type*) [Semiring S] (r n : ℕ) :
    (r ! : S) * (ascPochhammer S n).eval (r + 1 : S) = (r + n)! := by
  nth_rw 1 [← Nat.add_sub_cancel r 1]
  rw_mod_cast [ascPochhammer_nat_eq_ascFactorial, Nat.factorial_mul_ascFactorial, succ_add_sub_one]
  exact succ_pos r
#align factorial_mul_pochhammer factorial_mul_ascPochhammer

theorem ascPochhammer_nat_eval_succ (r : ℕ) :
    ∀ n : ℕ, n * (ascPochhammer ℕ r).eval (n + 1) = (n + r) * (ascPochhammer ℕ r).eval n
  | 0 => by
    by_cases h : r = 0
    · simp only [h, zero_mul, zero_add]
    · simp only [ascPochhammer_eval_zero, zero_mul, if_neg h, mul_zero]
  | k + 1 => by simp only [ascPochhammer_nat_eq_ascFactorial, Nat.succ_ascFactorial, add_right_comm]
#align pochhammer_nat_eval_succ ascPochhammer_nat_eval_succ

theorem ascPochhammer_eval_succ (r n : ℕ) :
    (n : S) * (ascPochhammer S r).eval (n + 1 : S) =
    (n + r) * (ascPochhammer S r).eval (n : S) := by
  exact_mod_cast congr_arg Nat.cast (ascPochhammer_nat_eval_succ r n)
#align pochhammer_eval_succ ascPochhammer_eval_succ

end Factorial

section Ring

variable (R : Type u) [Ring R]

/-- `descPochhammer R n` is the polynomial `X * (X - 1) * ... * (X - n + 1)`,
with coefficients in the ring `R`.
-/
noncomputable def descPochhammer : ℕ → R[X]
  | 0 => 1
  | n + 1 => X * (descPochhammer n).comp (X - 1)

@[simp]
theorem descPochhammer_zero : descPochhammer R 0 = 1 :=
  rfl

@[simp]
theorem descPochhammer_one : descPochhammer R 1 = X := by simp [descPochhammer]

theorem descPochhammer_succ_left (n : ℕ) :
    descPochhammer R (n + 1) = X * (descPochhammer R n).comp (X - 1) :=
  by rw [descPochhammer]

theorem monic_descPochhammer (n : ℕ) [Nontrivial R] [NoZeroDivisors R] :
    Monic <| descPochhammer R n := by
  induction' n with n hn
  · simp
  · have h : leadingCoeff (X - 1 : R[X]) = 1 := leadingCoeff_X_sub_C 1
    have : natDegree (X - (1 : R[X])) ≠ 0 := ne_zero_of_eq_one <| natDegree_X_sub_C (1 : R)
    rw [descPochhammer_succ_left, Monic.def, leadingCoeff_mul, leadingCoeff_comp this, hn, monic_X,
        one_mul, one_mul, h, one_pow]

section

variable {R} {T : Type v} [Ring T]

@[simp]
theorem descPochhammer_map (f : R →+* T) (n : ℕ) :
    (descPochhammer R n).map f = descPochhammer T n := by
  induction' n with n ih
  · simp
  · simp [ih, descPochhammer_succ_left, map_comp]
end

@[simp, norm_cast]
theorem descPochhammer_eval_cast (n : ℕ) (k : ℤ) :
    (((descPochhammer ℤ n).eval k : ℤ) : R) = ((descPochhammer R n).eval k : R) := by
  rw [← descPochhammer_map (algebraMap ℤ R), eval_map, ← eq_intCast (algebraMap ℤ R)]
  simp only [algebraMap_int_eq, eq_intCast, eval₂_at_int_cast, Nat.cast_id, eq_natCast, Int.cast_id]

theorem descPochhammer_eval_zero {n : ℕ} :
    (descPochhammer R n).eval 0 = if n = 0 then 1 else 0 := by
  cases n
  · simp
  · simp [X_mul, Nat.succ_ne_zero, descPochhammer_succ_left]

theorem descPochhammer_zero_eval_zero : (descPochhammer R 0).eval 0 = 1 := by simp

@[simp]
theorem descPochhammer_ne_zero_eval_zero {n : ℕ} (h : n ≠ 0) : (descPochhammer R n).eval 0 = 0 := by
  simp [descPochhammer_eval_zero, h]

theorem descPochhammer_succ_right (n : ℕ) :
    descPochhammer R (n + 1) = descPochhammer R n * (X - (n : R[X])) := by
  suffices h : descPochhammer ℤ (n + 1) = descPochhammer ℤ n * (X - (n : ℤ[X]))
  · apply_fun Polynomial.map (algebraMap ℤ R) at h
    simpa [descPochhammer_map, Polynomial.map_mul, Polynomial.map_add, map_X,
      Polynomial.map_int_cast] using h
  induction' n with n ih
  · simp [descPochhammer]
  · conv_lhs =>
      rw [descPochhammer_succ_left, ih, mul_comp, ← mul_assoc, ← descPochhammer_succ_left, sub_comp,
          X_comp, nat_cast_comp]
    nth_rw 1 [Nat.succ_eq_add_one]
    rw [Nat.succ_eq_one_add, Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub]

@[simp]
theorem descPochhammer_natDegree (n : ℕ) [NoZeroDivisors R] [Nontrivial R] :
    (descPochhammer R n).natDegree = n := by
  induction' n with n hn
  · simp
  · have : natDegree (X - (n : R[X])) = 1 := natDegree_X_sub_C (n : R)
    rw [descPochhammer_succ_right,
        natDegree_mul _ (ne_zero_of_natDegree_gt <| this.symm ▸ Nat.zero_lt_one), hn, this]
    cases n
    · simp
    · refine' ne_zero_of_natDegree_gt <| hn.symm ▸ Nat.succ_pos _

theorem descPochhammer_succ_eval {S : Type*} [Ring S] (n : ℕ) (k : S) :
    (descPochhammer S (n + 1)).eval k = (descPochhammer S n).eval k * (k - n) := by
  rw [descPochhammer_succ_right, mul_sub, eval_sub, eval_mul_X, ← Nat.cast_comm, ← C_eq_nat_cast,
    eval_C_mul, Nat.cast_comm, ← mul_sub]

theorem descPochhammer_succ_comp_X_sub_one (n : ℕ) :
    (descPochhammer R (n + 1)).comp (X - 1) =
      descPochhammer R (n + 1) - (n + (1 : R[X])) • (descPochhammer R n).comp (X - 1) := by
  suffices (descPochhammer ℤ (n + 1)).comp (X - 1) =
      descPochhammer ℤ (n + 1) - (n + 1) * (descPochhammer ℤ n).comp (X - 1)
    by simpa [map_comp] using congr_arg (Polynomial.map (Int.castRingHom R)) this
  nth_rw 2 [descPochhammer_succ_left]
  rw [← sub_mul, descPochhammer_succ_right ℤ n, mul_comp, mul_comm, sub_comp, X_comp, nat_cast_comp]
  ring

theorem descPochhammer_mul (n m : ℕ) :
    descPochhammer R n * (descPochhammer R m).comp (X - (n : R[X])) = descPochhammer R (n + m) := by
  induction' m with m ih
  · simp
  · rw [descPochhammer_succ_right, Polynomial.mul_X_sub_int_cast_comp, ← mul_assoc, ih,
      Nat.succ_eq_add_one, ← add_assoc, descPochhammer_succ_right, Nat.cast_add, sub_add_eq_sub_sub]

theorem descPochhammer_int_eq_descFactorial (n : ℕ) :
    ∀ k, (descPochhammer ℤ k).eval (n : ℤ) = n.descFactorial k
  | 0 => by
    rw [descPochhammer_zero, eval_one, Nat.descFactorial_zero]
    rfl
  | t + 1 => by
    rw [descPochhammer_succ_right, eval_mul, descPochhammer_int_eq_descFactorial n t]
    simp only [eval_sub, eval_X, eval_nat_cast, Nat.descFactorial_succ, Nat.cast_mul,
        Nat.descFactorial_eq_zero_iff_lt]
    rw [mul_comm]
    simp only [mul_eq_mul_right_iff, Nat.cast_eq_zero, Nat.descFactorial_eq_zero_iff_lt]
    by_cases n < t
    · tauto
    · left
      exact (Int.ofNat_sub <| not_lt.mp h).symm

theorem descPochhammer_int_eq_ascFactorial (a b : ℕ) :
    (descPochhammer ℤ b).eval (a + b : ℤ) = (a + 1).ascFactorial b := by
  rw [← Nat.cast_add, descPochhammer_int_eq_descFactorial (a + b) b, ← Nat.succ_add_sub_one a b,
      Nat.add_descFactorial_eq_ascFactorial]

end Ring
