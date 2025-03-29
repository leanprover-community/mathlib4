/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Evaluating Power Series
We produce an algebra homomorphism from a power series ring `R[[X]]` to itself by substituting `X`
into a positive order element.

## Main Definitions
  * `PowerSeries.eval` is the linear map from `R[[X]]` to itself given by sending `X` to `X * f(X)`,
    where `f(X)` is a power series.

## Main results


## To do

This may need to be deleted, since we now have Evaluation.lean.

-/


suppress_compilation

variable {Γ R A : Type*}

open Finset

namespace PowerSeries

/-- Given a power series `f(X)`, a linear map taking `g(X)` to `g(X * f(X))`. -/
def eval [Semiring R] (f : PowerSeries R) : PowerSeries R →ₗ[R] PowerSeries R where
  toFun g := mk (fun n => ∑ i ∈ antidiagonal n, (coeff R i.1 g) * coeff R i.2 (f ^ i.1))
  map_add' x y := by
    ext n
    simp [add_mul, sum_add_distrib, fun n g => coeff_mk n fun n ↦
      ∑ i ∈ antidiagonal n, (coeff R i.1 g) • coeff R i.2 (f ^ i.1)]
  map_smul' r x := by
    ext n
    simp [mul_sum, mul_assoc, fun n g => coeff_mk n fun n ↦
      ∑ i ∈ antidiagonal n, (coeff R i.1 g) • coeff R i.2 (f ^ i.1)]

lemma eval_coeff [Semiring R] (f g : PowerSeries R) (n : ℕ) :
    (coeff R n) (eval f g) = ∑ i ∈ antidiagonal n, (coeff R i.1 g) • coeff R i.2 (f ^ i.1) :=
  coeff_mk n fun n ↦ ∑ i ∈ antidiagonal n, (coeff R i.1 g) • coeff R i.2 (f ^ i.1)

@[simp]
lemma eval_mul [CommSemiring R] (f g h : PowerSeries R) : eval f (g * h) = eval f g * eval f h := by
  ext n
  simp only [eval_coeff, coeff_mul, smul_eq_mul]
  simp_rw [sum_mul_sum, sum_mul, sum_sigma']
  rw [sum_nbij' (ι := ((_ : ℕ × ℕ) × (_ : ℕ × ℕ) × ℕ × ℕ))
    (κ := ((_ : ℕ × ℕ) × (_ : ℕ × ℕ) × ℕ × ℕ))
    (t := (antidiagonal n).sigma fun a ↦ (antidiagonal a.1).sigma fun b ↦ antidiagonal a.2)
    (g := fun ⟨⟨_i, _j⟩, ⟨⟨k, l⟩, ⟨m, n⟩⟩⟩ =>
      (coeff R k) g * (coeff R m) (f ^ k) * ((coeff R l) h * (coeff R n) (f ^ l)))
    (fun ⟨⟨i, j⟩, ⟨k, l⟩, ⟨m, n⟩⟩ ↦ ⟨(k + m, l + n), (k, m), (l, n)⟩)
    (fun ⟨⟨i, j⟩, ⟨k, l⟩, ⟨m, n⟩⟩ ↦ ⟨(k + m, l + n), (k, m), (l, n)⟩)]
  · simp_rw [sum_sigma]
    refine sum_congr rfl (fun i _ => ?_)
    refine sum_congr rfl (fun j hj => ?_)
    rw [show f ^ i.1 = f ^ j.1 * f ^ j.2 by simp [← (List.Nat.mem_antidiagonal.mp) hj, pow_add],
      coeff_mul, mul_sum]
    exact sum_congr rfl (fun _ _ => (by ring))
  · intro i hi
    simp_all only [mem_sigma, mem_antidiagonal, and_self, and_true, add_assoc]
    rw [add_left_comm i.2.2.1, hi.2.2, ← add_assoc, hi.2.1, hi.1]
  · intro i hi
    simp_all only [mem_sigma, mem_antidiagonal, add_assoc, and_self, and_true]
    rw [add_left_comm i.2.2.1, hi.2.2, ← add_assoc, hi.2.1, hi.1]
  all_goals
  intro i hi
  simp_all

@[simp]
lemma eval_one [Semiring R] (f : PowerSeries R) : eval f 1 = 1 := by
  ext n
  by_cases h : n = 0; · simp [h, eval_coeff]
  · simp only [eval_coeff, coeff_one, smul_eq_mul, ite_mul, one_mul, zero_mul, h, ↓reduceIte]
    refine sum_eq_zero (fun i hi => ?_)
    simp_all only [mem_antidiagonal, pow_zero, coeff_one, ite_eq_right_iff]
    omega

@[simp]
lemma eval_monomial [Semiring R] (f : PowerSeries R) (r : R) (n : ℕ) :
    eval f (monomial R n r) = r • X ^ n * f ^ n := by
  ext m
  simp only [eval_coeff, smul_eq_mul, coeff_mul, map_smul]
  refine sum_congr rfl fun ij hij => ?_
  by_cases h : ij.1 = n
  · rw [h, coeff_X_pow_self, coeff_monomial_same, mul_one]
  · simp [h, coeff_X_pow ij.1 n, coeff_monomial ij.1 n]

/-!
/-- Given a power series `f(X)`, an algebra map taking `g(X)` to `g(X * f(X))`. -/
@[simps]
def aeval [CommSemiring R] (f : PowerSeries R) : PowerSeries R →ₐ[R] PowerSeries R where
  toFun x := eval f x
  map_one' := eval_one f
  map_mul' x y := by simp
  map_zero' := by simp
  map_add' := by simp
  commutes' r := by
    ext n
    simp only [algebraMap_eq, ← monomial_zero_eq_C_apply, eval_monomial, coeff_monomial, pow_zero,
      mul_one, map_smul, coeff_one, smul_eq_mul, mul_ite, mul_zero]
-/
end PowerSeries
