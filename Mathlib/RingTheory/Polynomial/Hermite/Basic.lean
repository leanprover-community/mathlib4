/-
Copyright (c) 2023 Luke Mantle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Mantle
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Hermite polynomials

This file defines `Polynomial.hermite n`, the `n`th probabilists' Hermite polynomial.

## Main definitions

* `Polynomial.hermite R n`: the `n`th probabilists' Hermite polynomial,
  with coefficients in an arbitrary commutative ring `R`.

## Results

* `Polynomial.hermite_succ`: the recursion `hermite (n+1) = (x - d/dx) (hermite n)`
* `Polynomial.coeff_hermite_explicit`: a closed formula for (nonvanishing) coefficients in terms
  of binomial coefficients and double factorials.
* `Polynomial.coeff_hermite_of_odd_add`: for `n`,`k` where `n+k` is odd, `(hermite n).coeff k` is
  zero.
* `Polynomial.coeff_hermite_of_even_add`: a closed formula for `(hermite n).coeff k` when `n+k` is
  even, equivalent to `Polynomial.coeff_hermite_explicit`.
* `Polynomial.monic_hermite`: for all `n`, `hermite n` is monic.
* `Polynomial.degree_hermite`: for all `n`, `hermite n` has degree `n`.
* `Polynomial.coeff_hermite_eq_intCast`: the coefficients are the images of the integral
coefficients.
* `Polynomial.coeff_hermite_explicit'` closed form for the coefficient as integers.

## Implementation notes

The Hermite polynomials are defined by a recursion with integer coefficients, so `hermite R n`
is always the image of `hermite ℤ n` under the unique ring hom `ℤ →+* R` (`map_hermite`).
The explicit coefficient formulas are proved over `ℤ` and transported to `R` by `Int.cast`.
Degree and monicity statements require `Nontrivial R`, since over the zero ring every polynomial
vanishes.

## References

* [Hermite Polynomials](https://en.wikipedia.org/wiki/Hermite_polynomials)

-/

@[expose] public section

noncomputable section

open Polynomial

namespace Polynomial

variable (R : Type*) [CommRing R]

/-- The probabilists' Hermite polynomials. -/
noncomputable def hermite : ℕ → Polynomial R
  | 0 => 1
  | n + 1 => X * hermite n - derivative (hermite n)

/-- The recursion `hermite R (n+1) = (x - d/dx) (hermite R n)` -/
@[simp]
theorem hermite_succ (n : ℕ) :
    hermite R (n + 1) = X * hermite R n - derivative (hermite R n) := by
  rw [hermite]

theorem hermite_eq_iterate (n : ℕ) :
    hermite R n = (fun p : Polynomial R => X * p - derivative p)^[n] 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ← ih, hermite_succ]

@[simp]
theorem hermite_zero : hermite R 0 = C 1 :=
  rfl

theorem hermite_one : hermite R 1 = X := by
  rw [hermite_succ, hermite_zero]
  simp only [map_one, mul_one, derivative_one, sub_zero]

/-! ### Base change -/

section coeff

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

/-- The Hermite polynomials commute with base change. -/
@[simp]
theorem map_hermite (n : ℕ) : map f (hermite R n) = hermite S n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hermite_succ, hermite_succ, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X,
       ←derivative_map,ih]

/-- `hermite R n` is the base change of the integral Hermite polynomial
along `Int.castRingHom R`. -/
theorem hermite_eq_map_int (R : Type*) [CommRing R] (n : ℕ) :
    hermite R n = map (Int.castRingHom R) (hermite ℤ n) :=
  (map_hermite _ n).symm

/-! ### Lemmas about `Polynomial.coeff` -/

variable (R : Type*) [CommRing R]

theorem coeff_hermite_succ_zero (n : ℕ) :
    coeff (hermite R (n + 1)) 0 = -coeff (hermite R n) 1 := by
  simp [coeff_derivative]

theorem coeff_hermite_succ_succ (n k : ℕ) : coeff (hermite R (n + 1)) (k + 1) =
    coeff (hermite R n) k - (k + 2) * coeff (hermite R n) (k + 2) := by
  rw [hermite_succ, coeff_sub, coeff_X_mul, coeff_derivative, mul_comm]
  push_cast
  ring

theorem coeff_hermite_of_lt {n k : ℕ} (hnk : n < k) : coeff (hermite R n) k = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hnk
  clear hnk
  induction n generalizing k with
  | zero => exact coeff_C
  | succ n ih =>
    have : n + k + 1 + 2 = n + (k + 2) + 1 := by ring
    rw [coeff_hermite_succ_succ, add_right_comm, this, ih k, ih (k + 2), mul_zero, sub_zero]

@[simp]
theorem coeff_hermite_self (n : ℕ) : coeff (hermite R n) n = 1 := by
  induction n with
  | zero => exact coeff_C
  | succ n ih =>
    rw [coeff_hermite_succ_succ, ih, coeff_hermite_of_lt, mul_zero, sub_zero]
    simp


@[simp]
theorem degree_hermite (n : ℕ) : (hermite R n).degree = n := by
  rw [degree_eq_of_le_of_coeff_ne_zero]
  · simp_rw [degree_le_iff_coeff_zero, Nat.cast_lt]
    rintro m hnm
    exact coeff_hermite_of_lt R hnm
  · simp [coeff_hermite_self R n]

@[simp]
theorem natDegree_hermite {n : ℕ} : (hermite R n).natDegree = n :=
  natDegree_eq_of_degree_eq_some (degree_hermite R n)

@[simp]
theorem leadingCoeff_hermite (n : ℕ) : (hermite R n).leadingCoeff = 1 := by
  rw [← coeff_natDegree, natDegree_hermite, coeff_hermite_self]

variable (R : Type*) [CommRing R]

theorem hermite_monic (n : ℕ) : (hermite R n).Monic := by
  nontriviality R
  exact leadingCoeff_hermite R n

variable (R : Type*) [CommRing R]

theorem coeff_hermite_of_odd_add {n k : ℕ} (hnk : Odd (n + k)) : coeff (hermite R n) k = 0 := by
  induction n generalizing k with
  | zero =>
    rw [zero_add k] at hnk
    exact coeff_hermite_of_lt R hnk.pos
  | succ n ih =>
    cases k with
    | zero =>
      rw [Nat.succ_add_eq_add_succ] at hnk
      rw [coeff_hermite_succ_zero, ih hnk, neg_zero]
    | succ k =>
      rw [coeff_hermite_succ_succ, ih, ih, mul_zero, sub_zero]
      · rwa [Nat.succ_add_eq_add_succ] at hnk
      · rw [(by rw [Nat.succ_add, Nat.add_succ] : n.succ + k.succ = n + k + 2)] at hnk
        exact (Nat.odd_add.mp hnk).mpr even_two

end coeff

section CoeffExplicit

open scoped Nat

/-- Because of `coeff_hermite_of_odd_add`, every nonzero coefficient is described as follows.
This is stated over `ℤ`; see `coeff_hermite_explicit'` for the version over an arbitrary
commutative ring. -/
theorem coeff_hermite_explicit :
    ∀ n k : ℕ,
      coeff (hermite ℤ (2 * n + k)) k = (-1) ^ n * (2 * n - 1)‼ * Nat.choose (2 * n + k) k
  | 0, _ => by simp
  | n + 1, 0 => by
    convert! coeff_hermite_succ_zero ℤ (2 * n + 1) using 1
    rw [coeff_hermite_explicit n 1, (by grind : 2 * (n + 1) - 1 = 2 * n + 1),
      Nat.doubleFactorial_add_one, Nat.choose_zero_right,
      Nat.choose_one_right, pow_succ]
    push_cast
    ring
  | n + 1, k + 1 => by
    let hermite_explicit : ℕ → ℕ → ℤ := fun n k =>
      (-1) ^ n * (2 * n - 1)‼ * Nat.choose (2 * n + k) k
    have hermite_explicit_recur :
      ∀ n k : ℕ,
        hermite_explicit (n + 1) (k + 1) =
          hermite_explicit (n + 1) k - (k + 2) * hermite_explicit n (k + 2) := by
      intro n k
      simp only [hermite_explicit]
      -- Factor out (-1)'s.
      rw [mul_comm (↑k + _ : ℤ), sub_eq_add_neg]
      nth_rw 3 [neg_eq_neg_one_mul]
      simp only [mul_assoc, ← mul_add, pow_succ']
      congr 2
      -- Factor out double factorials.
      norm_cast
      rw [(by grind : 2 * (n + 1) - 1 = 2 * n + 1),
        Nat.doubleFactorial_add_one, mul_comm (2 * n + 1)]
      simp only [mul_assoc, ← mul_add]
      congr 1
      -- Match up binomial coefficients using `Nat.choose_succ_right_eq`.
      rw [(by ring : 2 * (n + 1) + (k + 1) = 2 * n + 1 + (k + 1) + 1),
        (by ring : 2 * (n + 1) + k = 2 * n + 1 + (k + 1)),
        (by ring : 2 * n + (k + 2) = 2 * n + 1 + (k + 1))]
      rw [Nat.choose, Nat.choose_succ_right_eq (2 * n + 1 + (k + 1)) (k + 1), Nat.add_sub_cancel]
      ring
    change _ = hermite_explicit _ _
    rw [← add_assoc, coeff_hermite_succ_succ, hermite_explicit_recur]
    congr
    · rw [coeff_hermite_explicit (n + 1) k]
    · rw [(by ring : 2 * (n + 1) + k = 2 * n + (k + 2)), coeff_hermite_explicit n (k + 2)]

variable (R : Type*) [CommRing R]

/-- The coefficients of `hermite R n` are the images of the integral coefficients. -/
theorem coeff_hermite_eq_intCast (n k : ℕ) :
    coeff (hermite R n) k = ((coeff (hermite ℤ n) k : ℤ) : R) := by
  rw [hermite_eq_map_int R n, coeff_map]
  rfl

theorem coeff_hermite_explicit' (n k : ℕ) :
    coeff (hermite R (2 * n + k)) k
      = (-1) ^ n * ((2 * n - 1)‼ : R) * Nat.choose (2 * n + k) k := by
  rw [coeff_hermite_eq_intCast, coeff_hermite_explicit]
  push_cast
  ring

-- Hermite R n is an even function for even n and odd for odd n
theorem coeff_hermite_of_even_add {n k : ℕ} (hnk : Even (n + k)) :
    coeff (hermite R n) k = (-1) ^ ((n - k) / 2) * ((n - k - 1)‼ : R) * Nat.choose n k := by
  rcases le_or_gt k n with h_le | h_lt
  · rw [Nat.even_add, ← Nat.even_sub h_le] at hnk
    obtain ⟨m, hm⟩ := hnk
    rw [(by lia : n = 2 * m + k),
      Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (Nat.succ_pos 1), coeff_hermite_explicit']
  · simp [Nat.choose_eq_zero_of_lt h_lt, coeff_hermite_of_lt R h_lt]

theorem coeff_hermite (n k : ℕ) :
    coeff (hermite R n) k =
      if Even (n + k) then (-1 : R) ^ ((n - k) / 2) * ((n - k - 1)‼ : R) * Nat.choose n k
      else 0 := by
  split_ifs with h
  · exact coeff_hermite_of_even_add R h
  · exact coeff_hermite_of_odd_add R (Nat.not_even_iff_odd.1 h)

end CoeffExplicit

end Polynomial
