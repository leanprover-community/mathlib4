/-
Copyright (c) 2026 metakunt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: metakunt
-/
module

public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.Polynomial.Nilpotent

/-!
# Instance `IsReduced R[X]`
A polynomial `p : R[X]` over a reduced semiring `R` is reduced if `R` is reduced.

The original statement below was for commutative rings; it is generalized here to arbitrary
semirings via Armendariz's theorem (every reduced semiring is Armendariz).
-/

open Polynomial

public section

variable {R : Type*} [Semiring R] [IsReduced R]

/-- In a reduced semiring, annihilation is symmetric. -/
theorem IsReduced.mul_eq_zero_comm {a b : R} (h : a * b = 0) : b * a = 0 := by
  refine IsReduced.eq_zero _ ⟨2, ?_⟩
  have h2 : (b * a) ^ 2 = b * (a * b) * a := by simp [pow_two, mul_assoc]
  rw [h2, h]; simp

/-- A reduced semiring is semicommutative: `a * b = 0` implies `a * r * b = 0` for all `r`. -/
theorem IsReduced.mul_mid_eq_zero {a b : R} (h : a * b = 0) (r : R) : a * r * b = 0 := by
  have hba : b * a = 0 := IsReduced.mul_eq_zero_comm h
  refine IsReduced.eq_zero _ ⟨2, ?_⟩
  have h2 : (a * r * b) ^ 2 = a * r * (b * a) * (r * b) := by simp [pow_two, mul_assoc]
  rw [h2, hba]; simp

/-- In a reduced semiring, `a * b * b = 0` implies `a * b = 0`. -/
theorem IsReduced.mul_eq_zero_of_mul_sq_eq_zero {a b : R} (h : a * b * b = 0) : a * b = 0 := by
  have h2 : b * (a * b) = 0 := IsReduced.mul_eq_zero_comm (a := a * b) (b := b) h
  refine IsReduced.eq_zero _ ⟨2, ?_⟩
  have h3 : (a * b) ^ 2 = a * (b * (a * b)) := by simp [pow_two, mul_assoc]
  rw [h3, h2]; simp

/-- Armendariz's theorem for reduced semirings: if `p * q = 0` in `R[X]` with `R` reduced, then
every coefficient of `p` annihilates every coefficient of `q`. -/
theorem Polynomial.coeff_mul_coeff_eq_zero_of_isReduced (p q : R[X]) (h : p * q = 0) :
    ∀ j i, (coeff p i) * (coeff q j) = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j IHj =>
    intro i
    induction i using Nat.strong_induction_on with
    | _ i IHi =>
      have hc : ∑ x ∈ Finset.antidiagonal (i + j), coeff p x.1 * coeff q x.2 = 0 := by
        rw [← coeff_mul, h, coeff_zero]
      have hmul : ∑ x ∈ Finset.antidiagonal (i + j),
          (coeff p x.1 * coeff q x.2) * coeff q j = 0 := by
        rw [← Finset.sum_mul, hc, zero_mul]
      have hsingle : ∑ x ∈ Finset.antidiagonal (i + j),
          (coeff p x.1 * coeff q x.2) * coeff q j = (coeff p i * coeff q j) * coeff q j := by
        apply Finset.sum_eq_single (i, j)
        · rintro ⟨s, t⟩ hst hne
          grind [Finset.mem_antidiagonal.mp hst, IsReduced.mul_mid_eq_zero]
        · intro hmem
          grind [Finset.mem_antidiagonal]
      grind [IsReduced.mul_eq_zero_of_mul_sq_eq_zero]

public instance Polynomial.instIsReducedOfIsReduced : IsReduced R[X] := by
  have key : ∀ q : R[X], q * q = 0 → q = 0 := by
    intro q hq
    ext i
    have h := Polynomial.coeff_mul_coeff_eq_zero_of_isReduced q q hq i i
    simpa using IsReduced.eq_zero _ ⟨2, by rw [pow_two]; exact h⟩
  constructor
  rintro p ⟨n, hn⟩
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    match n, hn with
    | 0, hn =>
      have h1 : (1 : R[X]) = 0 := by simpa using hn
      calc p = p * 1 := by rw [mul_one]
        _ = 0 := by rw [h1, mul_zero]
    | 1, hn => simpa using hn
    | (n + 2), hn =>
      refine IH (n + 1) (by omega) (key _ ?_)
      have hx : p ^ (n + 1) * p ^ (n + 1) = p ^ (n + 2) * p ^ n := by
        rw [← pow_add, ← pow_add]; ring_nf
      rw [hx, hn, zero_mul]

end
