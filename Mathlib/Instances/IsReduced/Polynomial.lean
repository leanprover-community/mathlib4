/-
Copyright (c) 2026 metakunt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: metakunt
-/
module

public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Instance `IsReduced R[X]`
If `R` is reduced, so is `R[X].
-/

open Polynomial

variable {R : Type*} [Semiring R] [IsReduced R]

-- TODO: Private section for now. Find a new home for those theorems if necessary.
section

namespace IsReduced

/-- In a reduced semiring, annihilation is symmetric. -/
theorem mul_eq_zero_comm {a b : R} (h : a * b = 0) : b * a = 0 := by
  refine IsReduced.eq_zero _ ⟨2, ?_⟩
  grind => have : (b * a) ^ 2 = b * (a * b) * a

/-- A reduced semiring is semicommutative: `a * b = 0` implies `a * r * b = 0` for all `r`. -/
theorem mul_mid_eq_zero {a b : R} (h : a * b = 0) (r : R) : a * r * b = 0 := by
  have hba : b * a = 0 := IsReduced.mul_eq_zero_comm h
  refine IsReduced.eq_zero _ ⟨2, ?_⟩
  have h2 : (a * r * b) ^ 2 = a * r * (b * a) * (r * b) := by simp [pow_two, mul_assoc]
  simp [h2, hba]

/-- In a reduced semiring, `a * b * b = 0` implies `a * b = 0`. -/
theorem mul_eq_zero_of_mul_sq_eq_zero {a b : R} (h : a * b * b = 0) : a * b = 0 := by
  have h2 : b * (a * b) = 0 := IsReduced.mul_eq_zero_comm (a := a * b) (b := b) h
  refine IsReduced.eq_zero _ ⟨2, ?_⟩
  simp [pow_two, mul_assoc, h2]

end IsReduced

end

public section

namespace Polynomial

/-- Armendariz's theorem for reduced semirings: if `p * q = 0` in `R[X]` with `R` reduced, then
every coefficient of `p` annihilates every coefficient of `q`. -/
theorem coeff_mul_coeff_eq_zero_of_isReduced (p q : R[X]) (h : p * q = 0) :
    ∀ j i, (coeff p i) * (coeff q j) = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j IHj =>
    intro i
    induction i using Nat.strong_induction_on with
    | _ i IHi =>
      have : ∑ x ∈ Finset.antidiagonal (i + j), (coeff p x.1 * coeff q x.2) * coeff q j = 0 := by
        rw [← Finset.sum_mul, ← coeff_mul, h, coeff_zero, zero_mul]
      have : ∑ x ∈ Finset.antidiagonal (i + j),
          (coeff p x.1 * coeff q x.2) * coeff q j = (coeff p i * coeff q j) * coeff q j := by
        apply Finset.sum_eq_single (i, j)
        · rintro ⟨s, t⟩ hst hne
          grind [Finset.mem_antidiagonal.mp hst, IsReduced.mul_mid_eq_zero]
        · intro hmem
          grind [Finset.mem_antidiagonal]
      grind [IsReduced.mul_eq_zero_of_mul_sq_eq_zero]

instance : IsReduced R[X] := by
  have key : ∀ q : R[X], q * q = 0 → q = 0 := by
    intro q hq
    ext i
    have h := q.coeff_mul_coeff_eq_zero_of_isReduced q hq i i
    simpa using IsReduced.eq_zero _ ⟨2, by rw [pow_two]; exact h⟩
  constructor
  rintro p ⟨n, hn⟩
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    match n, hn with
    | 0, hn =>
      have : (1 : R[X]) = 0 := by simpa using hn
      rw [← mul_one p, this, mul_zero]
    | 1, hn => simpa using hn
    | (n + 2), hn =>
      refine IH (n + 1) (by lia) (key _ ?_)
      have : p ^ (n + 1) * p ^ (n + 1) = p ^ (n + 2) * p ^ n := by
        rw [← pow_add, ← pow_add]
        lia
      lia

end Polynomial

end
