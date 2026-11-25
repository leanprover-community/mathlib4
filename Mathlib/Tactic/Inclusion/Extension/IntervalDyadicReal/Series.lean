/-
Copyright (c) 2026 Emlis, Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emlis, Rao Xiaojia
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Hom.Defs

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring

/-!
# Partial sums of series with rational term ratios for interval_dyadic_real

This file computes partial sums of series with given term ratios by binary splitting. The
`interval_dyadic_real` extensions evaluate their Taylor series through it.

## Implementation notes

Binary splitting here is the summation technique of Haible and Papanikolaou. It is unrelated to
the `binarySplit` cover, which bisects intervals.

In a normal evaluator, this divide-and-conquer based approach is faster than linear computation
since it reduces the number of computations on larger numerals. However, the performance gain
is limited for kernel checks, since GMP arithmetic is still not the bottleneck even at ~10k bits,
while the binary splitting approach takes more kernel steps than a simple linear recursion.
An optimisation is implemented where blocks of up to 32 terms are evaluated linearly to reduce the
number of kernel steps.

The benefit of this approach is therefore mainly in reducing the recursion depth (`O(log n)`,
compared to `O(n)` for linear computation) rather than performance.

## References

* B. Haible and T. Papanikolaou, *Fast multiprecision evaluation of series of rational numbers*,
  <https://www.ginac.de/CLN/binsplit.pdf>
* R. L. Graham, D. E. Knuth and O. Patashnik, *Concrete Mathematics*, 2nd ed., §5.5
* F. Johansson, *hypgeom.h – support for hypergeometric series*, Arb documentation,
  <https://arblib.org/hypgeom.html>
-/

public section

open Finset

namespace Inclusion.IntervalDyadicReal

/-- The sum of a block of consecutive terms of a series with term ratios `p j / q j` and first
term `1`, and the term following the block, as fractions over the common denominator `den`. -/
structure HypergeomSum (R : Type*) where
  /-- The product of the `p j` over the block, so that `termNum / den` is the term following the
  block. -/
  termNum : R
  /-- The product of the `q j` over the block. It is a natural number so that it can serve as the
  denominator of `ratBall`. -/
  den : ℕ
  /-- The numerator of the sum of the block over `den`. -/
  sumNum : R

/-- The sum of the first `k` terms of the series starting with `1` where each later term is
the previous one multiplied by `p j / q j` for `j ∈ [a, a + k - 1)`, computed by binary splitting.
If no `q j` is zero, `sumNum / den` is the sum (`hypergeomPartialSum_div` states this precisely).
The recursion needs `termNum` to append a term or to join two blocks of terms, since every term
of the later block is scaled by `termNum / den`. -/
@[expose]
def hypergeomPartialSum {R : Type*} [Semiring R] (p : ℕ → R) (q : ℕ → ℕ) (a k : ℕ) :
    HypergeomSum R :=
  if k ≤ 32 then
    match k with
    | 0 => ⟨1, 1, 0⟩
    | m + 1 =>
      let X := hypergeomPartialSum p q a m
      let b := a + m
      ⟨X.termNum * p b, X.den * q b, q b * (X.sumNum + X.termNum)⟩
  else
    let X := hypergeomPartialSum p q a (k / 2)
    let Y := hypergeomPartialSum p q (a + k / 2) ((k + 1) / 2)
    ⟨X.termNum * Y.termNum, X.den * Y.den, Y.den * X.sumNum + X.termNum * Y.sumNum⟩

theorem hypergeomPartialSum_spec {R : Type*} [CommSemiring R] (p : ℕ → R) (q : ℕ → ℕ)
    (a k : ℕ) :
    letI X := hypergeomPartialSum p q a k
    X.termNum = ∏ i ∈ Ico a (a + k), p i ∧ X.den = ∏ i ∈ Ico a (a + k), q i ∧
    X.sumNum = ∑ i ∈ Ico a (a + k), (∏ j ∈ Ico a i, p j) * ∏ j ∈ Ico i (a + k), (q j : R) := by
  let S (a b : ℕ) : R := ∑ i ∈ Ico a b, (∏ j ∈ Ico a i, p j) * ∏ j ∈ Ico i b, (q j : R)
  have hS {a m b : ℕ} (ham : a ≤ m) (hmb : m ≤ b) :
      S a b = (∏ j ∈ Ico m b, (q j : R)) * S a m + (∏ j ∈ Ico a m, p j) * S m b := by
    simp only [S]
    rw [mul_sum, mul_sum, ← sum_Ico_consecutive _ ham hmb]
    congr 1 <;> refine sum_congr rfl fun i hi ↦ ?_
    · rw [← prod_Ico_consecutive _ (Finset.mem_Ico.mp hi).2.le hmb]
      ring
    · rw [← prod_Ico_consecutive _ ham (Finset.mem_Ico.mp hi).1]
      ring
  change _ ∧ _ ∧ _ = S a (a + k)
  fun_induction hypergeomPartialSum p q a k with
  | case1 a => simp [S]
  | case2 a m X b _ ih =>
    have hab : a ≤ a + m := by lia
    rw [Nat.succ_eq_add_one, ← add_assoc, prod_Ico_succ_top hab, prod_Ico_succ_top hab,
      hS hab (a + m).le_succ]
    simp [X, b, ih, S, mul_add, mul_comm]
  | case3 a k _ X Y ihl ihr =>
    have hk : a + k / 2 + (k + 1) / 2 = a + k := by lia
    rw [hk] at ihr
    have ham : a ≤ a + k / 2 := by lia
    have hmb : a + k / 2 ≤ a + k := by lia
    simp only [X, Y, ihl, ihr, prod_Ico_consecutive _ ham hmb, hS ham hmb, Nat.cast_prod, and_self]

/-- `hypergeomPartialSum` sums a series whose term ratios are `t (j + 1) / t j = p j / q j`. -/
theorem hypergeomPartialSum_div {R K : Type*} [CommSemiring R] [Semifield K] [CharZero K]
    (f : R →+* K) (p : ℕ → R) (q : ℕ → ℕ) (hq : ∀ j, q j ≠ 0) (t : ℕ → K)
    (ht : ∀ j, t (j + 1) = t j * (f (p j) / q j)) (n : ℕ) :
    t 0 * f (hypergeomPartialSum p q 0 n).sumNum / (hypergeomPartialSum p q 0 n).den =
      ∑ m ∈ range n, t m := by
  have key (m : ℕ) : t 0 * ∏ j ∈ range m, f (p j) / q j = t m := by
    induction m with
    | zero => simp
    | succ m ih => rw [prod_range_succ, ← mul_assoc, ih, ht]
  obtain ⟨-, hden, hsum⟩ := hypergeomPartialSum_spec p q 0 n
  simp only [hden, hsum, map_sum, map_mul, map_prod, map_natCast, Nat.cast_prod, mul_sum, sum_div,
    zero_add, Nat.Ico_zero_eq_range]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [mul_div_assoc, ← prod_range_mul_prod_Ico (fun j ↦ (q j : K)) (mem_range.mp hi).le,
    mul_div_mul_right _ _ (prod_ne_zero_iff.mpr fun j _ ↦ Nat.cast_ne_zero.mpr (hq j)),
    ← prod_div_distrib, key]

end Inclusion.IntervalDyadicReal
