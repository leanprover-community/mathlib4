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

/-- The partial sum `∑ i ∈ Ico a (a + k), ∏ j ∈ Ico a i, p j / q j` by binary splitting, as
`(P, Q, T)` with `P` and `Q` the products of `p j` and `q j` over `Ico a (a + k)`. The quotient
`T / Q` equals the partial sum once mapped into a field of characteristic zero, provided no `q j`
is zero. The `q j` are natural numbers so that `Q` can serve as the denominator of `ratBall`. -/
@[expose]
def hypergeomPartialSum {R : Type*} [Semiring R] (p : ℕ → R) (q : ℕ → ℕ) (a k : ℕ) :
    R × ℕ × R :=
  match k with
  | 0 => (1, 1, 0)
  | k@(m + 1) =>
    if k ≤ 32 then
      let (Pl, Ql, Tl) := hypergeomPartialSum p q a m
      let b := a + m
      (Pl * p b, Ql * q b, q b * (Tl + Pl))
    else
      let (Pl, Ql, Tl) := hypergeomPartialSum p q a (k / 2)
      let (Pr, Qr, Tr) := hypergeomPartialSum p q (a + k / 2) ((k + 1) / 2)
      (Pl * Pr, Ql * Qr, Qr * Tl + Pl * Tr)

theorem hypergeomPartialSum_spec {R : Type*} [CommSemiring R] (p : ℕ → R) (q : ℕ → ℕ)
    (a k : ℕ) :
    letI X := hypergeomPartialSum p q a k
    X.1 = ∏ i ∈ Ico a (a + k), p i ∧ X.2.1 = ∏ i ∈ Ico a (a + k), q i ∧
    X.2.2 = ∑ i ∈ Ico a (a + k), (∏ j ∈ Ico a i, p j) * ∏ j ∈ Ico i (a + k), (q j : R) := by
  let T (a b : ℕ) : R := ∑ i ∈ Ico a b, (∏ j ∈ Ico a i, p j) * ∏ j ∈ Ico i b, (q j : R)
  have hT {a m b : ℕ} (ham : a ≤ m) (hmb : m ≤ b) :
      T a b = (∏ j ∈ Ico m b, (q j : R)) * T a m + (∏ j ∈ Ico a m, p j) * T m b := by
    simp only [T]
    rw [mul_sum, mul_sum, ← sum_Ico_consecutive _ ham hmb]
    congr 1 <;> refine sum_congr rfl fun i hi ↦ ?_
    · rw [← prod_Ico_consecutive _ (Finset.mem_Ico.mp hi).2.le hmb]
      ring
    · rw [← prod_Ico_consecutive _ ham (Finset.mem_Ico.mp hi).1]
      ring
  change _ ∧ _ ∧ _ = T a (a + k)
  fun_induction hypergeomPartialSum p q a k with
  | case1 a => simp [T]
  | case2 a m _ Pl Ql Tl hl b ih =>
    rw [hl] at ih
    obtain ⟨rfl, rfl, rfl⟩ := ih
    have hab : a ≤ a + m := by lia
    rw [Nat.succ_eq_add_one, ← add_assoc, prod_Ico_succ_top hab, prod_Ico_succ_top hab,
      hT hab (a + m).le_succ]
    simp [T, b, mul_add, mul_comm]
  | case3 a m _ Pl Ql Tl hl Pr Qr Tr hr ihl ihr =>
    have hk : a + (m + 1) / 2 + (m + 1 + 1) / 2 = a + (m + 1) := by lia
    rw [hl] at ihl
    rw [hr, hk] at ihr
    obtain ⟨rfl, rfl, rfl⟩ := ihl
    obtain ⟨rfl, rfl, rfl⟩ := ihr
    have ham : a ≤ a + (m + 1) / 2 := by lia
    have hmb : a + (m + 1) / 2 ≤ a + (m + 1) := by lia
    simp only [prod_Ico_consecutive _ ham hmb, hT ham hmb, Nat.cast_prod, and_self]

/-- `hypergeomPartialSum` sums a series whose term ratios are `t (j + 1) / t j = p j / q j`. -/
theorem hypergeomPartialSum_div {R K : Type*} [CommSemiring R] [Semifield K] [CharZero K]
    (f : R →+* K) (p : ℕ → R) (q : ℕ → ℕ) (hq : ∀ j, q j ≠ 0) (t : ℕ → K)
    (ht : ∀ j, t (j + 1) = t j * (f (p j) / q j)) (n : ℕ) :
    t 0 * f (hypergeomPartialSum p q 0 n).2.2 / (hypergeomPartialSum p q 0 n).2.1 =
      ∑ m ∈ range n, t m := by
  have key (m : ℕ) : t 0 * ∏ j ∈ range m, f (p j) / q j = t m := by
    induction m with
    | zero => simp
    | succ m ih => rw [prod_range_succ, ← mul_assoc, ih, ht]
  obtain ⟨-, hQ, hT⟩ := hypergeomPartialSum_spec p q 0 n
  simp only [hQ, hT, map_sum, map_mul, map_prod, map_natCast, Nat.cast_prod, mul_sum, sum_div,
    zero_add, Nat.Ico_zero_eq_range]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [mul_div_assoc, ← prod_range_mul_prod_Ico (fun j ↦ (q j : K)) (mem_range.mp hi).le,
    mul_div_mul_right _ _ (prod_ne_zero_iff.mpr fun j _ ↦ Nat.cast_ne_zero.mpr (hq j)),
    ← prod_div_distrib, key]

end Inclusion.IntervalDyadicReal
