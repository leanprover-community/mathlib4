/-
Copyright (c) 2026 Emlis, Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emlis, Rao Xiaojia
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Hom.Defs

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Field

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
number of kernel steps. The block size is empirical: a smaller block does less arithmetic on
large numbers and takes more kernel steps, and therefore would be better for higher precision or
faster kernel. A larger block size is faster for the other case (lower precision, slower kernel).

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

When `p` and `q` are polynomials in `j`, this is a hypergeometric series in the sense of Graham,
Knuth and Patashnik: factoring `p` and `q` into linear factors `j + c`, the products of the `p j`
and of the `q j` become, up to constant factors, products of Pochhammer symbols, as in the usual
`ₚF_q` form. Nothing here requires `p` and `q` to be polynomials, but binary splitting is only
efficient when the factors `p j` and `q j` stay small, as they do for polynomials.

If no `q j` is zero, `sumNum / den` is the sum (`hypergeomPartialSum_spec` states this precisely).
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

theorem hypergeomPartialSum_den_ne_zero {R : Type*} [Semiring R] (p : ℕ → R) {q : ℕ → ℕ}
    (hq : ∀ j, q j ≠ 0) (a k : ℕ) : (hypergeomPartialSum p q a k).den ≠ 0 := by
  fun_induction hypergeomPartialSum p q a k with simp_all +zetaDelta

/-- `hypergeomPartialSum` sums a series whose term ratios are
`t (j + 1) / t j = p (a + j) / q (a + j)`. -/
theorem hypergeomPartialSum_spec {R K : Type*} [Semiring R] [Semifield K] [CharZero K]
    (f : R →+* K) (p : ℕ → R) (q : ℕ → ℕ) (hq : ∀ j, q j ≠ 0) (a : ℕ) (t : ℕ → K)
    (ht : ∀ j, t (j + 1) = t j * (f (p (a + j)) / q (a + j))) (k : ℕ) :
    letI X := hypergeomPartialSum p q a k
    t 0 * f X.termNum / X.den = t k ∧ t 0 * f X.sumNum / X.den = ∑ m ∈ range k, t m := by
  fun_induction hypergeomPartialSum p q a k generalizing t with
  | case1 => simp
  | case2 a m X b _ ih =>
    obtain ⟨hXt, hXs⟩ := ih t ht
    have hb : (q b : K) ≠ 0 := mod_cast hq b
    rw [sum_range_succ, ht, ← hXt, ← hXs]
    push_cast [map_mul, map_add, map_natCast]
    constructor <;> field
  | case3 a k _ X Y ihl ihr =>
    obtain ⟨hXt, hXs⟩ := ihl t ht
    obtain ⟨hYt, hYs⟩ := ihr (fun j ↦ t (k / 2 + j)) fun j ↦ by rw [← add_assoc, ht, add_assoc]
    have hY : (Y.den : K) ≠ 0 := mod_cast hypergeomPartialSum_den_ne_zero p hq _ _
    have hk : k / 2 + (k + 1) / 2 = k := by lia
    rw [← hk, sum_range_add, ← hXs, ← hYs, ← hYt, add_zero, ← hXt]
    push_cast [map_mul, map_add, map_natCast]
    constructor <;> field

end Inclusion.IntervalDyadicReal
