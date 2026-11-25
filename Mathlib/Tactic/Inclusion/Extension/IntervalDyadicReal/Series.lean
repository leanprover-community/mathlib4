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
`T / Q` equals the partial sum once mapped into a field. -/
@[expose]
def hypergeomPartialSum {R : Type*} [CommSemiring R] (p : ℕ → R) (q : ℕ → ℕ) (a k : ℕ) :
    R × ℕ × R :=
  match k with
  | 0 => (1, 1, 0)
  | 1 => (p a, q a, q a)
  | k + 2 =>
    -- Blocks of up to 32 terms are summed term by term, which the kernel evaluates faster.
    if k < 31 then
      let (Pl, Ql, Tl) := hypergeomPartialSum p q a (k + 1)
      let b := a + (k + 1)
      (Pl * p b, Ql * q b, q b * (Tl + Pl))
    else
      let (Pl, Ql, Tl) := hypergeomPartialSum p q a ((k + 2) / 2)
      let (Pr, Qr, Tr) := hypergeomPartialSum p q (a + (k + 2) / 2) ((k + 3) / 2)
      (Pl * Pr, Ql * Qr, Qr * Tl + Pl * Tr)

theorem hypergeomPartialSum_spec {R : Type*} [CommSemiring R] (p : ℕ → R) (q : ℕ → ℕ)
    (a k : ℕ) :
    letI X := hypergeomPartialSum p q a k
    X.1 = ∏ i ∈ Ico a (a + k), p i ∧ X.2.1 = ∏ i ∈ Ico a (a + k), q i ∧
    X.2.2 = ∑ i ∈ Ico a (a + k), (∏ j ∈ Ico a i, p j) * ∏ j ∈ Ico i (a + k), (q j : R) := by
  fun_induction hypergeomPartialSum p q a k with
  | case1 a => simp
  | case2 a => simp
  | case3 a k hk Pl Ql Tl hl b ih =>
    rw [hl] at ih
    obtain ⟨rfl, rfl, rfl⟩ := ih
    dsimp only [b]
    have hk2 : a + (k + 2) = a + (k + 1) + 1 := by lia
    have hab : a ≤ a + (k + 1) := by lia
    rw [hk2, prod_Ico_succ_top hab, prod_Ico_succ_top hab, sum_Ico_succ_top hab, mul_add,
      mul_sum, Nat.Ico_succ_singleton, prod_singleton]
    refine ⟨rfl, rfl, ?_⟩
    congr 1
    · refine sum_congr rfl fun i hi ↦ ?_
      rw [prod_Ico_succ_top (Finset.mem_Ico.mp hi).2.le]
      ring
    · ring
  | case4 a k hk Pl Ql Tl hl Pr Qr Tr hr ihl ihr =>
    have hk : a + (k + 2) / 2 + (k + 3) / 2 = a + (k + 2) := by lia
    rw [hl] at ihl
    rw [hr, hk] at ihr
    obtain ⟨rfl, rfl, rfl⟩ := ihl
    obtain ⟨rfl, rfl, rfl⟩ := ihr
    dsimp only
    have ham : a ≤ a + (k + 2) / 2 := by lia
    have hmb : a + (k + 2) / 2 ≤ a + (k + 2) := by lia
    refine ⟨prod_Ico_consecutive _ ham hmb, prod_Ico_consecutive _ ham hmb, ?_⟩
    rw [Nat.cast_prod, mul_sum, mul_sum, ← sum_Ico_consecutive _ ham hmb]
    congr 1 <;> refine sum_congr rfl fun i hi ↦ ?_
    · rw [← prod_Ico_consecutive _ (Finset.mem_Ico.mp hi).2.le hmb]
      ring
    · rw [← prod_Ico_consecutive _ ham (Finset.mem_Ico.mp hi).1]
      ring

/-- `hypergeomPartialSum` sums a series whose term ratios are `t (j + 1) / t j = p j / q j`. -/
theorem hypergeomPartialSum_div {R K : Type*} [CommSemiring R] [Field K] [CharZero K]
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
