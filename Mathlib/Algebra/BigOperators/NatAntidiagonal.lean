/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Basic

#align_import algebra.big_operators.nat_antidiagonal from "leanprover-community/mathlib"@"008205aa645b3f194c1da47025c5f110c8406eab"

/-!
# Big operators for `NatAntidiagonal`

This file contains theorems relevant to big operators over `Finset.NatAntidiagonal`.
-/

open BigOperators

variable {M N : Type*} [CommMonoid M] [AddCommMonoid N]

namespace Finset

namespace Nat

theorem prod_antidiagonal_succ {n : ℕ} {f : ℕ × ℕ → M} :
    (∏ p in antidiagonal (n + 1), f p) = f (0, n + 1) * ∏ p in antidiagonal n, f (p.1 + 1, p.2) :=
  by rw [antidiagonal_succ, prod_cons, prod_map]; rfl
#align finset.nat.prod_antidiagonal_succ Finset.Nat.prod_antidiagonal_succ

theorem sum_antidiagonal_succ {n : ℕ} {f : ℕ × ℕ → N} :
    (∑ p in antidiagonal (n + 1), f p) = f (0, n + 1) + ∑ p in antidiagonal n, f (p.1 + 1, p.2) :=
  @prod_antidiagonal_succ (Multiplicative N) _ _ _
#align finset.nat.sum_antidiagonal_succ Finset.Nat.sum_antidiagonal_succ

@[to_additive]
theorem prod_antidiagonal_swap {n : ℕ} {f : ℕ × ℕ → M} :
    ∏ p in antidiagonal n, f p.swap = ∏ p in antidiagonal n, f p := by
  conv_lhs => rw [← map_swap_antidiagonal, Finset.prod_map]
#align finset.nat.prod_antidiagonal_swap Finset.Nat.prod_antidiagonal_swap
#align finset.nat.sum_antidiagonal_swap Finset.Nat.sum_antidiagonal_swap

theorem prod_antidiagonal_succ' {n : ℕ} {f : ℕ × ℕ → M} : (∏ p in antidiagonal (n + 1), f p) =
    f (n + 1, 0) * ∏ p in antidiagonal n, f (p.1, p.2 + 1) := by
  rw [← prod_antidiagonal_swap, prod_antidiagonal_succ, ← prod_antidiagonal_swap]
  rfl
#align finset.nat.prod_antidiagonal_succ' Finset.Nat.prod_antidiagonal_succ'

theorem sum_antidiagonal_succ' {n : ℕ} {f : ℕ × ℕ → N} :
    (∑ p in antidiagonal (n + 1), f p) = f (n + 1, 0) + ∑ p in antidiagonal n, f (p.1, p.2 + 1) :=
  @prod_antidiagonal_succ' (Multiplicative N) _ _ _
#align finset.nat.sum_antidiagonal_succ' Finset.Nat.sum_antidiagonal_succ'

@[to_additive]
theorem prod_antidiagonal_subst {n : ℕ} {f : ℕ × ℕ → ℕ → M} :
    ∏ p in antidiagonal n, f p n = ∏ p in antidiagonal n, f p (p.1 + p.2) :=
  prod_congr rfl fun p hp ↦ by rw [Nat.mem_antidiagonal.1 hp]
#align finset.nat.prod_antidiagonal_subst Finset.Nat.prod_antidiagonal_subst
#align finset.nat.sum_antidiagonal_subst Finset.Nat.sum_antidiagonal_subst

@[to_additive]
theorem prod_antidiagonal_eq_prod_range_succ_mk {M : Type*} [CommMonoid M] (f : ℕ × ℕ → M)
    (n : ℕ) : ∏ ij in Finset.Nat.antidiagonal n, f ij = ∏ k in range n.succ, f (k, n - k) :=
  Finset.prod_map (range n.succ) ⟨fun i ↦ (i, n - i), fun _ _ h ↦ (Prod.mk.inj h).1⟩ f
#align finset.nat.prod_antidiagonal_eq_prod_range_succ_mk Finset.Nat.prod_antidiagonal_eq_prod_range_succ_mk
#align finset.nat.sum_antidiagonal_eq_sum_range_succ_mk Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk

/-- This lemma matches more generally than `Finset.Nat.prod_antidiagonal_eq_prod_range_succ_mk` when
using `rw ←`. -/
@[to_additive "This lemma matches more generally than
`Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk` when using `rw ←`."]
theorem prod_antidiagonal_eq_prod_range_succ {M : Type*} [CommMonoid M] (f : ℕ → ℕ → M) (n : ℕ) :
    ∏ ij in Finset.Nat.antidiagonal n, f ij.1 ij.2 = ∏ k in range n.succ, f k (n - k) :=
  prod_antidiagonal_eq_prod_range_succ_mk _ _
#align finset.nat.prod_antidiagonal_eq_prod_range_succ Finset.Nat.prod_antidiagonal_eq_prod_range_succ
#align finset.nat.sum_antidiagonal_eq_sum_range_succ Finset.Nat.sum_antidiagonal_eq_sum_range_succ
end Nat

end Finset
