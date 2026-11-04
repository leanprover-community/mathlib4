/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Degree and support of univariate polynomials

## Main results
* `Polynomial.as_sum_support`: write `p : R[X]` as a sum over its support
* `Polynomial.as_sum_range`: write `p : R[X]` as a sum over `{0, ..., natDegree p}`
* `Polynomial.natDegree_mem_support_of_ne_zero`: `natDegree p ∈ support p` if `p ≠ 0`
-/

public section

open AddMonoidAlgebra Finsupp Finset Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a c : R} {n m : ℕ}

section Semiring

variable [Semiring R] {p : R[X]}

theorem supDegree_eq_natDegree (p : R[X]) : p.supDegree id = p.natDegree := by
  obtain rfl | h := eq_or_ne p 0
  · simp
  apply WithBot.coe_injective
  rw [← AddMonoidAlgebra.supDegree_withBot_some_comp, Function.comp_id, supDegree_eq_degree,
    degree_eq_natDegree h, Nat.cast_withBot]
  change p.support.Nonempty
  rwa [nonempty_iff_ne_empty, Ne, support_eq_empty]

theorem le_natDegree_of_mem_supp (a : ℕ) : a ∈ p.support → a ≤ natDegree p :=
  le_natDegree_of_ne_zero ∘ mem_support_iff.mp

theorem supp_subset_range (h : degree p < m) : p.support ⊆ Finset.range m := fun _n hn =>
  mem_range.2 <| mod_cast (le_degree_of_ne_zero (mem_support_iff.1 hn)).trans_lt h

theorem supp_subset_range_natDegree_succ : p.support ⊆ Finset.range (natDegree p + 1) :=
  supp_subset_range (degree_le_natDegree.trans_lt (mod_cast Nat.lt_succ_self _))

theorem as_sum_support (p : R[X]) : p = ∑ i ∈ p.support, monomial i (p.coeff i) :=
  p.sum_coeff_monomial.symm

theorem as_sum_support_C_mul_X_pow (p : R[X]) : p = ∑ i ∈ p.support, C (p.coeff i) * X ^ i :=
  _root_.trans p.as_sum_support <| by simp only [C_mul_X_pow_eq_monomial]

/-- We can reexpress a sum over `p.support` as a sum over `range n`,
for any `n` satisfying `p.degree < n`. -/
theorem sum_coeff_eq_sum_range [AddCommMonoid S] (p : R[X]) {f : ℕ → R → S} (h : ∀ n, f n 0 = 0)
    (n : ℕ) (hn : p.degree < n) : p.coeff.sum f = ∑ a ∈ range n, f a (coeff p a) :=
  Finsupp.sum_of_support_subset _ (supp_subset_range hn) _ fun n _hn => h n

@[deprecated (since := "2026-11-02")] alias sum_over_range' := sum_coeff_eq_sum_range

/-- We can reexpress a sum over `p.support` as a sum over `range (p.natDegree + 1)`. -/
theorem sum_coeff_eq_sum_range_natDegree [AddCommMonoid S] (p : R[X]) {f : ℕ → R → S}
    (h : ∀ n, f n 0 = 0) : p.coeff.sum f = ∑ a ∈ range (p.natDegree + 1), f a (coeff p a) :=
  sum_coeff_eq_sum_range p h (p.natDegree + 1)
    (degree_le_natDegree.trans_lt (mod_cast lt_add_one _))

@[deprecated (since := "2026-11-02")] alias sum_over_range := sum_coeff_eq_sum_range_natDegree

@[deprecated sum_coeff_eq_sum_range_natDegree +typeChanged (since := "2026-11-02")]
theorem sum_fin [AddCommMonoid S] (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0) {n : ℕ} {p : R[X]}
    (hn : p.degree < n) : (∑ i : Fin n, f i (p.coeff i)) = p.coeff.sum f := by
  rw [sum_coeff_eq_sum_range _ hf n hn, Fin.sum_univ_eq_sum_range fun i => f i (p.coeff i)]

theorem as_sum_range' (p : R[X]) (n : ℕ) (hn : p.degree < n) :
    p = ∑ i ∈ range n, monomial i (coeff p i) :=
  p.sum_coeff_monomial.symm.trans <| p.sum_coeff_eq_sum_range monomial_zero_right _ hn

theorem as_sum_range (p : R[X]) : p = ∑ i ∈ range (p.natDegree + 1), monomial i (coeff p i) :=
  p.as_sum_range' _ (degree_le_natDegree.trans_lt (mod_cast lt_add_one _))

theorem as_sum_range_C_mul_X_pow' (p : R[X]) {n : ℕ} (hn : p.natDegree < n) :
    p = ∑ i ∈ range n, C (coeff p i) * X ^ i :=
  (p.as_sum_range' _ (degree_le_natDegree.trans_lt (mod_cast hn))).trans <| by
    simp only [C_mul_X_pow_eq_monomial]

theorem as_sum_range_C_mul_X_pow (p : R[X]) :
    p = ∑ i ∈ range (p.natDegree + 1), C (coeff p i) * X ^ i :=
  p.as_sum_range_C_mul_X_pow' (lt_add_one _)

theorem mem_support_C_mul_X_pow {n a : ℕ} {c : R} (h : a ∈ support (C c * X ^ n)) : a = n :=
  mem_singleton.1 <| support_C_mul_X_pow_subset n c h

theorem card_support_C_mul_X_pow_le_one {c : R} {n : ℕ} : #(support (C c * X ^ n)) ≤ 1 := by
  rw [← card_singleton n]
  apply card_le_card (support_C_mul_X_pow_subset n c)

theorem card_supp_le_succ_natDegree (p : R[X]) : #p.support ≤ p.natDegree + 1 := by
  rw [← Finset.card_range (p.natDegree + 1)]
  exact Finset.card_le_card supp_subset_range_natDegree_succ

theorem le_degree_of_mem_supp (a : ℕ) : a ∈ p.support → ↑a ≤ degree p :=
  le_degree_of_ne_zero ∘ mem_support_iff.mp

theorem nonempty_support_iff : p.support.Nonempty ↔ p ≠ 0 := by
  rw [Ne, nonempty_iff_ne_empty, Ne, ← support_eq_empty]

end Semiring

section Semiring

variable [Semiring R] {p : R[X]}

theorem natDegree_mem_support_of_ne_zero (H : p ≠ 0) : p.natDegree ∈ p.support := by
  rw [mem_support_iff]
  exact (not_congr leadingCoeff_eq_zero).mpr H

@[deprecated (since := "2026-10-13")]
alias natDegree_mem_support_of_nonzero := natDegree_mem_support_of_ne_zero

theorem natDegree_eq_support_max' (h : p ≠ 0) :
    p.natDegree = p.support.max' (nonempty_support_iff.mpr h) :=
  (le_max' _ _ <| natDegree_mem_support_of_ne_zero h).antisymm <|
    max'_le _ _ _ le_natDegree_of_mem_supp

end Semiring

end Polynomial
