/-
Copyright (c) 2024 Jineon Baek and Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek, Seewoo Lee
-/
import Mathlib.RingTheory.Polynomial.Radical

/-!
# Mason-Stothers theorem

This file states and proves the Mason-Stothers theorem, which is a polynomial version of the
ABC conjecture. For (pairwise) coprime polynomials `a, b, c` (over a field) with `a + b + c = 0`,
we have `max {deg(a), deg(b), deg(c)} + 1 ≤ deg(rad(abc))` or `a' = b' = c' = 0`.

Proof is based on this online note by Franz Lemmermeyer http://www.fen.bilkent.edu.tr/~franz/ag05/ag-02.pdf,
which is essentially based on Noah Snyder's paper "An Alternative Proof of Mason's Theorem",
but slightly different.

-/

open Polynomial UniqueFactorizationMonoid UniqueFactorizationDomain EuclideanDomain

variable {k : Type*} [Field k] [DecidableEq k]

-- we use this three times; the assumptions are symmetric in a, b, c.
private theorem abc_subcall {a b c w : k[X]} {hw : w ≠ 0} (wab : w = wronskian a b) (ha : a ≠ 0)
    (hb : b ≠ 0) (hc : c ≠ 0) (abc_dr_dvd_w : divRadical (a * b * c) ∣ w) :
      c.natDegree + 1 ≤ (radical (a * b * c)).natDegree := by
  have ab_nz := mul_ne_zero ha hb
  have abc_nz := mul_ne_zero ab_nz hc
  -- bound the degree of `divRadical (a * b * c)` using Wronskian `w`
  set abc_dr := divRadical (a * b * c)
  have abc_dr_ndeg_lt : abc_dr.natDegree < a.natDegree + b.natDegree := by
    calc
      abc_dr.natDegree ≤ w.natDegree := Polynomial.natDegree_le_of_dvd abc_dr_dvd_w hw
      _ < a.natDegree + b.natDegree := by rw [wab] at hw ⊢; exact natDegree_wronskian_lt_add hw
  -- add the degree of `radical (a * b * c)` to both sides and rearrange
  set abc_r := radical (a * b * c)
  apply Nat.lt_of_add_lt_add_left
  calc
    a.natDegree + b.natDegree + c.natDegree = (a * b * c).natDegree := by
      rw [Polynomial.natDegree_mul ab_nz hc, Polynomial.natDegree_mul ha hb]
    _ = ((divRadical (a * b * c)) * (radical (a * b * c))).natDegree := by
      rw [mul_comm _ (radical _), radical_mul_divRadical]
    _ = abc_dr.natDegree + abc_r.natDegree := by
      rw [← Polynomial.natDegree_mul (divRadical_ne_zero abc_nz) radical_ne_zero]
    _ < a.natDegree + b.natDegree + abc_r.natDegree := by
      exact Nat.add_lt_add_right abc_dr_ndeg_lt _

/-- **Polynomial ABC theorem.** -/
protected theorem Polynomial.abc
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) (hsum : a + b + c = 0) :
    ( natDegree a + 1 ≤ (radical (a * b * c)).natDegree ∧
      natDegree b + 1 ≤ (radical (a * b * c)).natDegree ∧
      natDegree c + 1 ≤ (radical (a * b * c)).natDegree ) ∨
      derivative a = 0 ∧ derivative b = 0 ∧ derivative c = 0 := by
  set w := wronskian a b with wab
  have hbc : IsCoprime b c := by
    rw [add_eq_zero_iff_neg_eq] at hsum
    rw [← hsum, IsCoprime.neg_right_iff]
    convert IsCoprime.add_mul_left_right hab.symm 1
    rw [mul_one]
  have hsum' : b + c + a = 0 := by rwa [add_rotate] at hsum
  have hca : IsCoprime c a := by
    rw [add_eq_zero_iff_neg_eq] at hsum'
    rw [← hsum', IsCoprime.neg_right_iff]
    convert IsCoprime.add_mul_left_right hbc.symm 1
    rw [mul_one]
  have wbc : w = wronskian b c := wronskian_eq_of_sum_zero hsum
  have wca : w = wronskian c a := by
    rw [add_rotate] at hsum
    simpa only [← wbc] using wronskian_eq_of_sum_zero hsum
  -- have `divRadical x` dividing `w` for `x = a, b, c`, and use coprimality
  have abc_dr_dvd_w : divRadical (a * b * c) ∣ w := by
    have adr_dvd_w := divRadical_dvd_wronskian_left a b
    have bdr_dvd_w := divRadical_dvd_wronskian_right a b
    have cdr_dvd_w := divRadical_dvd_wronskian_right b c
    rw [← wab] at adr_dvd_w bdr_dvd_w
    rw [← wbc] at cdr_dvd_w
    rw [divRadical_mul (hca.symm.mul_left hbc), divRadical_mul hab]
    exact (hca.divRadical.symm.mul_left hbc.divRadical).mul_dvd
      (hab.divRadical.mul_dvd adr_dvd_w bdr_dvd_w) cdr_dvd_w
  by_cases hw : w = 0
  · right
    rw [hw] at wab wbc
    obtain ⟨ga, gb⟩ := hab.wronskian_eq_zero_iff.mp wab.symm
    obtain ⟨_, gc⟩ := hbc.wronskian_eq_zero_iff.mp wbc.symm
    exact ⟨ga, gb, gc⟩
  · left
    -- use `abc_subcall` three times, using the symmetry in `a, b, c`
    refine ⟨?_, ?_, ?_⟩
    · rw [mul_rotate] at abc_dr_dvd_w ⊢
      apply abc_subcall wbc <;> assumption
    · rw [← mul_rotate] at abc_dr_dvd_w ⊢
      apply abc_subcall wca <;> assumption
    · apply abc_subcall wab <;> assumption
