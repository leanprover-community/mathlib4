/-
Copyright (c) 2024 Jineon Back and Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek, Seewoo Lee
-/
import Init.Data.Nat.Lemmas
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.EuclideanDomain.Defs
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Ring.Regular
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.RingTheory.Radical
import Mathlib.RingTheory.UniqueFactorizationDomain
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Mason-Stothers theorem

This file states and proves Mason-Stothers theorem, which is a polynomial version of ABC conjecture.
For a (pairwise) coprime polynomials `a, b, c` (over a field) with `a + b + c = 0`, we have
`max {deg(a), deg(b), deg(c)} + 1 ≤ deg(rad(abc))` or `a' = b' = c' = 0`.

Proof is based on this online note by Franz Lemmermeyer http://www.fen.bilkent.edu.tr/~franz/ag05/ag-02.pdf,
which is essentially based on Noah Snyder's paper "An Alternative Proof of Mason's Theorem", but slightly different.

## TODO
Prove polynomial FLT using Mason-Stothers theorem.
-/

noncomputable section

open scoped Polynomial Classical

open Polynomial UniqueFactorizationMonoid

variable {k : Type*} [Field k]


/-- Auxiliary theorems for `max₃ a b c = max (max a b) c`. -/
def max₃ (a b c : Nat) : Nat :=
  max (max a b) c

theorem max₃_mul_distrib_left (a b c d : Nat) : a * max₃ b c d = max₃ (a * b) (a * c) (a * d) := by
  rw [max₃, max₃, Nat.mul_max_mul_left, Nat.mul_max_mul_left]

theorem max₃_add_distrib_right (a b c d : Nat) : max₃ a b c + d = max₃ (a + d) (b + d) (c + d) := by
  rw [max₃, max₃, Nat.add_max_add_right, Nat.add_max_add_right]

theorem le_max₃_left (a b c : Nat) : a ≤ max₃ a b c :=
  Nat.le_trans (Nat.le_max_left a b) (Nat.le_max_left _ _)

theorem le_max₃_middle (a b c : Nat) : b ≤ max₃ a b c :=
  Nat.le_trans (Nat.le_max_right a b) (Nat.le_max_left _ _)

theorem le_max₃_right (a b c : Nat) : c ≤ max₃ a b c :=
  Nat.le_max_right _ c

theorem max₃_lt {a b c d : Nat} : max₃ a b c < d ↔ a < d ∧ b < d ∧ c < d := by
  rw [max₃, Nat.max_lt, Nat.max_lt, and_assoc]

theorem max₃_le {a b c d : Nat} : max₃ a b c ≤ d ↔ a ≤ d ∧ b ≤ d ∧ c ≤ d := by
  rw [max₃, Nat.max_le, Nat.max_le, and_assoc]


/-- For a given polynomial `a`, `divRadical a` is `a` divided by its radical `radical a`.-/
def divRadical (a : k[X]) : k[X] := a / (radical a)


theorem hMul_radical_divRadical (a : k[X]) : (radical a) * (divRadical a) = a := by
  rw [divRadical]
  rw [← EuclideanDomain.mul_div_assoc]
  refine' mul_div_cancel_left₀ _ _
  exact radical_ne_zero a
  exact radical_dvd_self a

theorem divRadical_ne_zero {a : k[X]} (ha : a ≠ 0) : divRadical a ≠ 0 := by
  rw [← hMul_radical_divRadical a] at ha
  exact right_ne_zero_of_mul ha

theorem divRadical_isUnit {u : k[X]} (hu : IsUnit u) : IsUnit (divRadical u) := by
  rwa [divRadical, radical_unit_eq_one hu, EuclideanDomain.div_one]

theorem eq_divRadical {a x : k[X]} (h : (radical a) * x = a) : x = divRadical a := by
  apply EuclideanDomain.eq_div_of_mul_eq_left (radical_ne_zero a)
  rwa [mul_comm]

theorem divRadical_hMul {a b : k[X]} (hc : IsCoprime a b) :
    divRadical (a * b) = (divRadical a) * (divRadical b) := by
  by_cases ha : a = 0
  · rw [ha, MulZeroClass.zero_mul, divRadical, EuclideanDomain.zero_div, MulZeroClass.zero_mul]
  by_cases hb : b = 0
  · rw [hb, MulZeroClass.mul_zero, divRadical, EuclideanDomain.zero_div, MulZeroClass.mul_zero]
  symm; apply eq_divRadical
  rw [radical_hMul hc]
  rw [mul_mul_mul_comm, hMul_radical_divRadical, hMul_radical_divRadical]

theorem divRadical_dvd_self (a : k[X]) : (divRadical a) ∣ a := by
  rw [divRadical]
  apply EuclideanDomain.div_dvd_of_dvd
  exact radical_dvd_self a

/-
Main lemma: `divRadical a` divides `a'`.
Proof uses `induction_on_coprime` of `UniqueFactorizationDomain`.
-/
theorem divRadical_dvd_derivative (a : k[X]) : (divRadical a) ∣ (derivative a) := by
  induction a using induction_on_coprime
  · case h0 =>
    rw [derivative_zero]
    apply dvd_zero
  · case h1 a ha =>
    exact (divRadical_isUnit ha).dvd
  · case hpr p i hp =>
    cases i
    · rw [pow_zero, derivative_one]
      apply dvd_zero
    · case succ i =>
      rw [← mul_dvd_mul_iff_left (radical_ne_zero (p ^ i.succ)), hMul_radical_divRadical,
        radical_pow_of_prime hp i.succ_pos, derivative_pow_succ, ← mul_assoc]
      apply dvd_mul_of_dvd_left
      rw [mul_comm, mul_assoc]
      apply dvd_mul_of_dvd_right
      rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero i hp.ne_zero), dvd_normalize_iff]
  · -- If it holds for coprime pair a and b, then it also holds for a * b.
    case hcp x y hpxy hx hy =>
    have hc : IsCoprime x y :=
      EuclideanDomain.isCoprime_of_dvd
        (fun ⟨hx, hy⟩ => not_isUnit_zero (hpxy (zero_dvd_iff.mpr hx) (zero_dvd_iff.mpr hy)))
        fun p hp _ hpx hpy => hp (hpxy hpx hpy)
    rw [divRadical_hMul hc, derivative_mul]
    exact dvd_add (mul_dvd_mul hx (divRadical_dvd_self y)) (mul_dvd_mul (divRadical_dvd_self x) hy)

theorem divRadical_dvd_wronskian_left (a b : k[X]) : (divRadical a) ∣ wronskian a b := by
  rw [wronskian]
  apply dvd_sub
  · apply dvd_mul_of_dvd_left
    exact divRadical_dvd_self a
  · apply dvd_mul_of_dvd_left
    exact divRadical_dvd_derivative a

theorem divRadical_dvd_wronskian_right (a b : k[X]) : (divRadical b) ∣ wronskian a b := by
  rw [← wronskian_neg_eq, dvd_neg]
  exact divRadical_dvd_wronskian_left _ _

@[simp]
theorem dvd_derivative_iff {a : k[X]} : a ∣ derivative a ↔ derivative a = 0 := by
  constructor
  intro h
  by_cases a_nz : a = 0
  · rw [a_nz]; simp only [derivative_zero]
  by_contra deriv_nz
  have deriv_lt := degree_derivative_lt a_nz
  have le_deriv := Polynomial.degree_le_of_dvd h deriv_nz
  have lt_self := le_deriv.trans_lt deriv_lt
  simp only [lt_self_iff_false] at lt_self
  intro h; rw [h]; simp

theorem IsCoprime.wronskian_eq_zero_iff {a b : k[X]} (hc : IsCoprime a b) :
    wronskian a b = 0 ↔ derivative a = 0 ∧ derivative b = 0 := by
  constructor
  intro hw
  rw [wronskian, sub_eq_iff_eq_add, zero_add] at hw
  constructor
  · rw [← dvd_derivative_iff]
    apply hc.dvd_of_dvd_mul_right
    rw [← hw]; exact dvd_mul_right _ _
  · rw [← dvd_derivative_iff]
    apply hc.symm.dvd_of_dvd_mul_left
    rw [hw]; exact dvd_mul_left _ _
  intro hdab
  cases' hdab with hda hdb
  rw [wronskian]
  rw [hda, hdb]; simp only [MulZeroClass.mul_zero, MulZeroClass.zero_mul, sub_self]


protected theorem IsCoprime.divRadical {a b : k[X]} (h : IsCoprime a b) :
    IsCoprime (divRadical a) (divRadical b) := by
  rw [← hMul_radical_divRadical a] at h
  rw [← hMul_radical_divRadical b] at h
  exact h.of_mul_left_right.of_mul_right_right

private theorem abc_subcall {a b c w : k[X]} {hw : w ≠ 0} (wab : w = wronskian a b) (ha : a ≠ 0)
    (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b) (hbc : IsCoprime b c) (hca : IsCoprime c a)
    (abc_dr_dvd_w : divRadical (a * b * c) ∣ w) : c.natDegree + 1 ≤ (radical (a * b * c)).natDegree := by
  have hab := mul_ne_zero ha hb
  have habc := mul_ne_zero hab hc
  set abc_dr_nd := (divRadical (a * b * c)).natDegree with def_abc_dr_nd
  set abc_r_nd := (radical (a * b * c)).natDegree with def_abc_r_nd
  have t11 : abc_dr_nd < a.natDegree + b.natDegree := by
    calc
      abc_dr_nd ≤ w.natDegree := Polynomial.natDegree_le_of_dvd abc_dr_dvd_w hw
      _ < a.natDegree + b.natDegree := by rw [wab] at hw ⊢; exact natDegree_wronskian_lt_add hw
  have t4 : abc_dr_nd + abc_r_nd < a.natDegree + b.natDegree + abc_r_nd :=
    Nat.add_lt_add_right t11 abc_r_nd
  have t3 : abc_dr_nd + abc_r_nd = a.natDegree + b.natDegree + c.natDegree := by
    calc
      abc_dr_nd + abc_r_nd = ((divRadical (a * b * c)) * (radical (a * b * c))).natDegree := by
        rw [←
          Polynomial.natDegree_mul (divRadical_ne_zero habc) (radical_ne_zero (a * b * c))]
      _ = (a * b * c).natDegree := by
        rw [mul_comm _ (radical _)]; rw [hMul_radical_divRadical (a * b * c)]
      _ = a.natDegree + b.natDegree + c.natDegree := by
        rw [Polynomial.natDegree_mul hab hc, Polynomial.natDegree_mul ha hb]
  rw [t3] at t4
  exact Nat.lt_of_add_lt_add_left t4

private theorem rot3_add {a b c : k[X]} : a + b + c = b + c + a := by ring_nf

private theorem rot3_mul {a b c : k[X]} : a * b * c = b * c * a := by ring_nf

/-- Polynomial ABC theorem. -/
theorem Polynomial.abc {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b)
    (hbc : IsCoprime b c) (hca : IsCoprime c a) (hsum : a + b + c = 0) :
    max₃ (natDegree a) (natDegree b) (natDegree c) + 1 ≤ (radical (a * b * c)).natDegree ∨
      derivative a = 0 ∧ derivative b = 0 ∧ derivative c = 0 := by
  -- Utility assertions
  have wbc := wronskian_eq_of_sum_zero hsum
  set w := wronskian a b with wab
  have wca : w = wronskian c a := by
    rw [rot3_add] at hsum
    have h := wronskian_eq_of_sum_zero hsum
    rw [← wbc] at h; exact h
  have abc_dr_dvd_w : divRadical (a * b * c) ∣ w := by
    have adr_dvd_w := divRadical_dvd_wronskian_left a b
    have bdr_dvd_w := divRadical_dvd_wronskian_right a b
    have cdr_dvd_w := divRadical_dvd_wronskian_right b c
    rw [← wab] at adr_dvd_w bdr_dvd_w
    rw [← wbc] at cdr_dvd_w
    have cop_ab_dr := hab.divRadical
    have cop_bc_dr := hbc.divRadical
    have cop_ca_dr := hca.divRadical
    have cop_abc_dr := cop_ca_dr.symm.mul_left cop_bc_dr
    have abdr_dvd_w := cop_ab_dr.mul_dvd adr_dvd_w bdr_dvd_w
    have abcdr_dvd_w := cop_abc_dr.mul_dvd abdr_dvd_w cdr_dvd_w
    convert abcdr_dvd_w using 1
    rw [← divRadical_hMul hab]
    rw [← divRadical_hMul _]
    exact hca.symm.mul_left hbc
  by_cases hw : w = 0
  · right
    rw [hw] at wab wbc
    cases' hab.wronskian_eq_zero_iff.mp wab.symm with ga gb
    cases' hbc.wronskian_eq_zero_iff.mp wbc.symm with _ gc
    refine' ⟨ga, gb, gc⟩
  · left
    rw [max₃_add_distrib_right, max₃_le]
    refine' ⟨_, _, _⟩
    · rw [rot3_mul] at abc_dr_dvd_w ⊢
      apply abc_subcall wbc <;> assumption
    · rw [rot3_mul, rot3_mul] at abc_dr_dvd_w ⊢
      apply abc_subcall wca <;> assumption
    · apply abc_subcall wab <;> assumption
