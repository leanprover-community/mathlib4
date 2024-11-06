/-
Copyright (c) 2024 Jineon Baek and Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek, Seewoo Lee
-/
import Mathlib.RingTheory.Polynomial.Radical

/-!
# Mason-Stothers theorem

This file states and proves Mason-Stothers theorem, which is a polynomial version of ABC conjecture.
For a (pairwise) coprime polynomials `a, b, c` (over a field) with `a + b + c = 0`, we have
`max {deg(a), deg(b), deg(c)} + 1 ≤ deg(rad(abc))` or `a' = b' = c' = 0`.

Proof is based on this online note by Franz Lemmermeyer http://www.fen.bilkent.edu.tr/~franz/ag05/ag-02.pdf,
which is essentially based on Noah Snyder's paper "An Alternative Proof of Mason's Theorem",
but slightly different.

## TODO

Prove polynomial FLT using Mason-Stothers theorem.
-/

noncomputable section

open scoped Classical

open Polynomial UniqueFactorizationMonoid UniqueFactorizationDomain EuclideanDomain

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

private theorem abc_subcall {a b c w : k[X]} {hw : w ≠ 0} (wab : w = wronskian a b) (ha : a ≠ 0)
    (hb : b ≠ 0) (hc : c ≠ 0) (abc_dr_dvd_w : divRadical (a * b * c) ∣ w) :
      c.natDegree + 1 ≤ (radical (a * b * c)).natDegree := by
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
        rw [mul_comm _ (radical _)]; rw [radical_mul_divRadical (a * b * c)]
      _ = a.natDegree + b.natDegree + c.natDegree := by
        rw [Polynomial.natDegree_mul hab hc, Polynomial.natDegree_mul ha hb]
  rw [t3] at t4
  exact Nat.lt_of_add_lt_add_left t4

/-- **Polynomial ABC theorem.** -/
theorem Polynomial.abc {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b)
    (hbc : IsCoprime b c) (hca : IsCoprime c a) (hsum : a + b + c = 0) :
    max₃ (natDegree a) (natDegree b) (natDegree c) + 1 ≤ (radical (a * b * c)).natDegree ∨
      derivative a = 0 ∧ derivative b = 0 ∧ derivative c = 0 := by
  -- Utility assertions
  have wbc := wronskian_eq_of_sum_zero hsum
  set w := wronskian a b with wab
  have wca : w = wronskian c a := by
    rw [add_rotate] at hsum
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
    rw [← divRadical_mul hab]
    rw [← divRadical_mul]
    exact hca.symm.mul_left hbc
  by_cases hw : w = 0
  · right
    rw [hw] at wab wbc
    cases' hab.wronskian_eq_zero_iff.mp wab.symm with ga gb
    cases' hbc.wronskian_eq_zero_iff.mp wbc.symm with _ gc
    exact ⟨ga, gb, gc⟩
  · left
    rw [max₃_add_distrib_right, max₃_le]
    refine ⟨?_, ?_, ?_⟩
    · rw [mul_rotate] at abc_dr_dvd_w ⊢
      apply abc_subcall wbc <;> assumption
    · rw [← mul_rotate] at abc_dr_dvd_w ⊢
      apply abc_subcall wca <;> assumption
    · apply abc_subcall wab <;> assumption
