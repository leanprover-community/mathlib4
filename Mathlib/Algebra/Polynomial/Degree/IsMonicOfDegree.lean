/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Monic

/-!
# Monic polynomials of given degree

This file defines the predicate `Polynomial.IsMonicOfDegree p n` that states that
the polynomial `p` is monic and has degree `n` (i.e., `p.natDegree = n`.)

We also provide some basic API.
-/

namespace Polynomial

variable {R : Type*}

section Semiring

variable [Semiring R]

/-- This says that `p` has `natDegree` `n` and is monic. -/
@[mk_iff isMonicOfDegree_iff']
structure IsMonicOfDegree (p : R[X]) (n : ℕ) : Prop where
  natDegree_eq : p.natDegree = n
  monic : p.Monic

@[simp]
lemma isMonicOfDegree_zero_iff {p : R[X]} : IsMonicOfDegree p 0 ↔ p = 1 := by
  simp only [isMonicOfDegree_iff']
  refine ⟨fun ⟨H₁, H₂⟩ ↦ eq_one_of_monic_natDegree_zero H₂ H₁, fun H ↦ ?_⟩
  subst H
  simp

lemma IsMonicOfDegree.leadingCoeff_eq {p : R[X]} {n : ℕ} (hp : IsMonicOfDegree p n) :
    p.leadingCoeff = 1 :=
  Monic.def.mp hp.monic

@[simp]
lemma isMonicOfDegree_iff_of_subsingleton [Subsingleton R] {p : R[X]} {n : ℕ} :
    IsMonicOfDegree p n ↔ n = 0 := by
  rw [Subsingleton.eq_one p]
  refine ⟨fun ⟨H, _⟩ ↦ ?_, fun H ↦ ?_⟩
  · rwa [natDegree_one, eq_comm] at H
  · rw [H, isMonicOfDegree_zero_iff]

lemma isMonicOfDegree_iff [Nontrivial R] (p : R[X]) (n : ℕ) :
    IsMonicOfDegree p n ↔ p.natDegree ≤ n ∧ p.coeff n = 1 := by
  simp only [isMonicOfDegree_iff']
  refine ⟨fun ⟨H₁, H₂⟩ ↦ ⟨H₁.le, H₁ ▸ Monic.coeff_natDegree H₂⟩, fun ⟨H₁, H₂⟩ ↦ ⟨?_, ?_⟩⟩
  · exact natDegree_eq_of_le_of_coeff_ne_zero H₁ <| H₂ ▸ one_ne_zero
  · exact monic_of_natDegree_le_of_coeff_eq_one n H₁ H₂

lemma IsMonicOfDegree.exists_natDegree_lt {p : R[X]} {n : ℕ} (hn : n ≠ 0)
    (hp : IsMonicOfDegree p n) :
    ∃ q : R[X], p = X ^ n + q ∧ q.natDegree < n := by
  refine ⟨p.eraseLead, ?_, ?_⟩
  · nth_rewrite 1 [← p.eraseLead_add_C_mul_X_pow]
    rw [add_comm, hp.natDegree_eq, hp.leadingCoeff_eq, map_one, one_mul]
  · refine p.eraseLead_natDegree_le.trans_lt ?_
    rw [hp.natDegree_eq]
    cutsat

lemma IsMonicOfDegree.mul {p q : R[X]} {m n : ℕ} (hp : IsMonicOfDegree p m)
    (hq : IsMonicOfDegree q n) :
    IsMonicOfDegree (p * q) (m + n) := by
  rcases subsingleton_or_nontrivial R with H | H
  · simp only [isMonicOfDegree_iff_of_subsingleton, Nat.add_eq_zero_iff] at hp hq ⊢
    exact ⟨hp, hq⟩
  refine ⟨?_, hp.monic.mul hq.monic⟩
  have : p.leadingCoeff * q.leadingCoeff ≠ 0 := by
    rw [hp.leadingCoeff_eq, hq.leadingCoeff_eq, one_mul]
    exact one_ne_zero
  rw [natDegree_mul' this, hp.natDegree_eq, hq.natDegree_eq]

lemma IsMonicOfDegree.pow {p : R[X]} {m : ℕ} (hp : IsMonicOfDegree p m) (n : ℕ) :
    IsMonicOfDegree (p ^ n) (m * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_add, mul_one]
    exact ih.mul hp

lemma IsMonicOfDegree.coeff_eq {p q : R[X]} {n : ℕ} (hp : IsMonicOfDegree p n)
    (hq : IsMonicOfDegree q n) {m : ℕ} (hm : n ≤ m) :
    p.coeff m = q.coeff m := by
  nontriviality R
  rw [isMonicOfDegree_iff] at hp hq
  rcases eq_or_lt_of_le hm with rfl | hm
  · rw [hp.2, hq.2]
  · replace hp : p.natDegree < m := hp.1.trans_lt hm
    replace hq : q.natDegree < m := hq.1.trans_lt hm
    rw [coeff_eq_zero_of_natDegree_lt hp, coeff_eq_zero_of_natDegree_lt hq]

lemma IsMonicOfDegree.of_mul_left {p q : R[X]} {m n : ℕ} (hp : IsMonicOfDegree p m)
    (hpq : IsMonicOfDegree (p * q) (m + n)) :
    IsMonicOfDegree q n := by
  rcases subsingleton_or_nontrivial R with H | H
  · simp only [isMonicOfDegree_iff_of_subsingleton, Nat.add_eq_zero_iff] at hpq ⊢
    exact hpq.2
  have h₂ : q.Monic := hp.monic.of_mul_monic_left hpq.monic
  refine ⟨?_, h₂⟩
  have := hpq.natDegree_eq
  have h : p.leadingCoeff * q.leadingCoeff ≠ 0 := by
    rw [hp.leadingCoeff_eq, h₂.leadingCoeff, one_mul]
    exact one_ne_zero
  rw [natDegree_mul' h, hp.natDegree_eq] at this
  exact (Nat.add_left_cancel this.symm).symm

lemma IsMonicOfDegree.of_mul_right {p q : R[X]} {m n : ℕ} (hq : IsMonicOfDegree q n)
    (hpq : IsMonicOfDegree (p * q) (m + n)) :
    IsMonicOfDegree p m := by
  rcases subsingleton_or_nontrivial R with H | H
  · simp only [isMonicOfDegree_iff_of_subsingleton, Nat.add_eq_zero_iff] at hpq ⊢
    exact hpq.1
  have h₂ : p.Monic := hq.monic.of_mul_monic_right hpq.monic
  refine ⟨?_, h₂⟩
  have := hpq.natDegree_eq
  have h : p.leadingCoeff * q.leadingCoeff ≠ 0 := by
    rw [h₂.leadingCoeff, hq.leadingCoeff_eq, one_mul]
    exact one_ne_zero
  rw [natDegree_mul' h, hq.natDegree_eq] at this
  exact (Nat.add_right_cancel this.symm).symm

lemma IsMonicOfDegree.add_right {p q : R[X]} {n : ℕ} (hp : IsMonicOfDegree p n)
    (hq : q.natDegree < n) :
    IsMonicOfDegree (p + q) n := by
  rcases subsingleton_or_nontrivial R with H | H
  · simpa using hp
  refine (isMonicOfDegree_iff ..).mpr ⟨?_, ?_⟩
  · exact natDegree_add_le_of_degree_le hp.natDegree_eq.le hq.le
  · rw [coeff_add_eq_left_of_lt hq]
    exact ((isMonicOfDegree_iff p n).mp hp).2

lemma IsMonicOfDegree.add_left {p q : R[X]} {n : ℕ} (hp : p.natDegree < n)
    (hq : IsMonicOfDegree q n) :
    IsMonicOfDegree (p + q) n := by
  rw [add_comm]
  exact hq.add_right hp

lemma IsMonicOfDegree.comp {p q : R[X]} {m n : ℕ} (hn : n ≠ 0) (hp : IsMonicOfDegree p m)
    (hq : IsMonicOfDegree q n) :
    IsMonicOfDegree (p.comp q) (m * n) := by
  rcases subsingleton_or_nontrivial R with h | h
  · simp only [isMonicOfDegree_iff_of_subsingleton, mul_eq_zero] at hp ⊢
    exact .inl hp
  rw [← hp.natDegree_eq, ← hq.natDegree_eq]
  refine (isMonicOfDegree_iff ..).mpr ⟨natDegree_comp_le, ?_⟩
  rw [coeff_comp_degree_mul_degree (hq.natDegree_eq ▸ hn), hp.leadingCoeff_eq, hq.leadingCoeff_eq,
    one_pow, one_mul]

variable [Nontrivial R]

lemma IsMonicOfDegree.ne_zero {p : R[X]} {n : ℕ} (h : IsMonicOfDegree p n) : p ≠ 0 :=
  h.monic.ne_zero

variable (R) in
lemma isMonicOfDegree_X : IsMonicOfDegree (X : R[X]) 1 :=
  (isMonicOfDegree_iff ..).mpr ⟨natDegree_X_le, coeff_X_one⟩

variable (R) in
lemma isMonicOfDegree_X_pow (n : ℕ) : IsMonicOfDegree ((X : R[X]) ^ n) n :=
  (isMonicOfDegree_iff ..).mpr ⟨natDegree_X_pow_le n, coeff_X_pow_self n⟩

lemma isMonicOfDegree_monomial_one (n : ℕ) : IsMonicOfDegree (monomial n (1 : R)) n := by
  simpa only [monomial_one_right_eq_X_pow] using isMonicOfDegree_X_pow R n

lemma isMonicOfDegree_X_add_one (r : R) : IsMonicOfDegree (X + C r) 1 :=
  (isMonicOfDegree_X R).add_right (by rw [natDegree_C]; exact zero_lt_one)

lemma isMonicOfDegree_one_iff {f : R[X]} : IsMonicOfDegree f 1 ↔ ∃ r : R, f = X + C r := by
  refine ⟨fun H ↦ ?_, fun ⟨r, H⟩ ↦ H ▸ isMonicOfDegree_X_add_one r⟩
  refine ⟨f.coeff 0, ?_⟩
  ext1 n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · exact H.coeff_eq (isMonicOfDegree_X_add_one _) (by cutsat)

lemma isMonicOfDegree_add_add_two (a b : R) : IsMonicOfDegree (X ^ 2 + C a * X + C b) 2 := by
  rw [add_assoc]
  exact (isMonicOfDegree_X_pow R 2).add_right <|
    calc
    _ ≤ max (C a * X).natDegree (C b).natDegree := natDegree_add_le ..
    _ = (C a * X).natDegree := by simp
    _ < 2 := natDegree_C_mul_le .. |>.trans natDegree_X_le |>.trans_lt one_lt_two

lemma isMonicOfDegree_two_iff {f : R[X]} :
    IsMonicOfDegree f 2 ↔ ∃ a b : R, f = X ^ 2 + C a * X + C b := by
  refine ⟨fun H ↦ ?_, fun ⟨a, b, h⟩ ↦ h ▸ isMonicOfDegree_add_add_two a b⟩
  refine ⟨f.coeff 1, f.coeff 0, ext fun n ↦ ?_⟩
  rcases lt_trichotomy n 1 with hn | rfl | hn
  · obtain rfl : n = 0 := Nat.lt_one_iff.mp hn
    simp
  · simp
  · exact H.coeff_eq (isMonicOfDegree_add_add_two ..) (by cutsat)

end Semiring

section Ring

variable [Ring R]

lemma IsMonicOfDegree.natDegree_sub_X_pow {p : R[X]} {n : ℕ} (hn : n ≠ 0)
    (hp : IsMonicOfDegree p n) :
    (p - X ^ n).natDegree < n := by
  obtain ⟨q, hq₁, hq₂⟩ := hp.exists_natDegree_lt hn
  simpa [hq₁]

lemma IsMonicOfDegree.natDegree_sub_lt {p q : R[X]} {n : ℕ} (hn : n ≠ 0) (hp : IsMonicOfDegree p n)
    (hq : IsMonicOfDegree q n) :
    (p - q).natDegree < n := by
  rw [← sub_sub_sub_cancel_right p q (X ^ n)]
  replace hp := hp.natDegree_sub_X_pow hn
  replace hq := hq.natDegree_sub_X_pow hn
  rw [← Nat.le_sub_one_iff_lt (Nat.zero_lt_of_ne_zero hn)] at hp hq ⊢
  exact (natDegree_sub_le_iff_left hq).mpr hp

lemma IsMonicOfDegree.sub {p q : R[X]} {n : ℕ} (hp : IsMonicOfDegree p n) (hq : q.natDegree < n) :
    IsMonicOfDegree (p - q) n := by
  rw [sub_eq_add_neg]
  exact hp.add_right <| (natDegree_neg q) ▸ hq

variable [Nontrivial R]

lemma isMonicOfDegree_X_sub_one (r : R) : IsMonicOfDegree (X - C r) 1 :=
  (isMonicOfDegree_X R).sub (by rw [natDegree_C]; exact zero_lt_one)

lemma isMonicOfDegree_sub_add_two (a b : R) : IsMonicOfDegree (X ^ 2 - C a * X + C b) 2 := by
  rw [sub_add]
  exact (isMonicOfDegree_X_pow R 2).add_right <| by
    rw [natDegree_neg]
    calc
    _ ≤ max (C a * X).natDegree (C b).natDegree := natDegree_sub_le ..
    _ = (C a * X).natDegree := by simp
    _ < 2 := natDegree_C_mul_le .. |>.trans natDegree_X_le |>.trans_lt one_lt_two

/-- A version of `Polynomial.isMonicOfDegree_two_iff` with negated middle coefficient. -/
lemma isMonicOfDegree_two_iff' {f : R[X]} :
    IsMonicOfDegree f 2 ↔ ∃ a b : R, f = X ^ 2 - C a * X + C b := by
  refine ⟨fun H ↦ ?_, fun ⟨a, b, h⟩ ↦ h ▸ isMonicOfDegree_sub_add_two a b⟩
  simp only [sub_eq_add_neg, ← neg_mul, ← map_neg]
  obtain ⟨a, b, h⟩ := isMonicOfDegree_two_iff.mp H
  exact ⟨-a, b, (neg_neg a).symm ▸ h⟩

end Ring

section CommRing

variable [CommRing R]

lemma IsMonicOfDegree.of_dvd_add {a b r : R[X]} {m n : ℕ} (hmn : n ≤ m) (ha : IsMonicOfDegree a m)
    (hb : IsMonicOfDegree b n) (hr : r.natDegree < m) (h : b ∣ a + r) :
    ∃ q : R[X], IsMonicOfDegree q (m - n) ∧ a = q * b - r := by
  obtain ⟨q, hq⟩ := exists_eq_mul_left_of_dvd  h
  refine ⟨q, hb.of_mul_right ?_, eq_sub_iff_add_eq.mpr hq⟩
  rw [← hq, show m - n + n = m by cutsat]
  exact ha.add_right hr

lemma IsMonicOfDegree.of_dvd_sub {a b r : R[X]} {m n : ℕ} (hmn : n ≤ m) (ha : IsMonicOfDegree a m)
    (hb : IsMonicOfDegree b n) (hr : r.natDegree < m) (h : b ∣ a - r) :
    ∃ q : R[X], IsMonicOfDegree q (m - n) ∧ a = q * b + r := by
  convert ha.of_dvd_add hmn hb ?_ h using 4 with q
  · rw [sub_neg_eq_add]
  · rwa [natDegree_neg]

lemma IsMonicOfDegree.aeval_add {p : R[X]} {n : ℕ} (hp : IsMonicOfDegree p n) (r : R) :
    IsMonicOfDegree (aeval (X + C r) p) n := by
  rcases subsingleton_or_nontrivial R with H | H
  · simpa using hp
  rw [← mul_one n]
  exact hp.comp one_ne_zero (isMonicOfDegree_X_add_one r)

lemma IsMonicOfDegree.aeval_sub {p : R[X]} {n : ℕ} (hp : IsMonicOfDegree p n) (r : R) :
    IsMonicOfDegree (aeval (X - C r) p) n := by
  rw [sub_eq_add_neg, ← map_neg]
  exact aeval_add hp (-r)

end CommRing

end Polynomial
