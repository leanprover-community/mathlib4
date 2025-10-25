/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.GroupWithZero.Regular
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Definitions

/-!
# Lemmas for calculating the degree of univariate polynomials

## Main results
- `degree_mul` : The degree of the product is the sum of degrees
- `leadingCoeff_add_of_degree_eq` and `leadingCoeff_add_of_degree_lt` :
    The leading coefficient of a sum is determined by the leading coefficients and degrees
-/

noncomputable section

open Finsupp Finset

open Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

section Semiring

variable [Semiring R] [Semiring S] {p q r : R[X]}

theorem supDegree_eq_degree (p : R[X]) : p.toFinsupp.supDegree WithBot.some = p.degree :=
  max_eq_sup_coe

theorem degree_lt_wf : WellFounded fun p q : R[X] => degree p < degree q :=
  InvImage.wf degree wellFounded_lt

instance : WellFoundedRelation R[X] :=
  ⟨_, degree_lt_wf⟩

@[nontriviality]
theorem monic_of_subsingleton [Subsingleton R] (p : R[X]) : Monic p :=
  Subsingleton.elim _ _

@[nontriviality]
theorem degree_of_subsingleton [Subsingleton R] : degree p = ⊥ := by
  rw [Subsingleton.elim p 0, degree_zero]

@[nontriviality]
theorem natDegree_of_subsingleton [Subsingleton R] : natDegree p = 0 := by
  rw [Subsingleton.elim p 0, natDegree_zero]

theorem le_natDegree_of_ne_zero (h : coeff p n ≠ 0) : n ≤ natDegree p := by
  rw [← Nat.cast_le (α := WithBot ℕ), ← degree_eq_natDegree]
  · exact le_degree_of_ne_zero h
  · rintro rfl
    exact h rfl

theorem degree_eq_of_le_of_coeff_ne_zero (pn : p.degree ≤ n) (p1 : p.coeff n ≠ 0) : p.degree = n :=
  pn.antisymm (le_degree_of_ne_zero p1)

theorem natDegree_eq_of_le_of_coeff_ne_zero (pn : p.natDegree ≤ n) (p1 : p.coeff n ≠ 0) :
    p.natDegree = n :=
  pn.antisymm (le_natDegree_of_ne_zero p1)

theorem natDegree_lt_natDegree {q : S[X]} (hp : p ≠ 0) (hpq : p.degree < q.degree) :
    p.natDegree < q.natDegree := by
  by_cases hq : q = 0
  · exact (not_lt_bot <| hq ▸ hpq).elim
  rwa [degree_eq_natDegree hp, degree_eq_natDegree hq, Nat.cast_lt] at hpq

lemma natDegree_eq_natDegree {q : S[X]} (hpq : p.degree = q.degree) :
    p.natDegree = q.natDegree := by simp [natDegree, hpq]

theorem coeff_eq_zero_of_degree_lt (h : degree p < n) : coeff p n = 0 :=
  Classical.not_not.1 (mt le_degree_of_ne_zero (not_le_of_gt h))

theorem coeff_eq_zero_of_natDegree_lt {p : R[X]} {n : ℕ} (h : p.natDegree < n) :
    p.coeff n = 0 := by
  apply coeff_eq_zero_of_degree_lt
  by_cases hp : p = 0
  · subst hp
    exact WithBot.bot_lt_coe n
  · rwa [degree_eq_natDegree hp, Nat.cast_lt]

theorem ext_iff_natDegree_le {p q : R[X]} {n : ℕ} (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    p = q ↔ ∀ i ≤ n, p.coeff i = q.coeff i := by
  refine Iff.trans Polynomial.ext_iff ?_
  refine forall_congr' fun i => ⟨fun h _ => h, fun h => ?_⟩
  refine (le_or_gt i n).elim h fun k => ?_
  exact
    (coeff_eq_zero_of_natDegree_lt (hp.trans_lt k)).trans
      (coeff_eq_zero_of_natDegree_lt (hq.trans_lt k)).symm

theorem ext_iff_degree_le {p q : R[X]} {n : ℕ} (hp : p.degree ≤ n) (hq : q.degree ≤ n) :
    p = q ↔ ∀ i ≤ n, p.coeff i = q.coeff i :=
  ext_iff_natDegree_le (natDegree_le_of_degree_le hp) (natDegree_le_of_degree_le hq)

@[simp]
theorem coeff_natDegree_succ_eq_zero {p : R[X]} : p.coeff (p.natDegree + 1) = 0 :=
  coeff_eq_zero_of_natDegree_lt (lt_add_one _)

-- We need the explicit `Decidable` argument here because an exotic one shows up in a moment!
theorem ite_le_natDegree_coeff (p : R[X]) (n : ℕ) (I : Decidable (n < 1 + natDegree p)) :
    @ite _ (n < 1 + natDegree p) I (coeff p n) 0 = coeff p n := by
  split_ifs with h
  · rfl
  · exact (coeff_eq_zero_of_natDegree_lt (not_le.1 fun w => h (Nat.lt_one_add_iff.2 w))).symm

end Semiring

section Ring

variable [Ring R]

theorem coeff_mul_X_sub_C {p : R[X]} {r : R} {a : ℕ} :
    coeff (p * (X - C r)) (a + 1) = coeff p a - coeff p (a + 1) * r := by simp [mul_sub]

theorem coeff_X_sub_C_mul {p : R[X]} {r : R} {a : ℕ} :
    coeff ((X - C r) * p) (a + 1) = coeff p a - r * coeff p (a + 1) := by simp [sub_mul]

end Ring

section Semiring

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem coeff_natDegree_eq_zero_of_degree_lt (h : degree p < degree q) :
    coeff p (natDegree q) = 0 :=
  coeff_eq_zero_of_degree_lt (lt_of_lt_of_le h degree_le_natDegree)

theorem ne_zero_of_degree_gt {n : WithBot ℕ} (h : n < degree p) : p ≠ 0 :=
  mt degree_eq_bot.2 h.ne_bot

theorem ne_zero_of_degree_ge_degree (hpq : p.degree ≤ q.degree) (hp : p ≠ 0) : q ≠ 0 :=
  Polynomial.ne_zero_of_degree_gt
    (lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr (by rwa [Ne, Polynomial.degree_eq_bot])) hpq :
      q.degree > ⊥)

theorem ne_zero_of_natDegree_gt {n : ℕ} (h : n < natDegree p) : p ≠ 0 := fun H => by
  simp [H] at h

theorem degree_lt_degree (h : natDegree p < natDegree q) : degree p < degree q := by
  by_cases hp : p = 0
  · simp only [hp, degree_zero]
    rw [bot_lt_iff_ne_bot]
    intro hq
    simp [hp, degree_eq_bot.mp hq] at h
  · rwa [degree_eq_natDegree hp, degree_eq_natDegree <| ne_zero_of_natDegree_gt h, Nat.cast_lt]

theorem natDegree_lt_natDegree_iff (hp : p ≠ 0) : natDegree p < natDegree q ↔ degree p < degree q :=
  ⟨degree_lt_degree, fun h ↦ by
    have hq : q ≠ 0 := ne_zero_of_degree_gt h
    rwa [degree_eq_natDegree hp, degree_eq_natDegree hq, Nat.cast_lt] at h⟩

theorem eq_C_of_degree_le_zero (h : degree p ≤ 0) : p = C (coeff p 0) := by
  ext (_ | n)
  · simp
  rw [coeff_C, if_neg (Nat.succ_ne_zero _), coeff_eq_zero_of_degree_lt]
  exact h.trans_lt (WithBot.coe_lt_coe.2 n.succ_pos)

theorem eq_C_of_degree_eq_zero (h : degree p = 0) : p = C (coeff p 0) :=
  eq_C_of_degree_le_zero h.le

theorem degree_le_zero_iff : degree p ≤ 0 ↔ p = C (coeff p 0) :=
  ⟨eq_C_of_degree_le_zero, fun h => h.symm ▸ degree_C_le⟩

theorem degree_add_eq_left_of_degree_lt (h : degree q < degree p) : degree (p + q) = degree p :=
  le_antisymm (max_eq_left_of_lt h ▸ degree_add_le _ _) <|
    degree_le_degree <| by
      rw [coeff_add, coeff_natDegree_eq_zero_of_degree_lt h, add_zero]
      exact mt leadingCoeff_eq_zero.1 (ne_zero_of_degree_gt h)

theorem degree_add_eq_right_of_degree_lt (h : degree p < degree q) : degree (p + q) = degree q := by
  rw [add_comm, degree_add_eq_left_of_degree_lt h]

theorem natDegree_add_eq_left_of_degree_lt (h : degree q < degree p) :
    natDegree (p + q) = natDegree p :=
  natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt h)

theorem natDegree_add_eq_left_of_natDegree_lt (h : natDegree q < natDegree p) :
    natDegree (p + q) = natDegree p :=
  natDegree_add_eq_left_of_degree_lt (degree_lt_degree h)

theorem natDegree_add_eq_right_of_degree_lt (h : degree p < degree q) :
    natDegree (p + q) = natDegree q :=
  natDegree_eq_of_degree_eq (degree_add_eq_right_of_degree_lt h)

theorem natDegree_add_eq_right_of_natDegree_lt (h : natDegree p < natDegree q) :
    natDegree (p + q) = natDegree q :=
  natDegree_add_eq_right_of_degree_lt (degree_lt_degree h)

theorem degree_add_C (hp : 0 < degree p) : degree (p + C a) = degree p :=
  add_comm (C a) p ▸ degree_add_eq_right_of_degree_lt <| lt_of_le_of_lt degree_C_le hp

@[simp] theorem natDegree_add_C {a : R} : (p + C a).natDegree = p.natDegree := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  by_cases hpd : p.degree ≤ 0
  · rw [eq_C_of_degree_le_zero hpd, ← C_add, natDegree_C, natDegree_C]
  · rw [not_le, degree_eq_natDegree hp, Nat.cast_pos, ← natDegree_C a] at hpd
    exact natDegree_add_eq_left_of_natDegree_lt hpd

@[simp] theorem natDegree_C_add {a : R} : (C a + p).natDegree = p.natDegree := by
  simp [add_comm _ p]

theorem degree_add_eq_of_leadingCoeff_add_ne_zero (h : leadingCoeff p + leadingCoeff q ≠ 0) :
    degree (p + q) = max p.degree q.degree :=
  le_antisymm (degree_add_le _ _) <|
    match lt_trichotomy (degree p) (degree q) with
    | Or.inl hlt => by
      rw [degree_add_eq_right_of_degree_lt hlt, max_eq_right_of_lt hlt]
    | Or.inr (Or.inl HEq) =>
      le_of_not_gt fun hlt : max (degree p) (degree q) > degree (p + q) =>
        h <|
          show leadingCoeff p + leadingCoeff q = 0 by
            rw [HEq, max_self] at hlt
            rw [leadingCoeff, leadingCoeff, natDegree_eq_of_degree_eq HEq, ← coeff_add]
            exact coeff_natDegree_eq_zero_of_degree_lt hlt
    | Or.inr (Or.inr hlt) => by
      rw [degree_add_eq_left_of_degree_lt hlt, max_eq_left_of_lt hlt]

lemma natDegree_eq_of_natDegree_add_lt_left (p q : R[X])
    (H : natDegree (p + q) < natDegree p) : natDegree p = natDegree q := by
  by_contra h
  cases Nat.lt_or_lt_of_ne h with
  | inl h => exact lt_asymm h (by rwa [natDegree_add_eq_right_of_natDegree_lt h] at H)
  | inr h =>
    rw [natDegree_add_eq_left_of_natDegree_lt h] at H
    exact LT.lt.false H

lemma natDegree_eq_of_natDegree_add_lt_right (p q : R[X])
    (H : natDegree (p + q) < natDegree q) : natDegree p = natDegree q :=
  (natDegree_eq_of_natDegree_add_lt_left q p (add_comm p q ▸ H)).symm

lemma natDegree_eq_of_natDegree_add_eq_zero (p q : R[X])
    (H : natDegree (p + q) = 0) : natDegree p = natDegree q := by
  by_cases h₁ : natDegree p = 0; on_goal 1 => by_cases h₂ : natDegree q = 0
  · exact h₁.trans h₂.symm
  · apply natDegree_eq_of_natDegree_add_lt_right; rwa [H, Nat.pos_iff_ne_zero]
  · apply natDegree_eq_of_natDegree_add_lt_left; rwa [H, Nat.pos_iff_ne_zero]

theorem monic_of_natDegree_le_of_coeff_eq_one (n : ℕ) (pn : p.natDegree ≤ n) (p1 : p.coeff n = 1) :
    Monic p := by
  unfold Monic
  nontriviality
  refine (congr_arg _ <| natDegree_eq_of_le_of_coeff_ne_zero pn ?_).trans p1
  exact ne_of_eq_of_ne p1 one_ne_zero

theorem monic_of_degree_le (n : ℕ) (pn : p.degree ≤ n) (p1 : p.coeff n = 1) : Monic p :=
  monic_of_natDegree_le_of_coeff_eq_one n (natDegree_le_of_degree_le pn) p1

@[deprecated (since := "2025-10-24")]
alias monic_of_degree_le_of_coeff_eq_one := monic_of_degree_le

theorem leadingCoeff_add_of_degree_lt (h : degree p < degree q) :
    leadingCoeff (p + q) = leadingCoeff q := by
  have : coeff p (natDegree q) = 0 := coeff_natDegree_eq_zero_of_degree_lt h
  simp only [leadingCoeff, natDegree_eq_of_degree_eq (degree_add_eq_right_of_degree_lt h), this,
    coeff_add, zero_add]

theorem leadingCoeff_add_of_degree_lt' (h : degree q < degree p) :
    leadingCoeff (p + q) = leadingCoeff p := by
  rw [add_comm]
  exact leadingCoeff_add_of_degree_lt h

theorem leadingCoeff_add_of_degree_eq (h : degree p = degree q)
    (hlc : leadingCoeff p + leadingCoeff q ≠ 0) :
    leadingCoeff (p + q) = leadingCoeff p + leadingCoeff q := by
  have : natDegree (p + q) = natDegree p := by
    apply natDegree_eq_of_degree_eq
    rw [degree_add_eq_of_leadingCoeff_add_ne_zero hlc, h, max_self]
  simp only [leadingCoeff, this, natDegree_eq_of_degree_eq h, coeff_add]

@[simp]
theorem coeff_mul_degree_add_degree (p q : R[X]) :
    coeff (p * q) (natDegree p + natDegree q) = leadingCoeff p * leadingCoeff q :=
  calc
    coeff (p * q) (natDegree p + natDegree q) =
        ∑ x ∈ antidiagonal (natDegree p + natDegree q), coeff p x.1 * coeff q x.2 :=
      coeff_mul _ _ _
    _ = coeff p (natDegree p) * coeff q (natDegree q) := by
      refine Finset.sum_eq_single (natDegree p, natDegree q) ?_ ?_
      · rintro ⟨i, j⟩ h₁ h₂
        rw [mem_antidiagonal] at h₁
        by_cases H : natDegree p < i
        · rw [coeff_eq_zero_of_degree_lt
              (lt_of_le_of_lt degree_le_natDegree (WithBot.coe_lt_coe.2 H)),
            zero_mul]
        · rw [not_lt_iff_eq_or_lt] at H
          rcases H with H | H
          · simp_all
          · suffices natDegree q < j by
              rw [coeff_eq_zero_of_degree_lt
                  (lt_of_le_of_lt degree_le_natDegree (WithBot.coe_lt_coe.2 this)),
                mul_zero]
            by_contra! H'
            exact
              ne_of_lt (Nat.lt_of_lt_of_le (Nat.add_lt_add_right H j) (Nat.add_le_add_left H' _))
                h₁
      · intro H
        exfalso
        apply H
        rw [mem_antidiagonal]

theorem degree_mul' (h : leadingCoeff p * leadingCoeff q ≠ 0) :
    degree (p * q) = degree p + degree q :=
  have hp : p ≠ 0 := by refine mt ?_ h; exact fun hp => by rw [hp, leadingCoeff_zero, zero_mul]
  have hq : q ≠ 0 := by refine mt ?_ h; exact fun hq => by rw [hq, leadingCoeff_zero, mul_zero]
  le_antisymm (degree_mul_le _ _)
    (by
      rw [degree_eq_natDegree hp, degree_eq_natDegree hq]
      refine le_degree_of_ne_zero (n := natDegree p + natDegree q) ?_
      rwa [coeff_mul_degree_add_degree])

theorem Monic.degree_mul (hq : Monic q) : degree (p * q) = degree p + degree q :=
  letI := Classical.decEq R
  if hp : p = 0 then by simp [hp]
  else degree_mul' <| by rwa [hq.leadingCoeff, mul_one, Ne, leadingCoeff_eq_zero]

theorem natDegree_mul' (h : leadingCoeff p * leadingCoeff q ≠ 0) :
    natDegree (p * q) = natDegree p + natDegree q :=
  have hp : p ≠ 0 := mt leadingCoeff_eq_zero.2 fun h₁ => h <| by rw [h₁, zero_mul]
  have hq : q ≠ 0 := mt leadingCoeff_eq_zero.2 fun h₁ => h <| by rw [h₁, mul_zero]
  natDegree_eq_of_degree_eq_some <| by
    rw [degree_mul' h, Nat.cast_add, degree_eq_natDegree hp, degree_eq_natDegree hq]

theorem leadingCoeff_mul' (h : leadingCoeff p * leadingCoeff q ≠ 0) :
    leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q := by
  unfold leadingCoeff
  rw [natDegree_mul' h, coeff_mul_degree_add_degree]
  rfl

theorem leadingCoeff_pow' : leadingCoeff p ^ n ≠ 0 → leadingCoeff (p ^ n) = leadingCoeff p ^ n :=
  Nat.recOn n (by simp) fun n ih h => by
    have h₁ : leadingCoeff p ^ n ≠ 0 := fun h₁ => h <| by rw [pow_succ, h₁, zero_mul]
    have h₂ : leadingCoeff p * leadingCoeff (p ^ n) ≠ 0 := by rwa [pow_succ', ← ih h₁] at h
    rw [pow_succ', pow_succ', leadingCoeff_mul' h₂, ih h₁]

theorem degree_pow' : ∀ {n : ℕ}, leadingCoeff p ^ n ≠ 0 → degree (p ^ n) = n • degree p
  | 0 => fun h => by rw [pow_zero, ← C_1] at *; rw [degree_C h, zero_nsmul]
  | n + 1 => fun h => by
    have h₁ : leadingCoeff p ^ n ≠ 0 := fun h₁ => h <| by rw [pow_succ, h₁, zero_mul]
    have h₂ : leadingCoeff (p ^ n) * leadingCoeff p ≠ 0 := by
      rwa [pow_succ, ← leadingCoeff_pow' h₁] at h
    rw [pow_succ, degree_mul' h₂, succ_nsmul, degree_pow' h₁]

theorem natDegree_pow' {n : ℕ} (h : leadingCoeff p ^ n ≠ 0) : natDegree (p ^ n) = n * natDegree p :=
  letI := Classical.decEq R
  if hp0 : p = 0 then
    if hn0 : n = 0 then by simp [*] else by rw [hp0, zero_pow hn0]; simp
  else
    have hpn : p ^ n ≠ 0 := fun hpn0 => by
      have h1 := h
      rw [← leadingCoeff_pow' h1, hpn0, leadingCoeff_zero] at h; exact h rfl
    Nat.cast_inj.1 <| by
      rw [← degree_eq_natDegree hpn, degree_pow' h, degree_eq_natDegree hp0]; simp

theorem leadingCoeff_monic_mul {p q : R[X]} (hp : Monic p) :
    leadingCoeff (p * q) = leadingCoeff q := by
  rcases eq_or_ne q 0 with (rfl | H)
  · simp
  · rw [leadingCoeff_mul', hp.leadingCoeff, one_mul]
    rwa [hp.leadingCoeff, one_mul, Ne, leadingCoeff_eq_zero]

theorem leadingCoeff_mul_monic {p q : R[X]} (hq : Monic q) :
    leadingCoeff (p * q) = leadingCoeff p :=
  letI := Classical.decEq R
  Decidable.byCases
    (fun H : leadingCoeff p = 0 => by
      rw [H, leadingCoeff_eq_zero.1 H, zero_mul, leadingCoeff_zero])
    fun H : leadingCoeff p ≠ 0 => by
      rw [leadingCoeff_mul', hq.leadingCoeff, mul_one]
      rwa [hq.leadingCoeff, mul_one]

lemma degree_C_mul_of_isUnit (ha : IsUnit a) (p : R[X]) : (C a * p).degree = p.degree := by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  nontriviality R
  rw [degree_mul', degree_C ha.ne_zero]
  · simp
  · simpa [ha.mul_right_eq_zero]

lemma degree_mul_C_of_isUnit (ha : IsUnit a) (p : R[X]) : (p * C a).degree = p.degree := by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  nontriviality R
  rw [degree_mul', degree_C ha.ne_zero]
  · simp
  · simpa [ha.mul_left_eq_zero]

lemma natDegree_C_mul_of_isUnit (ha : IsUnit a) (p : R[X]) : (C a * p).natDegree = p.natDegree := by
  simp [natDegree, degree_C_mul_of_isUnit ha]

lemma natDegree_mul_C_of_isUnit (ha : IsUnit a) (p : R[X]) : (p * C a).natDegree = p.natDegree := by
  simp [natDegree, degree_mul_C_of_isUnit ha]

lemma leadingCoeff_C_mul_of_isUnit (ha : IsUnit a) (p : R[X]) :
    (C a * p).leadingCoeff = a * p.leadingCoeff := by
  rwa [leadingCoeff, coeff_C_mul, natDegree_C_mul_of_isUnit, leadingCoeff]

lemma leadingCoeff_mul_C_of_isUnit (ha : IsUnit a) (p : R[X]) :
    (p * C a).leadingCoeff = p.leadingCoeff * a := by
  rwa [leadingCoeff, coeff_mul_C, natDegree_mul_C_of_isUnit, leadingCoeff]

@[simp]
theorem leadingCoeff_mul_X_pow {p : R[X]} {n : ℕ} : leadingCoeff (p * X ^ n) = leadingCoeff p :=
  leadingCoeff_mul_monic (monic_X_pow n)

@[simp]
theorem leadingCoeff_mul_X {p : R[X]} : leadingCoeff (p * X) = leadingCoeff p :=
  leadingCoeff_mul_monic monic_X

@[simp]
theorem coeff_pow_mul_natDegree (p : R[X]) (n : ℕ) :
    (p ^ n).coeff (n * p.natDegree) = p.leadingCoeff ^ n := by
  induction n with
  | zero => simp
  | succ i hi =>
    rw [pow_succ, pow_succ, Nat.succ_mul]
    by_cases hp1 : p.leadingCoeff ^ i = 0
    · rw [hp1, zero_mul]
      by_cases hp2 : p ^ i = 0
      · rw [hp2, zero_mul, coeff_zero]
      · apply coeff_eq_zero_of_natDegree_lt
        have h1 : (p ^ i).natDegree < i * p.natDegree := by
          refine lt_of_le_of_ne natDegree_pow_le fun h => hp2 ?_
          rw [← h, hp1] at hi
          exact leadingCoeff_eq_zero.mp hi
        calc
          (p ^ i * p).natDegree ≤ (p ^ i).natDegree + p.natDegree := natDegree_mul_le
          _ < i * p.natDegree + p.natDegree := by gcongr
    · rw [← natDegree_pow' hp1, ← leadingCoeff_pow' hp1]
      exact coeff_mul_degree_add_degree _ _

theorem coeff_mul_add_eq_of_natDegree_le {df dg : ℕ} {f g : R[X]}
    (hdf : natDegree f ≤ df) (hdg : natDegree g ≤ dg) :
    (f * g).coeff (df + dg) = f.coeff df * g.coeff dg := by
  rw [coeff_mul, Finset.sum_eq_single_of_mem (df, dg)]
  · rw [mem_antidiagonal]
  rintro ⟨df', dg'⟩ hmem hne
  obtain h | hdf' := lt_or_ge df df'
  · rw [coeff_eq_zero_of_natDegree_lt (hdf.trans_lt h), zero_mul]
  obtain h | hdg' := lt_or_ge dg dg'
  · rw [coeff_eq_zero_of_natDegree_lt (hdg.trans_lt h), mul_zero]
  obtain ⟨rfl, rfl⟩ :=
    (add_eq_add_iff_eq_and_eq hdf' hdg').mp (mem_antidiagonal.1 hmem)
  exact (hne rfl).elim

theorem degree_smul_le {S : Type*} [SMulZeroClass S R] (a : S) (p : R[X]) :
    degree (a • p) ≤ degree p := by
  refine (degree_le_iff_coeff_zero _ _).2 fun m hm => ?_
  rw [degree_lt_iff_coeff_zero] at hm
  simp [hm m le_rfl]

theorem natDegree_smul_le {S : Type*} [SMulZeroClass S R] (a : S) (p : R[X]) :
    natDegree (a • p) ≤ natDegree p :=
  natDegree_le_natDegree (degree_smul_le a p)

theorem degree_smul_of_isRightRegular_leadingCoeff (ha : a ≠ 0)
    (hp : IsRightRegular p.leadingCoeff) : (a • p).degree = p.degree := by
  refine le_antisymm (degree_smul_le a p) <| degree_le_degree ?_
  rw [coeff_smul, coeff_natDegree, smul_eq_mul, ne_eq]
  exact hp.mul_right_eq_zero_iff.ne.mpr ha

theorem degree_lt_degree_mul_X (hp : p ≠ 0) : p.degree < (p * X).degree := by
  haveI := Nontrivial.of_polynomial_ne hp
  have : leadingCoeff p * leadingCoeff X ≠ 0 := by simpa
  rw [degree_mul' this, degree_eq_natDegree hp, degree_X, ← Nat.cast_one, ← Nat.cast_add]
  norm_cast
  exact Nat.lt_succ_self _

theorem eq_C_of_natDegree_le_zero (h : natDegree p ≤ 0) : p = C (coeff p 0) :=
  eq_C_of_degree_le_zero <| degree_le_of_natDegree_le h

theorem eq_C_of_natDegree_eq_zero (h : natDegree p = 0) : p = C (coeff p 0) :=
  eq_C_of_natDegree_le_zero h.le

lemma natDegree_eq_zero {p : R[X]} : p.natDegree = 0 ↔ ∃ x, C x = p :=
  ⟨fun h ↦ ⟨_, (eq_C_of_natDegree_eq_zero h).symm⟩, by aesop⟩

theorem eq_C_coeff_zero_iff_natDegree_eq_zero : p = C (p.coeff 0) ↔ p.natDegree = 0 :=
  ⟨fun h ↦ by rw [h, natDegree_C], eq_C_of_natDegree_eq_zero⟩

theorem eq_one_of_monic_natDegree_zero (hf : p.Monic) (hfd : p.natDegree = 0) : p = 1 := by
  rw [Monic.def, leadingCoeff, hfd] at hf
  rw [eq_C_of_natDegree_eq_zero hfd, hf, map_one]

theorem Monic.natDegree_eq_zero (hf : p.Monic) : p.natDegree = 0 ↔ p = 1 :=
  ⟨eq_one_of_monic_natDegree_zero hf, by rintro rfl; simp⟩

theorem degree_sum_fin_lt {n : ℕ} (f : Fin n → R) :
    degree (∑ i : Fin n, C (f i) * X ^ (i : ℕ)) < n :=
  (degree_sum_le _ _).trans_lt <|
    (Finset.sup_lt_iff <| WithBot.bot_lt_coe n).2 fun k _hk =>
      (degree_C_mul_X_pow_le _ _).trans_lt <| WithBot.coe_lt_coe.2 k.is_lt

theorem degree_C_lt_degree_C_mul_X (ha : a ≠ 0) : degree (C b) < degree (C a * X) := by
  simpa only [degree_C_mul_X ha] using degree_C_lt

end Semiring

section NontrivialSemiring

variable [Semiring R] [Nontrivial R] {p q : R[X]} (n : ℕ)

@[simp] lemma natDegree_mul_X (hp : p ≠ 0) : natDegree (p * X) = natDegree p + 1 := by
  rw [natDegree_mul' (by simpa), natDegree_X]

@[simp] lemma natDegree_X_mul (hp : p ≠ 0) : natDegree (X * p) = natDegree p + 1 := by
  rw [commute_X p, natDegree_mul_X hp]

@[simp] lemma natDegree_mul_X_pow (hp : p ≠ 0) : natDegree (p * X ^ n) = natDegree p + n := by
  rw [natDegree_mul' (by simpa), natDegree_X_pow]

@[simp] lemma natDegree_X_pow_mul (hp : p ≠ 0) : natDegree (X ^ n * p) = natDegree p + n := by
  rw [commute_X_pow, natDegree_mul_X_pow n hp]

--  This lemma explicitly does not require the `Nontrivial R` assumption.
theorem natDegree_X_pow_le {R : Type*} [Semiring R] (n : ℕ) : (X ^ n : R[X]).natDegree ≤ n := by
  nontriviality R
  rw [Polynomial.natDegree_X_pow]

theorem not_isUnit_X : ¬IsUnit (X : R[X]) := fun ⟨⟨_, g, _hfg, hgf⟩, rfl⟩ =>
  zero_ne_one' R <| by
    rw [← coeff_one_zero, ← hgf]
    simp

@[simp]
theorem degree_mul_X : degree (p * X) = degree p + 1 := by simp [monic_X.degree_mul]

@[simp]
theorem degree_mul_X_pow : degree (p * X ^ n) = degree p + n := by simp [(monic_X_pow n).degree_mul]

end NontrivialSemiring

section Ring

variable [Ring R] {p q : R[X]}

theorem degree_sub_C (hp : 0 < degree p) : degree (p - C a) = degree p := by
  rw [sub_eq_add_neg, ← C_neg, degree_add_C hp]

@[simp]
theorem natDegree_sub_C {a : R} : natDegree (p - C a) = natDegree p := by
  rw [sub_eq_add_neg, ← C_neg, natDegree_add_C]

theorem leadingCoeff_sub_of_degree_lt (h : Polynomial.degree q < Polynomial.degree p) :
    (p - q).leadingCoeff = p.leadingCoeff := by
  rw [← q.degree_neg] at h
  rw [sub_eq_add_neg, leadingCoeff_add_of_degree_lt' h]

theorem leadingCoeff_sub_of_degree_lt' (h : Polynomial.degree p < Polynomial.degree q) :
    (p - q).leadingCoeff = -q.leadingCoeff := by
  rw [← q.degree_neg] at h
  rw [sub_eq_add_neg, leadingCoeff_add_of_degree_lt h, leadingCoeff_neg]

theorem leadingCoeff_sub_of_degree_eq (h : degree p = degree q)
    (hlc : leadingCoeff p ≠ leadingCoeff q) :
    leadingCoeff (p - q) = leadingCoeff p - leadingCoeff q := by
  replace h : degree p = degree (-q) := by rwa [q.degree_neg]
  replace hlc : leadingCoeff p + leadingCoeff (-q) ≠ 0 := by
    rwa [← sub_ne_zero, sub_eq_add_neg, ← q.leadingCoeff_neg] at hlc
  rw [sub_eq_add_neg, leadingCoeff_add_of_degree_eq h hlc, leadingCoeff_neg, sub_eq_add_neg]

theorem degree_sub_eq_left_of_degree_lt (h : degree q < degree p) : degree (p - q) = degree p := by
  rw [← degree_neg q] at h
  rw [sub_eq_add_neg, degree_add_eq_left_of_degree_lt h]

theorem degree_sub_eq_right_of_degree_lt (h : degree p < degree q) : degree (p - q) = degree q := by
  rw [← degree_neg q] at h
  rw [sub_eq_add_neg, degree_add_eq_right_of_degree_lt h, degree_neg]

theorem natDegree_sub_eq_left_of_natDegree_lt (h : natDegree q < natDegree p) :
    natDegree (p - q) = natDegree p :=
  natDegree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt (degree_lt_degree h))

theorem natDegree_sub_eq_right_of_natDegree_lt (h : natDegree p < natDegree q) :
    natDegree (p - q) = natDegree q :=
  natDegree_eq_of_degree_eq (degree_sub_eq_right_of_degree_lt (degree_lt_degree h))

end Ring

section NonzeroRing

variable [Nontrivial R]

section Semiring

variable [Semiring R]

@[simp]
theorem degree_X_add_C (a : R) : degree (X + C a) = 1 := by
  have : degree (C a) < degree (X : R[X]) :=
    calc
      degree (C a) ≤ 0 := degree_C_le
      _ < 1 := WithBot.coe_lt_coe.mpr zero_lt_one
      _ = degree X := degree_X.symm
  rw [degree_add_eq_left_of_degree_lt this, degree_X]

theorem natDegree_X_add_C (x : R) : (X + C x).natDegree = 1 :=
  natDegree_eq_of_degree_eq_some <| degree_X_add_C x

@[simp]
theorem nextCoeff_X_add_C [Semiring S] (c : S) : nextCoeff (X + C c) = c := by
  nontriviality S
  simp [nextCoeff_of_natDegree_pos]

theorem degree_X_pow_add_C {n : ℕ} (hn : 0 < n) (a : R) : degree ((X : R[X]) ^ n + C a) = n := by
  have : degree (C a) < degree ((X : R[X]) ^ n) := degree_C_le.trans_lt <| by
    rwa [degree_X_pow, Nat.cast_pos]
  rw [degree_add_eq_left_of_degree_lt this, degree_X_pow]

theorem X_pow_add_C_ne_zero {n : ℕ} (hn : 0 < n) (a : R) : (X : R[X]) ^ n + C a ≠ 0 :=
  mt degree_eq_bot.2
    (show degree ((X : R[X]) ^ n + C a) ≠ ⊥ by
      rw [degree_X_pow_add_C hn a]; exact WithBot.coe_ne_bot)

theorem X_add_C_ne_zero (r : R) : X + C r ≠ 0 :=
  pow_one (X : R[X]) ▸ X_pow_add_C_ne_zero zero_lt_one r

theorem zero_notMem_multiset_map_X_add_C {α : Type*} (m : Multiset α) (f : α → R) :
    (0 : R[X]) ∉ m.map fun a => X + C (f a) := fun mem =>
  let ⟨_a, _, ha⟩ := Multiset.mem_map.mp mem
  X_add_C_ne_zero _ ha

@[deprecated (since := "2025-05-24")]
alias zero_nmem_multiset_map_X_add_C := zero_notMem_multiset_map_X_add_C

theorem natDegree_X_pow_add_C {n : ℕ} {r : R} : (X ^ n + C r).natDegree = n := by
  simp

theorem X_pow_add_C_ne_one {n : ℕ} (hn : 0 < n) (a : R) : (X : R[X]) ^ n + C a ≠ 1 := fun h =>
  hn.ne' <| by simpa only [natDegree_X_pow_add_C, natDegree_one] using congr_arg natDegree h

theorem X_add_C_ne_one (r : R) : X + C r ≠ 1 :=
  pow_one (X : R[X]) ▸ X_pow_add_C_ne_one zero_lt_one r

end Semiring

end NonzeroRing

section Semiring

variable [Semiring R]

@[simp]
theorem leadingCoeff_X_pow_add_C {n : ℕ} (hn : 0 < n) {r : R} :
    (X ^ n + C r).leadingCoeff = 1 := by
  nontriviality R
  rw [leadingCoeff, natDegree_X_pow_add_C, coeff_add, coeff_X_pow_self, coeff_C,
    if_neg (pos_iff_ne_zero.mp hn), add_zero]

@[simp]
theorem leadingCoeff_X_add_C [Semiring S] (r : S) : (X + C r).leadingCoeff = 1 := by
  rw [← pow_one (X : S[X]), leadingCoeff_X_pow_add_C zero_lt_one]

@[simp]
theorem leadingCoeff_X_pow_add_one {n : ℕ} (hn : 0 < n) : (X ^ n + 1 : R[X]).leadingCoeff = 1 :=
  leadingCoeff_X_pow_add_C hn

@[simp]
theorem leadingCoeff_pow_X_add_C (r : R) (i : ℕ) : leadingCoeff ((X + C r) ^ i) = 1 := by
  nontriviality
  rw [leadingCoeff_pow'] <;> simp

variable [NoZeroDivisors R] {p q : R[X]}

@[simp]
lemma degree_mul : degree (p * q) = degree p + degree q :=
  letI := Classical.decEq R
  if hp0 : p = 0 then by simp only [hp0, degree_zero, zero_mul, WithBot.bot_add]
  else
    if hq0 : q = 0 then by simp only [hq0, degree_zero, mul_zero, WithBot.add_bot]
    else degree_mul' <| mul_ne_zero (mt leadingCoeff_eq_zero.1 hp0) (mt leadingCoeff_eq_zero.1 hq0)

/-- `degree` as a monoid homomorphism between `R[X]` and `Multiplicative (WithBot ℕ)`.
  This is useful to prove results about multiplication and degree. -/
def degreeMonoidHom [Nontrivial R] : R[X] →* Multiplicative (WithBot ℕ) where
  toFun := degree
  map_one' := degree_one
  map_mul' _ _ := degree_mul

@[simp]
lemma degree_pow [Nontrivial R] (p : R[X]) (n : ℕ) : degree (p ^ n) = n • degree p :=
  map_pow (@degreeMonoidHom R _ _ _) _ _

@[simp]
lemma leadingCoeff_mul (p q : R[X]) : leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q := by
  by_cases hp : p = 0
  · simp only [hp, zero_mul, leadingCoeff_zero]
  · by_cases hq : q = 0
    · simp only [hq, mul_zero, leadingCoeff_zero]
    · rw [leadingCoeff_mul']
      exact mul_ne_zero (mt leadingCoeff_eq_zero.1 hp) (mt leadingCoeff_eq_zero.1 hq)

/-- `Polynomial.leadingCoeff` bundled as a `MonoidHom` when `R` has `NoZeroDivisors`, and thus
  `leadingCoeff` is multiplicative -/
def leadingCoeffHom : R[X] →* R where
  toFun := leadingCoeff
  map_one' := by simp
  map_mul' := leadingCoeff_mul

@[simp]
lemma leadingCoeffHom_apply (p : R[X]) : leadingCoeffHom p = leadingCoeff p :=
  rfl

@[simp]
lemma leadingCoeff_pow (p : R[X]) (n : ℕ) : leadingCoeff (p ^ n) = leadingCoeff p ^ n :=
  (leadingCoeffHom : R[X] →* R).map_pow p n

lemma leadingCoeff_dvd_leadingCoeff {a p : R[X]} (hap : a ∣ p) :
    a.leadingCoeff ∣ p.leadingCoeff :=
  map_dvd leadingCoeffHom hap

lemma degree_le_mul_left (p : R[X]) (hq : q ≠ 0) : degree p ≤ degree (p * q) := by
  classical
  obtain rfl | hp := eq_or_ne p 0
  · simp
  · rw [degree_mul, degree_eq_natDegree hp, degree_eq_natDegree hq]
    exact WithBot.coe_le_coe.2 (Nat.le_add_right _ _)

end Semiring

section CommSemiring
variable [CommSemiring R] {a p : R[X]} (hp : p.Monic)
include hp

lemma Monic.natDegree_pos : 0 < natDegree p ↔ p ≠ 1 :=
  Nat.pos_iff_ne_zero.trans hp.natDegree_eq_zero.not

lemma Monic.degree_pos : 0 < degree p ↔ p ≠ 1 :=
  natDegree_pos_iff_degree_pos.symm.trans hp.natDegree_pos

end CommSemiring

section Ring

variable [Ring R]

@[simp]
theorem leadingCoeff_X_pow_sub_C {n : ℕ} (hn : 0 < n) {r : R} :
    (X ^ n - C r).leadingCoeff = 1 := by
  rw [sub_eq_add_neg, ← map_neg C r, leadingCoeff_X_pow_add_C hn]

@[simp]
theorem leadingCoeff_X_pow_sub_one {n : ℕ} (hn : 0 < n) : (X ^ n - 1 : R[X]).leadingCoeff = 1 :=
  leadingCoeff_X_pow_sub_C hn

variable [Nontrivial R]

@[simp]
theorem degree_X_sub_C (a : R) : degree (X - C a) = 1 := by
  rw [sub_eq_add_neg, ← map_neg C a, degree_X_add_C]

theorem natDegree_X_sub_C (x : R) : (X - C x).natDegree = 1 := by
  rw [natDegree_sub_C, natDegree_X]

@[simp]
theorem nextCoeff_X_sub_C [Ring S] (c : S) : nextCoeff (X - C c) = -c := by
  rw [sub_eq_add_neg, ← map_neg C c, nextCoeff_X_add_C]

theorem degree_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : R) : degree ((X : R[X]) ^ n - C a) = n := by
  rw [sub_eq_add_neg, ← map_neg C a, degree_X_pow_add_C hn]

theorem X_pow_sub_C_ne_zero {n : ℕ} (hn : 0 < n) (a : R) : (X : R[X]) ^ n - C a ≠ 0 := by
  rw [sub_eq_add_neg, ← map_neg C a]
  exact X_pow_add_C_ne_zero hn _

theorem X_sub_C_ne_zero (r : R) : X - C r ≠ 0 :=
  pow_one (X : R[X]) ▸ X_pow_sub_C_ne_zero zero_lt_one r

theorem zero_notMem_multiset_map_X_sub_C {α : Type*} (m : Multiset α) (f : α → R) :
    (0 : R[X]) ∉ m.map fun a => X - C (f a) := fun mem =>
  let ⟨_a, _, ha⟩ := Multiset.mem_map.mp mem
  X_sub_C_ne_zero _ ha

@[deprecated (since := "2025-05-24")]
alias zero_nmem_multiset_map_X_sub_C := zero_notMem_multiset_map_X_sub_C

theorem natDegree_X_pow_sub_C {n : ℕ} {r : R} : (X ^ n - C r).natDegree = n := by
  rw [sub_eq_add_neg, ← map_neg C r, natDegree_X_pow_add_C]

@[simp]
theorem leadingCoeff_X_sub_C [Ring S] (r : S) : (X - C r).leadingCoeff = 1 := by
  rw [sub_eq_add_neg, ← map_neg C r, leadingCoeff_X_add_C]

end Ring
end Polynomial
