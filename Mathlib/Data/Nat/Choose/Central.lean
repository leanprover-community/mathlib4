/-
Copyright (c) 2021 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens, Thomas Browning
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Central binomial coefficients

This file proves properties of the central binomial coefficients (that is, `Nat.choose (2 * n) n`).

## Main definition and results

* `Nat.centralBinom`: the central binomial coefficient, `(2 * n).choose n`.
* `Nat.succ_mul_centralBinom_succ`: the inductive relationship between successive central binomial
  coefficients.
* `Nat.four_pow_lt_mul_centralBinom`: an exponential lower bound on the central binomial
  coefficient.
* `succ_dvd_centralBinom`: The result that `n+1 ∣ n.centralBinom`, ensuring that the explicit
  definition of the Catalan numbers is integer-valued.
-/


namespace Nat

/-- The central binomial coefficient, `Nat.choose (2 * n) n`.
-/
def centralBinom (n : ℕ) :=
  (2 * n).choose n

theorem centralBinom_eq_two_mul_choose (n : ℕ) : centralBinom n = (2 * n).choose n :=
  rfl

theorem centralBinom_pos (n : ℕ) : 0 < centralBinom n :=
  choose_pos (Nat.le_mul_of_pos_left _ zero_lt_two)

theorem centralBinom_ne_zero (n : ℕ) : centralBinom n ≠ 0 :=
  (centralBinom_pos n).ne'

@[simp]
theorem centralBinom_zero : centralBinom 0 = 1 :=
  choose_zero_right _

/-- The central binomial coefficient is the largest binomial coefficient.
-/
theorem choose_le_centralBinom (r n : ℕ) : choose (2 * n) r ≤ centralBinom n :=
  calc
    (2 * n).choose r ≤ (2 * n).choose (2 * n / 2) := choose_le_middle r (2 * n)
    _ = (2 * n).choose n := by rw [Nat.mul_div_cancel_left n zero_lt_two]

theorem two_le_centralBinom (n : ℕ) (n_pos : 0 < n) : 2 ≤ centralBinom n :=
  calc
    2 ≤ 2 * n := Nat.le_mul_of_pos_right _ n_pos
    _ = (2 * n).choose 1 := (choose_one_right (2 * n)).symm
    _ ≤ centralBinom n := choose_le_centralBinom 1 n

/-- An inductive property of the central binomial coefficient.
-/
theorem succ_mul_centralBinom_succ (n : ℕ) :
    (n + 1) * centralBinom (n + 1) = 2 * (2 * n + 1) * centralBinom n :=
  calc
    (n + 1) * (2 * (n + 1)).choose (n + 1) = (2 * n + 2).choose (n + 1) * (n + 1) := mul_comm _ _
    _ = (2 * n + 1).choose n * (2 * n + 2) := by rw [choose_succ_right_eq, choose_mul_succ_eq]
    _ = 2 * ((2 * n + 1).choose n * (n + 1)) := by ring
    _ = 2 * ((2 * n + 1).choose n * (2 * n + 1 - n)) := by rw [two_mul n, add_assoc,
                                                               Nat.add_sub_cancel_left]
    _ = 2 * ((2 * n).choose n * (2 * n + 1)) := by rw [choose_mul_succ_eq]
    _ = 2 * (2 * n + 1) * (2 * n).choose n := by rw [mul_assoc, mul_comm (2 * n + 1)]

/-- An exponential lower bound on the central binomial coefficient.
This bound is of interest because it appears in
[Tochiori's refinement of Erdős's proof of Bertrand's postulate](tochiori_bertrand).
-/
theorem four_pow_lt_mul_centralBinom (n : ℕ) (n_big : 4 ≤ n) : 4 ^ n < n * centralBinom n := by
  induction n using Nat.strong_induction_on with | _ n IH
  rcases lt_trichotomy n 4 with (hn | rfl | hn)
  · clear IH; exact False.elim ((not_lt.2 n_big) hn)
  · norm_num [centralBinom, choose]
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  calc
    4 ^ (n + 1) < 4 * (n * centralBinom n) := lt_of_eq_of_lt pow_succ' <|
      (mul_lt_mul_left <| zero_lt_four' ℕ).mpr (IH n n.lt_succ_self (Nat.le_of_lt_succ hn))
    _ ≤ 2 * (2 * n + 1) * centralBinom n := by rw [← mul_assoc]; linarith
    _ = (n + 1) * centralBinom (n + 1) := (succ_mul_centralBinom_succ n).symm

/-- An exponential lower bound on the central binomial coefficient.
This bound is weaker than `Nat.four_pow_lt_mul_centralBinom`, but it is of historical interest
because it appears in Erdős's proof of Bertrand's postulate.
-/
theorem four_pow_le_two_mul_self_mul_centralBinom :
    ∀ (n : ℕ) (_ : 0 < n), 4 ^ n ≤ 2 * n * centralBinom n
  | 0, pr => (Nat.not_lt_zero _ pr).elim
  | 1, _ => by simp [centralBinom, choose]
  | 2, _ => by simp [centralBinom, choose]
  | 3, _ => by simp [centralBinom, choose]
  | n + 4, _ =>
    calc
      4 ^ (n+4) ≤ (n+4) * centralBinom (n+4) := (four_pow_lt_mul_centralBinom _ le_add_self).le
      _ ≤ 2 * (n+4) * centralBinom (n+4) := by
        rw [mul_assoc]; refine Nat.le_mul_of_pos_left _ zero_lt_two

theorem two_dvd_centralBinom_succ (n : ℕ) : 2 ∣ centralBinom (n + 1) := by
  use (n + 1 + n).choose n
  rw [centralBinom_eq_two_mul_choose, two_mul, ← add_assoc,
      choose_succ_succ' (n + 1 + n) n, choose_symm_add, ← two_mul]

theorem two_dvd_centralBinom_of_one_le {n : ℕ} (h : 0 < n) : 2 ∣ centralBinom n := by
  rw [← Nat.succ_pred_eq_of_pos h]
  exact two_dvd_centralBinom_succ n.pred

/-- A crucial lemma to ensure that Catalan numbers can be defined via their explicit formula
  `catalan n = n.centralBinom / (n + 1)`. -/
theorem succ_dvd_centralBinom (n : ℕ) : n + 1 ∣ n.centralBinom := by
  have h_s : (n + 1).Coprime (2 * n + 1) := by
    rw [two_mul, add_assoc, coprime_add_self_right, coprime_self_add_left]
    exact coprime_one_left n
  apply h_s.dvd_of_dvd_mul_left
  apply Nat.dvd_of_mul_dvd_mul_left zero_lt_two
  rw [← mul_assoc, ← succ_mul_centralBinom_succ, mul_comm]
  exact mul_dvd_mul_left _ (two_dvd_centralBinom_succ n)

end Nat
