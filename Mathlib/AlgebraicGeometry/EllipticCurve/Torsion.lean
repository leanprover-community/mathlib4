/-
Copyright (c) 2023 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Point

/-!
# Torsion points on Weierstrass curves
-/

universe u

namespace WeierstrassCurve

open Polynomial

open scoped Polynomial PolynomialPolynomial

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

noncomputable def divisionPolynomial : ℕ → (R[X][Y])
| 0       => 0
| 1       => 1
| 2       => Y - W.negPolynomial
| 3       => C <| 3 * X ^ 4 + C W.b₂ * X ^ 3 + 3 * C W.b₄ * X ^ 2 + 3 * C W.b₆ * X + C W.b₈
| 4       => (Y - W.negPolynomial)
  * C (2 * X ^ 6 + C W.b₂ * X ^ 5 + 5 * C W.b₄ * X ^ 4 + 10 * C W.b₆ * X ^ 3 + 10 * C W.b₈ * X ^ 2
        + C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X + C (W.b₄ * W.b₈ - W.b₆ ^ 2))
| (n + 5) =>
if hn : Even n then
  let m := ((even_iff_exists_two_mul n).mp hn).choose
  have h4 : m + 4 < n + 5 :=
    by linarith only [show n = 2 * m by exact ((even_iff_exists_two_mul n).mp hn).choose_spec]
  have h3 : m + 3 < n + 5 := (lt_add_one _).trans h4
  have h2 : m + 2 < n + 5 := (lt_add_one _).trans h3
  have h1 : m + 1 < n + 5 := (lt_add_one _).trans h2
  divisionPolynomial (m + 4) * divisionPolynomial (m + 2) ^ 3
    - divisionPolynomial (m + 1) * divisionPolynomial (m + 3) ^ 3
else
  let m := (Nat.odd_iff_not_even.mpr hn).choose
  have h : m < n :=
    by linarith only [show n = 2 * m + 1 by exact (Nat.odd_iff_not_even.mpr hn).choose_spec]
  have h5 : m + 5 < n + 5 := add_lt_add_right h 5
  have h4 : m + 4 < n + 5 := (lt_add_one _).trans h5
  have h3 : m + 3 < n + 5 := (lt_add_one _).trans h4
  have h2 : m + 2 < n + 5 := (lt_add_one _).trans h3
  have h1 : m + 1 < n + 5 := (lt_add_one _).trans h2
  Ring.divide
    (divisionPolynomial (m + 2) ^ 2 * divisionPolynomial (m + 3) * divisionPolynomial (m + 5)
      - divisionPolynomial (m + 1) * divisionPolynomial (m + 3) * divisionPolynomial (m + 4) ^ 2)
    (Y - W.negPolynomial)

@[simp]
lemma divisionPolynomial_zero : W.divisionPolynomial 0 = 0 :=
  rfl

@[simp]
lemma divisionPolynomial_one : W.divisionPolynomial 1 = 1 :=
  rfl

@[simp]
lemma divisionPolynomial_two : W.divisionPolynomial 2 = Y - W.negPolynomial :=
  rfl

@[simp]
lemma divisionPolynomial_three :
    W.divisionPolynomial 3 =
      C (3 * X ^ 4 + C W.b₂ * X ^ 3 + 3 * C W.b₄ * X ^ 2 + 3 * C W.b₆ * X + C W.b₈) :=
  rfl

@[simp]
lemma divisionPolynomial_four :
    W.divisionPolynomial 4 =
      (Y - W.negPolynomial)
        * C (2 * X ^ 6 + C W.b₂ * X ^ 5 + 5 * C W.b₄ * X ^ 4 + 10 * C W.b₆ * X ^ 3
              + 10 * C W.b₈ * X ^ 2 + C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X
              + C (W.b₄ * W.b₈ - W.b₆ ^ 2)) :=
  rfl

@[simp]
lemma divisionPolynomial_odd (m : ℕ) :
    W.divisionPolynomial (2 * (m + 2) + 1) =
      W.divisionPolynomial (m + 4) * W.divisionPolynomial (m + 2) ^ 3
        - W.divisionPolynomial (m + 1) * W.divisionPolynomial (m + 3) ^ 3 := by
  erw [divisionPolynomial, dif_pos <| even_two_mul m]
  simp only [← (mul_right_inj' two_ne_zero).mp (⟨m, rfl⟩ : ∃ n : ℕ, 2 * m = 2 * n).choose_spec]

@[simp]
lemma divisionPolynomial_even (m : ℕ) :
    W.divisionPolynomial (2 * (m + 3)) =
      Ring.divide
        (W.divisionPolynomial (m + 2) ^ 2 * W.divisionPolynomial (m + 3)
            * W.divisionPolynomial (m + 5)
          - W.divisionPolynomial (m + 1) * W.divisionPolynomial (m + 3)
              * W.divisionPolynomial (m + 4) ^ 2)
        (Y - W.negPolynomial) := by
  erw [divisionPolynomial, dif_neg <| Nat.odd_iff_not_even.mp <| odd_two_mul_add_one m]
  simp only [← (mul_right_inj' two_ne_zero).mp <|
    Nat.succ_injective (odd_two_mul_add_one m).choose_spec]

private
lemma even_rw (y p1 p2 p3 p4 p5 : R) :
    (y * p2) ^ 2 * p3 * p5 - p1 * p3 * (y * p4) ^ 2 =
      y * (y * (p2 ^ 2 * p3 * p5 - p1 * p3 * p4 ^ 2)) := by
  ring1

private
lemma odd_rw (y p1 p2 p3 p4 p5 : R) :
    p2 ^ 2 * (y * p3) * (y * p5) - (y * p1) * (y * p3) * p4 ^ 2 =
      y * (y * (p2 ^ 2 * p3 * p5 - p1 * p3 * p4 ^ 2)) := by
  ring1

set_option maxHeartbeats 500000 in
lemma dvd_divisionPolynomial_even [IsDomain R] (m : ℕ) :
    Y - W.negPolynomial ∣ W.divisionPolynomial (2 * m) := by
  suffices ∀ {n : ℕ}, Even n → Y - W.negPolynomial ∣ W.divisionPolynomial n by
    exact this <| even_two_mul _
  intro n hn
  induction' n using Nat.strongRec' with n ih
  rcases hn with ⟨n, rfl⟩
  rcases n with _ | _ | _ | n
  · exact ⟨0, by rw [mul_zero, W.divisionPolynomial_zero]⟩
  · exact ⟨1, by rw [mul_one, W.divisionPolynomial_two]⟩
  · exact ⟨_, W.divisionPolynomial_four⟩
  · rw [show n + 3 + (n + 3) = 2 * n + 6 by exact (two_mul <| n + 3).symm] at ih ⊢
    rw [divisionPolynomial]
    simp only [dif_neg <| Nat.odd_iff_not_even.mp <| odd_two_mul_add_one n,
      ← (mul_right_inj' two_ne_zero).mp <| Nat.succ_injective (odd_two_mul_add_one n).choose_spec]
    rcases n.even_or_odd' with ⟨n, rfl | rfl⟩
    · cases' ih (2 * n + 2) (by linarith only) (even_two_mul <| n + 1) with _ h2
      cases' ih (2 * n + 4) (by linarith only) (even_two_mul <| n + 2) with _ h4
      rw [h2, h4, even_rw]
      by_cases hY : Y - W.negPolynomial = 0
      · rw [hY, zero_mul, Ring.divide_zero]
      · simpa only [Ring.mul_divide_cancel_left hY] using dvd_mul_right _ _
    · cases' ih (2 * n + 1 + 1) (by linarith only) (even_two_mul <| n + 1) with _ h1
      cases' ih (2 * n + 1 + 3) (by linarith only) (even_two_mul <| n + 2) with _ h3
      cases' ih (2 * n + 1 + 5) (by linarith only) (even_two_mul <| n + 3) with _ h5
      rw [h1, h3, h5, odd_rw]
      by_cases hY : Y - W.negPolynomial = 0
      · rw [hY, zero_mul, Ring.divide_zero]
      · simpa only [Ring.mul_divide_cancel_left hY] using dvd_mul_right _ _

lemma mul_divisionPolynomial_even [IsDomain R] (m : ℕ) :
    (Y - W.negPolynomial) * W.divisionPolynomial (2 * (m + 3)) =
      W.divisionPolynomial (m + 2) ^ 2 * W.divisionPolynomial (m + 3) * W.divisionPolynomial (m + 5)
        - W.divisionPolynomial (m + 1) * W.divisionPolynomial (m + 3)
            * W.divisionPolynomial (m + 4) ^ 2 := by
  rw [divisionPolynomial_even]
  rcases m.even_or_odd' with ⟨m, rfl | rfl⟩
  · rw [show 2 * m + 2 = 2 * (m + 1) by rfl, show 2 * m + 4 = 2 * (m + 2) by rfl,
        (W.dvd_divisionPolynomial_even $ m + 1).choose_spec,
        (W.dvd_divisionPolynomial_even $ m + 2).choose_spec, even_rw]
    by_cases hY : Y - W.negPolynomial = 0
    · simp only [hY, zero_mul]
    · rw [Ring.mul_divide_cancel hY]
      exact dvd_mul_right _ _
  · rw [show 2 * m + 1 + 1 = 2 * (m + 1) by rfl, show 2 * m + 1 + 3 = 2 * (m + 2) by rfl,
        show 2 * m + 1 + 5 = 2 * (m + 3) by rfl,
        (W.dvd_divisionPolynomial_even $ m + 1).choose_spec,
        (W.dvd_divisionPolynomial_even $ m + 2).choose_spec,
        (W.dvd_divisionPolynomial_even $ m + 3).choose_spec, odd_rw]
    by_cases hY : Y - W.negPolynomial = 0
    · simp only [hY, zero_mul]
    · rw [Ring.mul_divide_cancel hY]
      exact dvd_mul_right _ _

noncomputable
def divisionPolynomial' : ℤ → (R[X][Y])
| Int.ofNat n   => W.divisionPolynomial n
| Int.negSucc n => -W.divisionPolynomial (n + 1)

@[simp]
lemma divisionPolynomial'_nat (n : ℕ) : W.divisionPolynomial' n = W.divisionPolynomial n :=
  rfl

@[simp]
lemma divisionPolynomial'_neg (n : ℕ) : W.divisionPolynomial' (-n) = -W.divisionPolynomial n := by
  cases n
  · erw [Int.neg_zero, divisionPolynomial'_nat, W.divisionPolynomial_zero, neg_zero]
  · rfl

end WeierstrassCurve
