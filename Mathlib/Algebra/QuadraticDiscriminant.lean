/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou

! This file was ported from Lean 3 source module algebra.quadratic_discriminant
! leanprover-community/mathlib commit 829895f162a1f29d0133f4b3538f4cd1fb5bffd3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.CharP.Invertible
import Mathbin.Order.Filter.AtTopBot
import Mathbin.Tactic.Linarith.Default
import Mathbin.Tactic.FieldSimp
import Mathbin.Tactic.LinearCombination

/-!
# Quadratic discriminants and roots of a quadratic

This file defines the discriminant of a quadratic and gives the solution to a quadratic equation.

## Main definition

- `discrim a b c`: the discriminant of a quadratic `a * x * x + b * x + c` is `b * b - 4 * a * c`.

## Main statements

- `quadratic_eq_zero_iff`: roots of a quadratic can be written as
  `(-b + s) / (2 * a)` or `(-b - s) / (2 * a)`, where `s` is a square root of the discriminant.
- `quadratic_ne_zero_of_discrim_ne_sq`: if the discriminant has no square root,
  then the corresponding quadratic has no root.
- `discrim_le_zero`: if a quadratic is always non-negative, then its discriminant is non-positive.

## Tags

polynomial, quadratic, discriminant, root
-/


open Filter

section Ring

variable {R : Type _}

/-- Discriminant of a quadratic -/
def discrim [Ring R] (a b c : R) : R :=
  b ^ 2 - 4 * a * c
#align discrim discrim

variable [CommRing R] [IsDomain R] {a b c : R}

/-- A quadratic has roots if and only if its discriminant equals some square.
-/
theorem quadratic_eq_zero_iff_discrim_eq_sq (h2 : (2 : R) ≠ 0) (ha : a ≠ 0) (x : R) :
    a * x * x + b * x + c = 0 ↔ discrim a b c = (2 * a * x + b) ^ 2 :=
  by
  dsimp [discrim] at *
  constructor
  · intro h
    linear_combination -4 * a * h
  · intro h
    have ha : 2 * 2 * a ≠ 0 := mul_ne_zero (mul_ne_zero h2 h2) ha
    apply mul_left_cancel₀ ha
    linear_combination -h
#align quadratic_eq_zero_iff_discrim_eq_sq quadratic_eq_zero_iff_discrim_eq_sq

/-- A quadratic has no root if its discriminant has no square root. -/
theorem quadratic_ne_zero_of_discrim_ne_sq (h2 : (2 : R) ≠ 0) (ha : a ≠ 0)
    (h : ∀ s : R, discrim a b c ≠ s * s) (x : R) : a * x * x + b * x + c ≠ 0 :=
  by
  intro h'
  rw [quadratic_eq_zero_iff_discrim_eq_sq h2 ha, sq] at h'
  exact h _ h'
#align quadratic_ne_zero_of_discrim_ne_sq quadratic_ne_zero_of_discrim_ne_sq

end Ring

section Field

variable {K : Type _} [Field K] [Invertible (2 : K)] {a b c x : K}

/-- Roots of a quadratic -/
theorem quadratic_eq_zero_iff (ha : a ≠ 0) {s : K} (h : discrim a b c = s * s) (x : K) :
    a * x * x + b * x + c = 0 ↔ x = (-b + s) / (2 * a) ∨ x = (-b - s) / (2 * a) :=
  by
  have h2 : (2 : K) ≠ 0 := nonzero_of_invertible 2
  rw [quadratic_eq_zero_iff_discrim_eq_sq h2 ha, h, sq, mul_self_eq_mul_self_iff]
  have ne : 2 * a ≠ 0 := mul_ne_zero h2 ha
  field_simp
  apply or_congr
  · constructor <;> intro h' <;> linear_combination -h'
  · constructor <;> intro h' <;> linear_combination h'
#align quadratic_eq_zero_iff quadratic_eq_zero_iff

/-- A quadratic has roots if its discriminant has square roots -/
theorem exists_quadratic_eq_zero (ha : a ≠ 0) (h : ∃ s, discrim a b c = s * s) :
    ∃ x, a * x * x + b * x + c = 0 := by
  rcases h with ⟨s, hs⟩
  use (-b + s) / (2 * a)
  rw [quadratic_eq_zero_iff ha hs]
  simp
#align exists_quadratic_eq_zero exists_quadratic_eq_zero

/-- Root of a quadratic when its discriminant equals zero -/
theorem quadratic_eq_zero_iff_of_discrim_eq_zero (ha : a ≠ 0) (h : discrim a b c = 0) (x : K) :
    a * x * x + b * x + c = 0 ↔ x = -b / (2 * a) :=
  by
  have : discrim a b c = 0 * 0 := by rw [h, MulZeroClass.mul_zero]
  rw [quadratic_eq_zero_iff ha this, add_zero, sub_zero, or_self_iff]
#align quadratic_eq_zero_iff_of_discrim_eq_zero quadratic_eq_zero_iff_of_discrim_eq_zero

end Field

section LinearOrderedField

variable {K : Type _} [LinearOrderedField K] {a b c : K}

/-- If a polynomial of degree 2 is always nonnegative, then its discriminant is nonpositive -/
theorem discrim_le_zero (h : ∀ x : K, 0 ≤ a * x * x + b * x + c) : discrim a b c ≤ 0 :=
  by
  rw [discrim, sq]
  obtain ha | rfl | ha : a < 0 ∨ a = 0 ∨ 0 < a := lt_trichotomy a 0
  -- if a < 0
  · have : tendsto (fun x => (a * x + b) * x + c) at_top at_bot :=
      tendsto_at_bot_add_const_right _ c
        ((tendsto_at_bot_add_const_right _ b (tendsto_id.neg_const_mul_at_top ha)).atBot_mul_atTop
          tendsto_id)
    rcases(this.eventually (eventually_lt_at_bot 0)).exists with ⟨x, hx⟩
    exact False.elim ((h x).not_lt <| by rwa [← add_mul])
  -- if a = 0
  · rcases em (b = 0) with (rfl | hb)
    · simp
    · have := h ((-c - 1) / b)
      rw [mul_div_cancel' _ hb] at this
      linarith
  -- if a > 0
  · have :=
      calc
        4 * a * (a * (-(b / a) * (1 / 2)) * (-(b / a) * (1 / 2)) + b * (-(b / a) * (1 / 2)) + c) =
            a * (b / a) * (a * (b / a)) - 2 * (a * (b / a)) * b + 4 * a * c :=
          by ring
        _ = -(b * b - 4 * a * c) :=
          by
          simp only [mul_div_cancel' b (ne_of_gt ha)]
          ring
        
    have ha' : 0 ≤ 4 * a := by linarith
    have h := mul_nonneg ha' (h (-(b / a) * (1 / 2)))
    rw [this] at h
    rwa [← neg_nonneg]
#align discrim_le_zero discrim_le_zero

/-- If a polynomial of degree 2 is always positive, then its discriminant is negative,
at least when the coefficient of the quadratic term is nonzero.
-/
theorem discrim_lt_zero (ha : a ≠ 0) (h : ∀ x : K, 0 < a * x * x + b * x + c) : discrim a b c < 0 :=
  by
  have : ∀ x : K, 0 ≤ a * x * x + b * x + c := fun x => le_of_lt (h x)
  refine' lt_of_le_of_ne (discrim_le_zero this) _
  intro h'
  have := h (-b / (2 * a))
  have : a * (-b / (2 * a)) * (-b / (2 * a)) + b * (-b / (2 * a)) + c = 0 := by
    rw [quadratic_eq_zero_iff_of_discrim_eq_zero ha h' (-b / (2 * a))]
  linarith
#align discrim_lt_zero discrim_lt_zero

end LinearOrderedField

