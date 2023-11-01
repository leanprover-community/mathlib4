/-
Copyright (c) 2023 Miguel Marco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Miguel Marco
-/
import Init.Data.Nat.Basic
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Data.Nat.Order.Lemmas
import Mathlib.Tactic.FieldSimp
import Std.Data.Nat.Lemmas

open Lean Meta Elab Tactic Parser Tactic

/-!
# `unify_denoms` and `unify_denoms!` tactics

Tactics to clear denominators in algebraic expressions, extends `field_simp`  using
rules that require denominators to be nonzero. The corresponding hypotheses are
added as new goals.

The `unify_denoms` tactic tries to unify denominators in expressions, adding the
necessary hypothesis about denominators being nonzero (and dividing the numerator in the case
of euclidean domains) as new goals.

The `unify_denoms!` tactic extends `unify_denoms` to work also on
(in)equalities. In the case of inequalities, it assumes denominators are positive.
--/

/-
The following lemmas are needed to manage divisions in the naturals:
-/

/--
`unify_denoms` reduces expressions with nested fractions to a single fraction.

It adds the hypothesis that the corresponding denominators are nonzero (and divide the numerator
in the case of euclidean domains) as new goals.
-/
syntax (name := unify_denoms) "unify_denoms" (location)? : tactic

macro_rules
| `(tactic | unify_denoms $[at $location]?) => `(tactic |(
  try field_simp $[at $location]?
  repeat (first
  | (rw [← one_div] $[at $location]?) -- x⁻¹ = 1 / x
  | (rw [one_mul] $[at $location]?) -- 1 * x = x
  | (rw [mul_one] $[at $location]?) -- x * 1 = x
  | (rw [mul_div_mul_right] $[at $location]?) -- a * c / (b * c) = a / b
  | (rw [mul_div_mul_left] $[at $location]?) -- c * a / (c * b) = a / b
  | (rw [div_add_div] $[at $location]?) -- a / b + c / d = (a * d + b * c) / (b * d)
  | (rw [div_sub_div] $[at $location]?) -- a / b - c / d = (a * d - b * c) / (b * d)
  | (rw [add_div'] $[at $location]?) -- b + a / c = (b * c + a) / c
  | (rw [div_add'] $[at $location]?) -- a / c + b = (a + b * c) / c
  | (rw [div_sub'] $[at $location]?) -- a / c - b = (a - c * b) / c
  | (rw [sub_div'] $[at $location]?) -- b - a / c = (b * c - a) / c
  | (rw [Nat.div_div_eq_div_mul] $[at $location]?) -- m / n / k = m / (n * k)
  | (rw [Nat.div_self] $[at $location]?) -- n / n = 1
  | (rw [Nat.one_mul] $[at $location]?) -- 1 * n = n
  | (rw [Nat.mul_one] $[at $location]?) -- n * 1 = n
  | (rw [Nat.mul_div_mul_right] $[at $location]?) -- n * m / (k * m) = n / k
  | (rw [Nat.mul_div_mul_left] $[at $location]?) -- m * n / (m * k) = n / k
  | (rw [Nat.div_add_div_of_dvd] $[at $location]?) -- m / n + k / l = (m * l + n * k) / (n * l)
  | (rw [Nat.div_sub_div_of_dvd] $[at $location]?) -- m / n - k / l = (m * l - n * k) / (n * l)
  | (rw [Nat.div_add_of_dvd] $[at $location]?) -- m / n + k = (m + n * k) / n
  | (rw [Nat.div_sub_of_dvd] $[at $location]?) -- m / n - k = (m - n * k) / n
  | (rw [Nat.add_div_of_dvd] $[at $location]?) -- m + n / k = (k * m + n) / k
  | (rw [Nat.sub_div_of_dvd] $[at $location]?) -- m - n / k = (k * m - n) / k
  | (rw [Int.div_self] $[at $location]?) -- n / n = 1
  | (rw [Int.one_mul] $[at $location]?) -- 1 * n = n
  | (rw [Int.mul_one] $[at $location]?) -- 1 * n = n
  | (rw [EuclideanDomain.mul_div_cancel] $[at $location]?) -- a * b / b = a
  | (rw [EuclideanDomain.mul_div_cancel'] $[at $location]?) -- b * (a / b) = a
  | (rw [EuclideanDomain.mul_div_cancel_left] $[at $location]?) -- a * b / a = b
  | (rw [EuclideanDomain.mul_div_mul_cancel] $[at $location]?) -- a * b / (a * c) = b / c
  | (rw [←EuclideanDomain.mul_div_assoc] $[at $location]?) -- x * (y / z) = x * y / z
  | (rw [EuclideanDomain.div_div] $[at $location]?) -- x / y / z = x / (y * z)
  | (rw [EuclideanDomain.div_add_div_of_dvd] $[at $location]?) -- x / y + z / t = (t * x + y * z) / (t * y)
  | (rw [EuclideanDomain.div_sub_div_of_dvd] $[at $location]?) -- x / y - z / t = (t * x - y * z) / (t * y)
  | (rw [EuclideanDomain.div_add_of_dvd] $[at $location]?) -- x / y + z = (x + y * z) / y
  | (rw [EuclideanDomain.div_sub_of_dvd] $[at $location]?) -- x / y - z = (x - y * z) / y
  | (rw [EuclideanDomain.add_div_of_dvd] $[at $location]?) -- x + y / z = (z * x + y) / z
  | (rw [EuclideanDomain.sub_div_of_dvd] $[at $location]?) -- x - y / z = (z * x - y) / z
  | (rw [←Nat.mul_div_assoc] $[at $location]?) -- m * (n / k) = m * n / k
  | (rw [Nat.div_mul_assoc] $[at $location]?) -- n / k * m = n * m / k
  | (rw [Nat.div_mul_div_comm] $[at $location]?) -- m * k / (n * l)
   )))

/--
`unify_denoms!` works as `unify_denoms`, but:
- it also simplifies divisions in euclidean domains, and
- it also tries to cancel denominators in both sides of an (in)equality.

The needed hypothesis about the divisibility and sign of denominators are added as new goals.
-/
syntax (name := unify_denoms!) "unify_denoms!" (location)?: tactic

macro_rules
| `(tactic | unify_denoms! $[at $location]?) => `(tactic |(
  unify_denoms $[at $location]?
  repeat (first
  | (rw [mul_eq_zero] $[at $location]?) -- a * b = 0 ↔ a = 0 ∨ b = 0
  | (rw [eq_comm,mul_eq_zero] $[at $location]?) -- 0 = a * b ↔ a = 0 ∨ b = 0
  | (rw [div_eq_zero_iff] $[at $location]?) -- a / b = 0 ↔ a = 0 ∨ b = 0
  | (rw [div_eq_div_iff] $[at $location]?) -- a / b = c / d ↔ a * d = c * b
  | (rw [gt_iff_lt] $[at $location]?) -- a > b ↔ b < a
  | (rw [ge_iff_le] $[at $location]?) -- a ≥ b ↔ b ≤ a
  | (rw [div_le_div_iff] $[at $location]?) -- a / b ≤ c / d ↔ a * d ≤ c * b
  | (rw [div_lt_div_iff] $[at $location]?) -- a / b < c / d ↔ a * d < c * b
  | (rw [div_eq_iff] $[at $location]?) -- a / b = c ↔ a = c * b
  | (rw [div_le_iff] $[at $location]?) -- a / b ≤ c ↔ a ≤ c * b
  | (rw [div_lt_iff] $[at $location]?) -- b / c < a ↔ b < a * c
  | (rw [eq_div_iff] $[at $location]?) -- a / b ↔ c * b = a
  | (rw [le_div_iff] $[at $location]?) -- a ≤ b / c ↔ a * c ≤ b
  | (rw [lt_div_iff] $[at $location]?) -- a < b / c ↔ a * c < b
  | (rw [Nat.div_eq_iff_eq_mul_left] $[at $location]?) -- a / b = c ↔ a = c * b
  | (rw [Nat.eq_div_iff_mul_eq_left] $[at $location]?) -- m = n / k ↔ n = m * k
  | (rw [eq_comm,Nat.div_eq_iff_eq_mul_left] $[at $location]?) -- c = a / b ↔ a = c * b
  | (rw [Nat.div_lt_iff_lt_mul] $[at $location]?) -- x / k < y ↔ x < y * k
  | (rw [Nat.le_div_iff_mul_le] $[at $location]?) -- x ≤ y / k ↔ x * k ≤ y
  | (rw [Nat.div_le_iff_le_mul_of_dvd] $[at $location]?) -- m / n ≤ k ↔ m ≤ k * n
  | (rw [Nat.lt_div_iff_mul_lt_of_dvd] $[at $location]?) -- m < n / k ↔ m * k < n
  | (rw [EuclideanDomain.div_eq_div_iff_mul_eq_mul_of_dvd] $[at $location]?) -- x / y = z / t ↔ t * x = y * z
  | (rw [EuclideanDomain.eq_div_iff_mul_eq_of_dvd] $[at $location]?) -- x = y / z ↔ z * x = y
  | (rw [EuclideanDomain.div_eq_iff_eq_mul_of_dvd] $[at $location]?) -- x / y = z ↔ x = y * z
  | (rw [Int.div_le_div_iff_of_dvd_of_pos] $[at $location]?) -- x / y ≤ z / t ↔ t * x ≤ z * y
  | (rw [Int.div_lt_div_iff_of_dvd_of_pos] $[at $location]?) -- x / y < z / t ↔ t * x < z * y
  | (rw [Int.div_le_iff_of_dvd_of_pos] $[at $location]?) -- x / y ≤ z ↔ x ≤ y * z
  | (rw [Int.div_lt_iff_of_dvd_of_pos] $[at $location]?) -- x / y < z ↔ x < y * z
  | (rw [Int.le_div_iff_of_dvd_of_pos] $[at $location]?) -- x ≤ y / z ↔ z * x ≤ y
  | (rw [Int.lt_div_iff_of_dvd_of_pos] $[at $location]?) -- x < y / z ↔ z * x < y
  | (push_neg $[at $location]?) )
  try (any_goals assumption) ))
