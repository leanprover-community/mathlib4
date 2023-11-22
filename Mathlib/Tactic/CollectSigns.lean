/-
Copyright (c) 2023 Miguel Marco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel Marco
-/
import Init.Data.Nat.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Tactic.FieldSimp

/-!
# `collect_signs` and `collect_signs!` tactics.

The `collect_signs` tactic rewrites expression combining additions and substractions into
an expression with only additions minus annother expression with only additions.


The `collect_signs!` tactic extends `collect_signs`, trying to cancel additions and
substractions of naturals, adding the necessary inequalities as new goals.
-/

open Lean Meta Elab Tactic Parser Tactic

/--
The `collect_signs` tactic rewrites expression combining additions and substractions into
an expression with only additions minus annother expression with only additions.
--/
syntax (name := collect_signs) "collect_signs" (location)?: tactic

/-These rules either reduce the number of minus signs, fix it but push
a minus sign closer to the root of the expression tree, or fix
the minus signs but reduce the number of terms in the expression.-/
macro_rules
| `(tactic | collect_signs $[at $location]?) => `(tactic |(
  repeat (first
  | (rw [sub_self]                    $[at $location]?) -- x - x = 0
  | (rw [Nat.sub_self]                $[at $location]?) -- n - n = 0 (ℕ)
  | (rw [add_zero]                    $[at $location]?) -- x + 0 = x
  | (rw [zero_add]                    $[at $location]?) -- 0 + x = x
  | (rw [sub_zero]                    $[at $location]?) -- x - 0 = x
  | (rw [Nat.sub_zero]                $[at $location]?) -- n - 0 = n (ℕ)
  | (rw [zero_sub]                    $[at $location]?) -- 0 - x = - x
  | (rw [add_tsub_cancel_right]       $[at $location]?) -- x + y - y = x
  | (rw [add_tsub_cancel_left]        $[at $location]?) -- x + y - x = y
  | (rw [add_sub_add_left_eq_sub]     $[at $location]?) -- z + x - (z + y) = x - y
  | (rw [add_sub_add_right_eq_sub]    $[at $location]?) -- x + z - (y + z) = x - y
  | (rw [add_sub_add_cancel]          $[at $location]?) -- x + y - (z + x) = y - z
  | (rw [add_sub_add_cancel']         $[at $location]?) -- y + x - (x + z) = y - x
  | (rw [sub_sub]                     $[at $location]?) -- x - y - z = x - (y + z)
  | (rw [Nat.sub_sub]                 $[at $location]?) -- n - m - k = n - (m + k) (ℕ)
  | (rw [sub_sub_eq_add_sub]          $[at $location]?) -- x - (y - z) = x + z - y
  | (rw [sub_add, sub_sub_eq_add_sub] $[at $location]?) -- (x - y) + z = x + z - y
  | (rw [add_sub]                     $[at $location]?) -- x + (y - z) = x + y - z
  | (rw [sub_neg_eq_add]              $[at $location]?) -- x - -y = x + y
  | (rw [← sub_eq_add_neg]            $[at $location]?) -- x + -y = x - y
  | (rw [neg_add_eq_sub]              $[at $location]?) -- -x + y = x - y
  | (rw [← add_assoc]                 $[at $location]?)) -- x + (y + z) = x + y + z
  try (any_goals assumption) ))

/-These two lemmas are also used as rewriting rules later.-/
lemma Nat.sub_sub_of_le (m n k : ℕ) (h : k ≤ n) : m - (n - k) = m + k - n := by
  have haux := Nat.le.dest h
  cases haux with
  | intro d hd =>
    · rw [←hd,add_comm m k,add_tsub_cancel_left,Nat.add_sub_add_left]

lemma Nat.add_sub_comm_of_le (m n k : ℕ) (h : k ≤ n) : m + (n - k) = (m + n) - k := by
  have haux := Nat.le.dest h
  cases haux with
  | intro d hd =>
    · rw [← hd,add_comm k d,←add_assoc,add_tsub_cancel_right,add_tsub_cancel_right]

/--
The `collect_signs!` tactic extends `collect_signs`, trying to cancel additions and
substractions of naturals, adding the necessary inequalities as new goals.
--/
syntax (name := collect_signs!) "collect_signs!" (location)?: tactic

-- These rules either reduce the number of minus signs, fix it but push
-- a minus sign closer to the root of the expression tree, or fix
-- the minus signs but reduce the number of terms in the expression.
macro_rules
| `(tactic | collect_signs! $[at $location]?) => `(tactic |(
  repeat (first
  | (rw [sub_self]                    $[at $location]?) -- x - x = 0
  | (rw [Nat.sub_self]                $[at $location]?) -- n - n = 0 (ℕ)
  | (rw [add_zero]                    $[at $location]?) -- x + 0 = x
  | (rw [zero_add]                    $[at $location]?) -- 0 + x = x
  | (rw [sub_zero]                    $[at $location]?) -- x - 0 = x
  | (rw [Nat.sub_zero]                $[at $location]?) -- n - 0 = n (ℕ)
  | (rw [zero_sub]                    $[at $location]?) -- 0 - x = - x
  | (rw [add_tsub_cancel_right]       $[at $location]?) -- x + y - y = x
  | (rw [add_tsub_cancel_left]        $[at $location]?) -- x + y - x = y
  | (rw [Nat.add_sub_of_le]           $[at $location]?) -- n + (m - n) = m (ℕ)
  | (rw [Nat.sub_sub_self]            $[at $location]?) -- n - (n - m) = m (ℕ)
  | (rw [Nat.sub_sub_of_le]           $[at $location]?) -- m - (n - k) = m + k - n (ℕ)
  | (rw [Nat.add_sub_of_le]           $[at $location]?) -- m + k - (n + k) = m - n (ℕ)
  | (rw [add_sub_add_left_eq_sub]     $[at $location]?) -- z + x - (y + z) = x - y
  | (rw [add_sub_add_right_eq_sub]    $[at $location]?) -- x + z - (y + z) = x - y
  | (rw [add_sub_add_cancel]          $[at $location]?) -- x + y - (z + x) = y - z
  | (rw [add_sub_add_cancel']         $[at $location]?) -- y + x - (x + z) = y - z
  | (rw [sub_sub]                     $[at $location]?) -- x - y - z = x - (y + z)
  | (rw [Nat.sub_sub]                 $[at $location]?) -- n - m - k = n - (m + k) (ℕ)
  | (rw [sub_sub_eq_add_sub]          $[at $location]?) -- x - (y - z) = x + z - y
  | (rw [sub_add, sub_sub_eq_add_sub] $[at $location]?) -- (x - y) + z = x + z - y
  | (rw [← Nat.sub_add_comm]          $[at $location]?) -- (n - k) + m = (n + m) - k (ℕ)
  | (rw [Nat.add_sub_comm_of_le]      $[at $location]?) -- m + (n - k) = m + n - k (ℕ)
  | (rw [add_sub]                     $[at $location]?) -- x + (y - z) = x + y - z
  | (rw [sub_neg_eq_add]              $[at $location]?) -- x - -y = x + y
  | (rw [← sub_eq_add_neg]            $[at $location]?) -- x + -y = x - y
  | (rw [neg_add_eq_sub]              $[at $location]?) -- -x + y = y - x
  | (rw [← add_assoc]                 $[at $location]?) -- x + (y + z) = x + y + z
  | (rw [add_le_add_iff_left]         $[at $location]?) -- a + b ≤ a + c ↔ b ≤ c
  | (rw [add_lt_add_iff_left]         $[at $location]?) -- a + b < a + c ↔ b < c
  | (rw [add_le_add_iff_right]        $[at $location]?) -- b + a ≤ c + a ↔ b ≤ c
  | (rw [add_lt_add_iff_right]        $[at $location]?) -- b + a < c + a ↔ b < c
  | (rw [sub_le_sub_iff_left]         $[at $location]?) -- a - b ≤ a - c ↔ c ≤ b
  | (rw [sub_lt_sub_iff_left]         $[at $location]?) -- a - b < a - c ↔ c < b
  | (rw [sub_le_sub_iff_right]        $[at $location]?) -- a - c ≤ b - c ↔ a ≤ b
  | (rw [sub_lt_sub_iff_right]        $[at $location]?) -- a - c < b - c ↔ a < b
  | (rw [Nat.add_le_add_iff_left]     $[at $location]?) -- a + b ≤ a + c ↔ b ≤ c
  | (rw [Nat.add_lt_add_iff_left]     $[at $location]?) -- a + b < a + c ↔ b < c
  | (rw [Nat.add_le_add_iff_right]    $[at $location]?) -- b + a ≤ c + a ↔ b ≤ c
  | (rw [Nat.add_lt_add_iff_right]    $[at $location]?) -- b + a < c + a ↔ b < c
  | (rw [Nat.sub_le_sub_iff_left]     $[at $location]?) -- a - b ≤ a - c ↔ c ≤ b
  | (rw [Nat.sub_lt_sub_iff_left]     $[at $location]?) -- a - b < a - c ↔ c < b
  | (rw [Nat.sub_le_sub_iff_right]    $[at $location]?) -- a - c ≤ b - c ↔ a ≤ b
  | (rw [Nat.sub_lt_sub_iff_right]    $[at $location]?) -- a - c < b - c ↔ a < b
  | (simp only [add_assoc,add_le_add_iff_left]         $[at $location]?) -- a + b ≤ a + c ↔ b ≤ c
  | (simp only [add_assoc,add_lt_add_iff_left]         $[at $location]?) -- a + b < a + c ↔ b < c
  | (simp only [add_assoc,add_le_add_iff_right]        $[at $location]?) -- b + a ≤ c + a ↔ b ≤ c
  | (simp only [add_assoc,add_lt_add_iff_right]        $[at $location]?) -- b + a < c + a ↔ b < c
  | (simp only [add_assoc,sub_le_sub_iff_left]         $[at $location]?) -- a - b ≤ a - c ↔ c ≤ b
  | (simp only [add_assoc,sub_lt_sub_iff_left]         $[at $location]?) -- a - b < a - c ↔ c < b
  | (simp only [add_assoc,sub_le_sub_iff_right]        $[at $location]?) -- a - c ≤ b - c ↔ a ≤ b
  | (simp only [add_assoc,sub_lt_sub_iff_right]        $[at $location]?) -- a - c < b - c ↔ a < b
  | (simp only [add_assoc,Nat.add_le_add_iff_left]     $[at $location]?) -- a + b ≤ a + c ↔ b ≤ c
  | (simp only [add_assoc,Nat.add_lt_add_iff_left]     $[at $location]?) -- a + b < a + c ↔ b < c
  | (simp only [add_assoc,Nat.add_le_add_iff_right]    $[at $location]?) -- b + a ≤ c + a ↔ b ≤ c
  | (simp only [add_assoc,Nat.add_lt_add_iff_right]    $[at $location]?) -- b + a < c + a ↔ b < c
  | (simp only [add_assoc,Nat.sub_le_sub_iff_left]     $[at $location]?) -- a - b ≤ a - c ↔ c ≤ b
  | (simp only [add_assoc,Nat.sub_lt_sub_iff_left]     $[at $location]?) -- a - b < a - c ↔ c < b
  | (simp only [add_assoc,Nat.sub_le_sub_iff_right]    $[at $location]?) -- a - c ≤ b - c ↔ a ≤ b
  | (simp only [add_assoc,Nat.sub_lt_sub_iff_right]    $[at $location]?) -- a - c < b - c ↔ a < b
  | (rw [sub_le_iff_le_add]         $[at $location]?) --  a - c ≤ b ↔ a ≤ b + c
  | (rw [sub_lt_iff_lt_add]         $[at $location]?) --  a - c < b ↔ a < b + c
  | (rw [le_sub_iff_add_le]         $[at $location]?) -- a ≤ c - b ↔ a + b ≤ c
  | (rw [lt_sub_iff_add_lt]         $[at $location]?) -- a < c - b ↔ a + b < c
  | (rw [Nat.sub_le_iff_le_add]         $[at $location]?) -- a - b ≤ c ↔ a ≤ c + b
  | (rw [Nat.le_sub_iff_add_le]         $[at $location]?) ) -- x ≤ y - k ↔ x + k ≤ y
  try (any_goals assumption)))
