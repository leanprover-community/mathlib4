import Mathlib.Tactic.ApplyRules
import Std.Data.Nat.Lemmas

open Nat

example {a b c d e : Nat} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ e) :
  a + c * e + a + c + 0 ≤ b + d * e + b + d + e :=
add_le_add (add_le_add (add_le_add (add_le_add h1 (Nat.mul_le_mul_of_nonneg_right h2)) h1) h2) h3

example {a b c d e : Nat} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ e) :
  a + c * e + a + c + 0 ≤ b + d * e + b + d + e :=
by apply_rules [add_le_add, Nat.mul_le_mul_of_nonneg_right]

-- Check that when we supply an iteration bound,
-- `apply_rules` works up to that bound and returns the remaining goals.
example {a b c d e : Nat} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ e) :
  a + c * e + a + c + 0 ≤ b + d * e + b + d + e :=
by
  apply_rules [add_le_add, Nat.mul_le_mul_of_nonneg_right] 9
  guard_target = 0 ≤ e
  assumption

-- Test that metavariables created for implicit arguments don't get stuck
-- This required extra work in Lean 3, but doesn't seem to be a problem in Lean 4.
example (P : Nat → Type) (f : {n : Nat} → P n → P (n + 1)) (g : P 0) : P 2 :=
by apply_rules [f, g]

-- Check that `apply_rules` solves goals that come after goals that it can't solve
example (Q : Type) (f : Nat → Q) : Int × Q :=
by
  apply_rules [Prod.mk, f]
  guard_target = Int
  exact 0
  guard_target = Nat
  exact 37
