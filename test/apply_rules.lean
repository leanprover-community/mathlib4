import Mathlib.Tactic.SolveByElim
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
  apply_rules (config := {maxDepth := 9}) [add_le_add, Nat.mul_le_mul_of_nonneg_right]
  guard_target = 0 ≤ e
  assumption

-- Check that `apply_rules only` works.
example {P Q : Prop} (p : P) (f : P → Q) : Q := by
  apply_rules only [f]
  exact p

-- Check that `apply_rules [-p]` works.
example {P Q : Prop} (p : P) (f : P → Q) : Q := by
  apply_rules [-p]
  exact p

-- Test that metavariables created for implicit arguments don't get stuck
-- This required extra work in Lean 3, but doesn't seem to be a problem in Lean 4.
example (P : Nat → Type) (f : {n : Nat} → P n → P (n + 1)) (g : P 0) : P 2 :=
by apply_rules only [f, g]

-- Check that `apply_rules` solves goals that come after goals that it can't solve
example (Q : Type) (f : Nat → Q) : Int × Q :=
by
  apply_rules only [Prod.mk, f]
  guard_target = Int
  exact 0
  guard_target = Nat
  exact 37
