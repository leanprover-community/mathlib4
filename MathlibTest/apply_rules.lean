import Mathlib.Algebra.Order.Field.Basic

set_option autoImplicit true
open Nat

example {a b c d e : Nat} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ e) :
    a + c * e + a + c + 0 ≤ b + d * e + b + d + e :=
  Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add h1 (Nat.mul_le_mul_right _ h2)) h1) h2) h3

example {a b c d e : Nat} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ e) :
    a + c * e + a + c + 0 ≤ b + d * e + b + d + e := by
  apply_rules [Nat.add_le_add, Nat.mul_le_mul_right]

-- Check that when we supply an iteration bound,
-- `apply_rules` works up to that bound and returns the remaining goals.
example {a b c d e : Nat} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ e) :
    a + c * e + a + c + 0 ≤ b + d * e + b + d + e := by
  apply_rules (config := {maxDepth := 9}) [Nat.add_le_add, Nat.mul_le_mul_right]
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
example (P : Nat → Type) (f : {n : Nat} → P n → P (n + 1)) (g : P 0) : P 2 := by
  apply_rules only [f, g]

-- Check that `apply_rules` solves goals that come after goals that it can't solve
example (Q : Type) (f : Nat → Q) : Int × Q := by
  apply_rules only [Prod.mk, f]
  guard_target = Int
  exact 0
  guard_target = Nat
  exact 37

-- Test that with transparency set to `.reducible`, the tactic will not unfold `/` to the underlying
-- `*` to match the form of the lemma `mul_le_mul`
example [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} (hb : 0 ≤ b) (hab : a ≤ b) :
    a / 2 ≤ b / 2 := by
  fail_if_success
    apply_rules (config := { transparency := .reducible }) [mul_le_mul]
  guard_target = a / 2 ≤ b / 2
  exact div_le_div₀ hb hab zero_lt_two le_rfl
