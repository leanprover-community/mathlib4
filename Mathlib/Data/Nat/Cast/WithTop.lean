/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop

/-!
# Lemma about the coercion `ℕ → WithBot ℕ`.

An orphaned lemma about casting from `ℕ` to `WithBot ℕ`,
exiled here during the port to minimize imports of `Algebra.Order.Ring.Rat`.
-/

public section

instance : WellFoundedRelation (WithTop ℕ) where
  rel := (· < ·)
  wf := IsWellFounded.wf

theorem Nat.cast_withTop (n : ℕ) : Nat.cast n = WithTop.some n :=
  rfl

theorem Nat.cast_withBot (n : ℕ) : Nat.cast n = WithBot.some n :=
  rfl


-- Dual/order lemmas discovered by the Manifold Destiny verifier-mediated learner.
-- Paper: https://github.com/sumofagents/manifold-destiny
section
theorem Nat.WithTop.add_eq_one_iff : ∀ {n m : WithTop ℕ}, n + m = 1 ↔ n = 0 ∧ m = 1 ∨ n = 1 ∧ m = 0 := by
  open Nat Nat.WithBot in
    intro n m
    cases n
    · simp
    cases m
    · simp [WithTop.add_top]
    simp [← WithTop.coe_add, Nat.add_eq_one_iff]

theorem Nat.WithTop.add_eq_two_iff : ∀ {n m : WithTop ℕ}, n + m = 2 ↔ n = 0 ∧ m = 2 ∨ n = 1 ∧ m = 1 ∨ n = 2 ∧ m = 0 := by
  open Nat Nat.WithBot in
    intro n m
    cases n
    · simp [WithTop.top_add]
    cases m
    · simp [WithTop.add_top]
    simp [← WithTop.coe_add, Nat.add_eq_two_iff]

theorem Nat.WithTop.add_eq_three_iff : ∀ {n m : WithTop ℕ}, n + m = 3 ↔ n = 0 ∧ m = 3 ∨ n = 1 ∧ m = 2 ∨ n = 2 ∧ m = 1 ∨ n = 3 ∧ m = 0 := by
  open Nat Nat.WithBot in
    intro n m
    cases n
    · simp [WithTop.top_add]
    cases m
    · simp [WithTop.add_top]
    simp [← WithTop.coe_add, Nat.add_eq_three_iff]

end
