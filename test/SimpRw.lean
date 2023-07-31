/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Mario Carneiro
-/

import Mathlib.Tactic.SimpRw

-- `simp_rw` can perform rewrites under binders:
example : (λ (x y : Nat) => x + y) = (λ x y => y + x) := by simp_rw [Nat.add_comm]

-- `simp_rw` can apply reverse rules:
example (f : Nat → Nat) {a b c : Nat} (ha : f b = a) (hc : f b = c) : a = c := by simp_rw [← ha, hc]

-- `simp_rw` applies rewrite rules multiple times:
example (a b c d : Nat) : a + (b + (c + d)) = ((d + c) + b) + a := by simp_rw [Nat.add_comm]

-- `simp_rw` can also rewrite in assumptions:
example (p : Nat → Prop) (a b : Nat) (h : p (a + b)) : p (b + a) :=
by {simp_rw [Nat.add_comm a b] at h; exact h}
-- or at multiple assumptions:
example (p : Nat → Prop) (a b : Nat) (h₁ : p (b + a) → p (a + b)) (h₂ : p (a + b)) : p (b + a) :=
by {simp_rw [Nat.add_comm a b] at h₁ h₂; exact h₁ h₂}
-- or everywhere:
example (p : Nat → Prop) (a b : Nat) (h₁ : p (b + a) → p (a + b)) (h₂ : p (a + b)) : p (a + b) :=
by {simp_rw [Nat.add_comm a b] at *; exact h₁ h₂}

-- `simp` and `rw`, alone, can't close this goal. But `simp_rw` can
example {a : Nat}
  (h1 : ∀ a b : Nat, a - 1 ≤ b ↔ a ≤ b + 1)
  (h2 : ∀ a b : Nat, a ≤ b ↔ ∀ c, c < a → c < b) :
  (∀ b, a - 1 ≤ b) = ∀ b c : Nat, c < a → c < b + 1 :=
by simp_rw [h1, h2]
