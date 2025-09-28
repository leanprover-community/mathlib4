/-
Copyright (c) 2022 Alice Laroche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alice Laroche, Frédéric Dupuis, Jireh Loreaux
-/

import Mathlib.Order.Defs.LinearOrder
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Push

private axiom test_sorry : ∀ {α}, α
set_option autoImplicit true
variable {α β : Type} [LinearOrder β] {p q : Prop} {p' q' : α → Prop}

example : ¬ False := by
  push_neg

example (h : ¬ True) : False := by
  push_neg at h
  exact h

example : (¬p ∧ ¬q) → ¬(p ∨ q) := by
  intro h
  push_neg
  guard_target = ¬p ∧ ¬q
  exact h

example : ¬(p ∧ q) → (p → ¬q) := by
  intro h
  push_neg at h
  guard_hyp h : p → ¬q
  exact h

example : (∀ (x : α), ¬ p' x) → ¬ ∃ (x : α), p' x := by
  intro h
  push_neg
  guard_target = ∀ (x : α), ¬p' x
  exact h

example : (¬ ∀ (x : α), p' x) → (∃ (x : α), ¬ p' x) := by
  intro h
  push_neg at h
  guard_hyp h : ∃ (x : α), ¬p' x
  exact h

example (p : Bool) : decide (¬ ¬ p) = p := by
  push_neg
  guard_target = decide p = p
  cases p <;> rfl

example : ((fun x => x+x) 1) = 2 := by
  push_neg
  guard_target = 1 + 1 = 2
  simp

example : ¬ ¬ p = p := by
  push_neg
  guard_target = p = p
  rfl

example (x y : β) (h : y < x) : ¬(x ≤ y) := by
  push_neg
  guard_target = y < x
  exact h

example (a b : β) (h : a ≤ b) : ¬ a > b := by
  push_neg
  guard_target = a ≤ b
  exact h

example (x y : α) (h : x = y) : ¬ (x ≠ y) := by
  push_neg
  guard_target = x = y
  exact h

example : ¬∃ (y : Unit), (y ≠ ()) := by
  push_neg
  guard_target = ∀ (y : Unit), y = ()
  simp

example (h : ∃ y : Nat, ¬(y=1)): ¬∀ (y : Nat), (y = 1) := by
  push_neg
  guard_target = ∃ (y : Nat), y ≠ 1
  exact h

example (x y : β) (h : y < x) : ¬¬¬ (x ≤ y) := by
  push_neg
  guard_target = y < x
  exact h

set_option linter.unusedVariables false in
example (x y : β) (h₁ : ¬¬¬(x < y)) (h₂ : ¬∃ (x y : Nat), x = y) : ¬ ∀ (x y : Nat), x = y := by
  push_neg at *
  guard_target = ∃ (x y : Nat), x ≠ y
  guard_hyp h₁ : y ≤ x
  guard_hyp h₂ : ∀ (x y : Nat), x ≠ y
  exact ⟨0, 1, by simp⟩

set_option linter.unusedVariables false in
example (x y : β) (h₁ : ¬¬¬(x < y)) (h₂ : ¬∃ (x y : Nat), x = y) : ¬ ∀ (x y : Nat), x = y := by
  push_neg at h₁ h₂ ⊢
  guard_target = ∃ (x y : Nat), x ≠ y
  guard_hyp h₁ : y ≤ x
  guard_hyp h₂ : ∀ (x y : Nat), x ≠ y
  exact ⟨0, 1, by simp⟩

example (h : p → ¬ q) : ¬ (p ∧ q) := by
  push_neg
  guard_target = p → ¬q
  exact h

example (a : β) : ¬ ∀ x : β, x < a → ∃ y : β, (y < a) ∧ ∀ z : β, x = z := by
  push_neg
  guard_target = ∃ x, x < a ∧ ∀ (y : β), y < a → ∃ z, x ≠ z
  exact test_sorry

set_option linter.unusedVariables false in
example {α} [Preorder α] (m n : α) (h : ¬(∃ k : α, m ≤ k)) (h₂ : m ≤ n) : m ≤ n := by
  push_neg at h
  guard_hyp h : ∀ k, ¬(m ≤ k)
  exact h₂

set_option linter.unusedVariables false in
example {α} [Preorder α] (m n : α) (h : ¬(∃ k : α, m < k)) (h₂ : m ≤ n) : m ≤ n := by
  push_neg at h
  guard_hyp h : ∀ k, ¬(m < k)
  exact h₂

example (r : LinearOrder α) (s : Preorder α) (a b : α) : ¬(s.lt a b → r.lt a b) := by
  push_neg
  guard_target = s.lt a b ∧ r.le b a
  exact test_sorry

example (r : LinearOrder α) (s : Preorder α) (a b : α) : ¬(r.lt a b → s.lt a b) := by
  push_neg
  guard_target = r.lt a b ∧ ¬ s.lt a b
  exact test_sorry

-- check that `push_neg` does not expand `let` definitions
example (h : p ∧ q) : ¬¬(p ∧ q) := by
  let r := p ∧ q
  change ¬¬r
  push_neg
  guard_target =ₛ r
  exact h

-- new error message as of https://github.com/leanprover-community/mathlib4/issues/27562
/-- error: push made no progress anywhere -/
#guard_msgs in
example {P : Prop} (h : P) : P := by push_neg at *

-- new behaviour as of https://github.com/leanprover-community/mathlib4/issues/27562
-- (Previously, because of a metavariable instantiation issue, the tactic succeeded as a no-op.)
/-- error: push made no progress at h -/
#guard_msgs in
example {x y : ℕ} : True := by
  have h : x ≤ y := test_sorry
  push_neg at h

-- new behaviour as of https://github.com/leanprover-community/mathlib4/issues/27562 (previously the tactic succeeded as a no-op)
/-- error: cannot run push at inductive_proof, it is an implementation detail -/
#guard_msgs in
def inductive_proof : True := by
  push_neg at inductive_proof
  trivial

section use_distrib
set_option push_neg.use_distrib true

example (h : ¬ p ∨ ¬ q): ¬ (p ∧ q) := by
  push_neg
  guard_target = ¬p ∨ ¬q
  exact h

example : p → ¬ ¬ ¬ ¬ ¬ ¬ p := by
  push_neg
  guard_target = p → p
  exact id

example (h : x = 0 ∧ y ≠ 0) : ¬(x = 0 → y = 0) := by
  push_neg
  guard_target = x = 0 ∧ y ≠ 0
  exact h

end use_distrib

example (a : α) (o : Option α) (h : ¬∀ hs, o.get hs ≠ a) : ∃ hs, o.get hs = a := by
  push_neg at h
  exact h

example (s : Set α) (h : ¬s.Nonempty) : s = ∅ := by
  push_neg at h
  exact h

example (s : Set α) (h : ¬ s = ∅) : s.Nonempty := by
  push_neg at h
  exact h

example (s : Set α) (h : s ≠ ∅) : s.Nonempty := by
  push_neg at h
  exact h

example (s : Set α) (h : ∅ ≠ s) : s.Nonempty := by
  push_neg at h
  exact h

namespace no_proj

structure G (V : Type) where
  Adj : V → V → Prop

def g : G Nat where
  Adj a b := (a ≠ b) ∧ ((a ∣ b) ∨ (b ∣ a))

example {p q : Nat} : ¬ g.Adj p q := by
  rw [g]
  guard_target =ₛ ¬ G.Adj { Adj := fun a b => (a ≠ b) ∧ ((a ∣ b) ∨ (b ∣ a)) } p q
  fail_if_success push_neg
  guard_target =ₛ ¬ G.Adj { Adj := fun a b => (a ≠ b) ∧ ((a ∣ b) ∨ (b ∣ a)) } p q
  dsimp only
  guard_target =ₛ ¬ ((p ≠ q) ∧ ((p ∣ q) ∨ (q ∣ p)))
  push_neg
  guard_target =ₛ p ≠ q → ¬p ∣ q ∧ ¬q ∣ p
  exact test_sorry

end no_proj
