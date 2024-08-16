import Mathlib.Tactic.RSuffices
import Mathlib.Tactic.ExistsI
import Mathlib.Algebra.Ring.Nat

set_option autoImplicit true
/-- These next few are duplicated from `rcases/obtain` tests, with the goal order swapped. -/

example : True := by
  rsuffices ⟨n : ℕ, h : n = n, -⟩ : True ∧ ∃ n : ℕ, n = n ∧ True := by
  · existsi 0
    simp
  · guard_hyp n : ℕ
    guard_hyp h : n = n
    trivial


example : True := by
  rsuffices : ∃ n : ℕ, n = n ∧ True
  · trivial
  · existsi 0
    simp

-- new syntax enabled
example : True := by
  rsuffices : ∃ n : ℕ, n = n ∧ True ∧ 2 + 2 = 4 := by
    existsi 0
    simp
  · trivial

example : True := by
  rsuffices (h : True) | ⟨⟨⟩⟩ : True ∨ False := by
    left
    trivial
  · guard_hyp h : True
    trivial


example (x y : α × β) : True := by
  rsuffices ⟨⟨a, b⟩, c, d⟩ : (α × β) × (α × β) := by
    exact ⟨x, y⟩
  guard_hyp a : α
  guard_hyp b : β
  guard_hyp c : α
  guard_hyp d : β
  trivial

-- This test demonstrates why `swap` is not used in the implementation of `rsuffices`:
-- it would make the _second_ goal the one requiring ⟨x, y⟩, not the last one.
example (x y : α ⊕ β) : True := by
  rsuffices ⟨a|b, c|d⟩ : (α ⊕ β) × (α ⊕ β) := by
  · guard_hyp a : α
    guard_hyp c : α
    trivial
  · guard_hyp a : α
    guard_hyp d : β
    trivial
  · guard_hyp b : β
    guard_hyp c : α
    trivial
  ·
  exact ⟨x, y⟩


protected def Set.foo {α β} (_ : Set α) (_ : Set β) : Set (α × β) := ∅

example {α} (V : Set α) (w : True → ∃ p, p ∈ (V.foo V) ∩ (V.foo V)) : True := by
  rsuffices ⟨_, _⟩ : ∃ p, p ∈ (V.foo V) ∩ (V.foo V)
  · trivial
  · exact w trivial
