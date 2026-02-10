import Mathlib.Tactic.RSuffices
import Mathlib.Tactic.ExistsI
import Mathlib.Algebra.Ring.Nat
import Mathlib.Data.Set.Defs

set_option autoImplicit true
/-- These next few are duplicated from `rcases/obtain` tests, with the goal order swapped. -/

example : True := by
  rsuffices ⟨n : ℕ, h : n = n, -⟩ : ∃ n : ℕ, n = n ∧ True
  · guard_hyp n : ℕ
    guard_hyp h : n = n
    trivial
  · existsi 0
    simp

example : True := by
  rsuffices : ∃ n : ℕ, n = n ∧ True
  · trivial
  · existsi 0
    simp

example : True := by
  rsuffices (h : True) | ⟨⟨⟩⟩ : True ∨ False
  · guard_hyp h : True
    trivial
  · left
    trivial

example (x y : α × β) : True := by
  rsuffices ⟨⟨a, b⟩, c, d⟩ : (α × β) × (α × β)
  · guard_hyp a : α
    guard_hyp b : β
    guard_hyp c : α
    guard_hyp d : β
    trivial
  · exact ⟨x, y⟩

-- This test demonstrates why `swap` is not used in the implementation of `rsuffices`:
-- it would make the _second_ goal the one requiring ⟨x, y⟩, not the last one.
example (x y : α ⊕ β) : True := by
  rsuffices ⟨a|b, c|d⟩ : (α ⊕ β) × (α ⊕ β)
  · guard_hyp a : α
    guard_hyp c : α
    trivial
  · guard_hyp a : α
    guard_hyp d : β
    trivial
  · guard_hyp b : β
    guard_hyp c : α
    trivial
  · guard_hyp b : β
    guard_hyp d : β
    trivial
  exact ⟨x, y⟩


protected def Set.foo {α β} (_ : Set α) (_ : Set β) : Set (α × β) := ∅

example {α} (V : Set α) (w : True → ∃ p, p ∈ (V.foo V) ∩ (V.foo V)) : True := by
  rsuffices ⟨_, _⟩ : ∃ p, p ∈ (V.foo V) ∩ (V.foo V)
  · trivial
  · exact w trivial
