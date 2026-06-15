/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gareth Ma, Lua Viana Reis
-/
import Mathlib.Tactic.Setm

variable {a b c : Nat}

/- Basic usage -/
example : 1 + 2 = 3 := by
  setm ?A + ?B = _
  guard_hyp A :=ₛ 1
  guard_hyp B :=ₛ 2
  trivial

/- Usage with `at` keywords -/
example (h1 : 1 + 1 = 5) (h2 : 1 + 3 = 5) (h3 : 1 + 2 = 5) : True := by
  setm ?A + _ = ?B at h1 h2 h3
  guard_hyp A :=ₛ 1
  guard_hyp B :=ₛ 5
  guard_hyp h1 :ₛ A + A = B
  guard_hyp h2 :ₛ A + 3 = B
  guard_hyp h3 :ₛ A + 2 = B
  trivial

/- Test reusing named holes -/
example (h : b + a = c) : a + b = c := by
  /- setm 1-/
  setm ?A + ?B = _
  guard_hyp A :=ₛ a
  guard_hyp B :=ₛ b
  /- clean up -/
  unfold A B
  clear A B
  /- setm 2 -/
  rewrite [Nat.add_comm]
  setm ?A + ?B = _ at h ⊢
  guard_hyp A :=ₛ b
  guard_hyp B :=ₛ a
  exact h

/- Test reducible + instances transparency -/

def NotQuiteNat : Type := Nat

instance : HAdd NotQuiteNat NotQuiteNat NotQuiteNat := inferInstanceAs (HAdd Nat Nat Nat)

example {a b c : NotQuiteNat} (h : a + b = c) : True := by
  /- setm 1-/
  setm ?A + ?B = _ at h
  guard_hyp A := a
  guard_hyp B := b
  trivial

/--
error: setm: pattern
  @Eq Nat (?A✝ + ?B✝) ?m.11
is not defeq to goal
  @Eq NotQuiteNat (a + b) c
-/
#guard_msgs in
example {a b c : NotQuiteNat} (h : a + b = c) : True := by
  /- setm 1-/
  setm (?A : Nat) + ?B = _ at h

/- Test conflicts with goal metavariables (thanks to Niklas Halonen for this example!) -/

inductive AOrB where | A | B

example (h : AOrB) : 1 + 2 = 3 := by
  cases h
  · setm ?A + ?B = _
    guard_hyp A :=ₛ 1
    guard_hyp B :=ₛ 2
    trivial
  trivial
