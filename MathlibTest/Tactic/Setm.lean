/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis, Gareth Ma
-/
import Mathlib.Tactic.Setm

/- Basic usage. -/
example : 1 + 2 = 3 := by
  setm ?a + ?b = _
  guard_target =ₛ a + b = 3
  guard_hyp a :=ₛ 1
  guard_hyp b :=ₛ 2
  trivial

/- Assignment of a constant under a binder. -/
example : (fun x ↦ x + 2) = (fun y ↦ y + 1 + 1) := by
  setm (fun x ↦ x + ?b) = _
  guard_target =ₛ (fun x ↦ x + b) = (fun y ↦ y + 1 + 1)
  guard_hyp b :=ₛ 2
  trivial

/- Usage with `using` and `at` keywords -/
set_option linter.unusedVariables false in
example (h1 : 1 + 1 = 5) (h2 : 1 + 3 = 5) (h3 : 1 + 2 = 5) : True := by
  setm ?a + _ = ?b using h1 at h1 h2 h3
  guard_hyp a :=ₛ 1
  guard_hyp b :=ₛ 5
  guard_hyp h1 :ₛ a + a = b
  guard_hyp h2 :ₛ a + 3 = b
  guard_hyp h3 :ₛ a + 2 = b
  trivial

/- Conflict with a previously defined local declaration name. (The previous one gets ignored.) -/
example : 1 + 2 = 3 := by
  let a := "foo"
  setm ?a + ?b = _
  guard_target =ₛ a + b = 3
  guard_hyp a :=ₛ 1
  guard_hyp b :=ₛ 2
  trivial

variable {a b c : Nat}

/- Test reusing named holes -/
example (h : b + a = c) : a + b = c := by
  /- setm 1-/
  setm ?A + ?B = _
  guard_target =ₛ A + B = c
  guard_hyp A :=ₛ a
  guard_hyp B :=ₛ b
  /- clean up -/
  unfold A B
  clear A B
  /- setm 2 -/
  rewrite [Nat.add_comm]
  setm ?A + ?B = _ at h
  guard_hyp h :ₛ A + B = c
  guard_hyp A :=ₛ b
  guard_hyp B :=ₛ a
  exact h

/- Test reducible + instances transparency -/

def NotQuiteNat : Type := Nat

instance : HAdd NotQuiteNat NotQuiteNat NotQuiteNat := inferInstanceAs (HAdd Nat Nat Nat)

example {a b c : NotQuiteNat} (h : a + b = c) : True := by
  /- setm 1-/
  setm ?A + ?B = _ using h
  guard_hyp h :ₛ A + B = c
  guard_hyp A := a
  guard_hyp B := b
  trivial

/--
error: setm pattern
  @Eq Nat (A + B) ?m.18
is not definitionally equal to the target
  @Eq NotQuiteNat (a + b) c
-/
#guard_msgs in
example {a b c : NotQuiteNat} (h : a + b = c) : True := by
  /- setm 1-/
  setm (?A : Nat) + ?B = _ using h

/- Test conflicts with goal metavariables (thanks to Niklas Halonen for this example). -/

inductive AOrB where | A | B

example (h : AOrB) : 1 + 2 = 3 := by
  cases h
  · setm ?A + ?B = _
    guard_target =ₛ A + B = 3
    guard_hyp A :=ₛ 1
    guard_hyp B :=ₛ 2
    trivial
  trivial
