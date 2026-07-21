/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis, Gareth Ma
-/
module

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

-- TODO:
-- -- set_option pp.raw true
-- example : ∃ n : ℕ, True := by
--   let a := "foo"
--   setm ∃ n, ?n

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

-- TODO:
-- example (a : Array Nat) (i i' : Nat) (h') (h) (h₀ : a[i] = 2) : a[i] + a[i'] = 4 := by
--   setm a[?j] + a[i'] = 4 at h₀

/- Test reducible + instances transparency -/

def NotQuiteNat : Type := Nat

instance : HAdd NotQuiteNat NotQuiteNat NotQuiteNat := inferInstanceAs (HAdd Nat Nat Nat)

example {a b c : NotQuiteNat} (h : a + b = c) : True := by
  /- setm 1-/
  have A : True := trivial
  setm ?A + ?B = _ using h
  guard_hyp h :ₛ A + B = c
  guard_hyp A := a
  guard_hyp B := b
  trivial

-- TODO:
-- abbrev f : Nat → Nat → Nat := fun _ x => x

-- example (h : 4 = 3) : () = () := by
--   setm (true : Unit) = (true : Unit)

-- example (h : (4, fun x : Nat => x) = (5, fun _ => 5)) :
--   ((4, fun x : Nat => x) : Nat × (Nat → Nat)) = (5, fun _ : Nat => 5) := by
--   /- setm 1-/
--   have A : True := trivial
--   setm (?l, fun _ => ?l) = (_ + _, _) at h
--   guard_hyp h :ₛ A + B = c
--   guard_hyp A := a
--   guard_hyp B := b
--   trivial

/--
error: Tactic `setm` failed: Pattern
  @Eq Nat (A + B) ?m.20
is not definitionally equal to the target
  @Eq NotQuiteNat (a + b) c

a✝ b✝ c✝ : Nat
a b c : NotQuiteNat
h : a + b = c
⊢ True
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

/- Test for `.synthetic` metavariables created during elaboration of the pattern that should be
synthesized "later". Here it is the hypothesis `h` that `i < l.length`. -/

example {i : Nat} {l : List Nat} (h) : l[i] = l[i] := by
  setm l[i] = _
  trivial
