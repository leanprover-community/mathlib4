/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Johan Commelin
-/
import Mathlib.Tactic.WLOG
import Mathlib.Tactic.SuccessIfFailWithMsg
import Mathlib.Algebra.Ring.Nat

example {x y : ℕ} : True := by
  wlog h : x ≤ y
  · guard_hyp h : ¬x ≤ y
    guard_hyp this : ∀ {x y : ℕ}, x ≤ y → True -- `wlog` generalizes by default
    guard_target =ₛ True
    trivial
  · guard_hyp h : x ≤ y
    guard_target =ₛ True
    trivial

example {x y : ℕ} : True := by
  wlog h : x ≤ y generalizing x with H
  · guard_hyp h : ¬x ≤ y
    guard_hyp H : ∀ {x : ℕ}, x ≤ y → True -- only `x` was generalized
    guard_target =ₛ True
    trivial
  · guard_hyp h : x ≤ y
    guard_target =ₛ True
    trivial

example {x y z : ℕ} : True := by
  wlog h : x ≤ y + z with H
  · guard_hyp h : ¬ x ≤ y + z
    guard_hyp H : ∀ {x y z : ℕ}, x ≤ y + z → True -- wlog-claim is named `H` instead of `this`
    guard_target =ₛ True
    trivial
  · guard_hyp h : x ≤ y + z
    guard_target =ₛ True
    trivial

example : ∀ _ _ : ℕ, True := by
  intro x y
  wlog h : x ≤ y -- `wlog` finds new variables
  · trivial
  · trivial

example {x y : ℕ} : True := by
  wlog h : x ≤ y generalizing y x with H
  · guard_hyp h : ¬ x ≤ y
    guard_hyp H : ∀ {x y : ℕ}, x ≤ y → True -- order of ids in `generalizing` is ignored
    trivial
  · trivial

-- metadata doesn't cause a problem
example (α : Type := ℕ) (x : Option α := none) (y : Option α := by exact 0) : True := by
  wlog h : x = y with H
  · guard_hyp h : ¬ x = y
    guard_hyp H : ∀ α, ∀ {x y : Option α}, x = y → True
    trivial
  · guard_hyp h : x = y
    guard_target =ₛ True
    trivial

-- inaccessible names work
example {x y : ℕ} : True := by
  wlog _ : x ≤ y
  case _ h => -- if these hypotheses weren't inaccessible, they wouldn't be renamed by `case`
    guard_hyp h : ¬x ≤ y
    guard_hyp this : ∀ {x y : ℕ}, x ≤ y → True
    guard_target =ₛ True
    trivial
  case _ h =>
    guard_hyp h : x ≤ y
    guard_target =ₛ True
    trivial

-- Handle ldecls properly:
example (x y : ℕ) : True := by
  let z := 0
  wlog hxy' : z ≤ y with H
  · trivial
  · trivial

section Replacing

axiom A : Nat → Prop
axiom B : Nat → Prop
axiom C : Nat → Prop

axiom S : (n : Nat) → A n → Prop

example (n : Nat) (h : A n) (h' : B n) : True := by
  guard_hyp h : A n
  wlog h'' : C n generalizing n replacing h
  · guard_hyp this : ∀ (n : ℕ), B n → C n → True
    trivial
  · success_if_fail_with_msg "unknown identifier 'h'" guard_hyp h : A n
    trivial

-- Forward dependencies are accounted for
example (n : Nat) (h : A n) (_h' : S n h) : True := by
  guard_hyp h : A n
  guard_hyp _h' : S n h
  wlog h'' : C n generalizing n replacing h
  · guard_hyp this : ∀ (n : ℕ), C n → True
    trivial
  · success_if_fail_with_msg "unknown identifier 'h'" guard_hyp h : A n
    success_if_fail_with_msg "unknown identifier '_h''" guard_hyp _h' : S h
    trivial

def err₁ := "replaced hypotheses
  [m]
were expected to depend on the generalized hypotheses
  [n]"

-- Can't replace something not generalized
example (n m : Nat) : True := by
  success_if_fail_with_msg err₁ wlog h : True generalizing n replacing m
  trivial

def err₂ := "  S n h → True
depends on the replaced hypotheses
  [h]"

example (n : Nat) (h : A n) : True := by
  guard_hyp h : A n
  /- If this worked, we'd have `this : ∀ (n : ℕ), S n h → True`. `this` can't possibly be
  type-correct: since `P := S n h` depends on `h`, and `h` depends on a reverted
  variable `n` (via `h : A n`), the `n` in `h : A n` would be the `n` in the local context, which
  is not the same as the `n` bound by `∀ (n : ℕ)`. -/
  success_if_fail_with_msg err₂ wlog h'' : S n h generalizing n replacing h
  trivial

end Replacing
