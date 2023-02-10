/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Johan Commelin
-/
import Mathlib.Tactic.WLOG
import Mathlib.Data.Nat.Basic

set_option trace.debug true
example {x y : ℕ} : True := by
  wlog h : x ≤ y
  { guard_hyp h : ¬x ≤ y
    guard_hyp «this» : ∀ {x y : ℕ}, x ≤ y → True -- `wlog` generalizes by default
    guard_target =ₛ True
    trivial }
  { guard_hyp h : x ≤ y
    guard_target =ₛ True
    trivial }

example {x y : ℕ} : True := by
  wlog h : x ≤ y generalizing x with H
  { guard_hyp h : ¬x ≤ y
    guard_hyp H : ∀ {x : ℕ}, x ≤ y → True -- only `x` was generalized
    guard_target =ₛ True
    trivial }
  { guard_hyp h : x ≤ y
    guard_target =ₛ True
    trivial }

example {x y z : ℕ} : True := by
  wlog h : x ≤ y + z with H
  { guard_hyp h : ¬ x ≤ y + z
    guard_hyp H : ∀ {x y z : ℕ}, x ≤ y + z → True -- wlog-claim is named `H` instead of `this`
    guard_target =ₛ True
    trivial }
  { guard_hyp h : x ≤ y + z
    guard_target =ₛ True
    trivial }

example : ∀ _ _ : ℕ, True := by
  intro x y
  wlog h : x ≤ y -- `wlog` finds new variables
  { trivial }
  { trivial }
