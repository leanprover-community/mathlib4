/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Johan Commelin
-/
import Mathlib.Tactic.WLOG
import Mathlib.Algebra.Ring.Nat

example {x y : ℕ} : True := by
  wlog h : x ≤ y
  · guard_hyp h :ₛ ¬x ≤ y
    guard_hyp this :ₛ ∀ {x y : ℕ}, x ≤ y → True -- `wlog` generalizes by default
    guard_target =ₛ True
    trivial
  · guard_hyp h :ₛ x ≤ y
    guard_target =ₛ True
    trivial

example {x y : ℕ} : True := by
  wlog! h : x ≤ y
  · guard_hyp h : y < x
    guard_hyp this :ₛ ∀ {x y : ℕ}, x ≤ y → True -- `wlog` generalizes by default
    guard_target =ₛ True
    trivial
  · guard_hyp h :ₛ x ≤ y
    guard_target =ₛ True
    trivial

example {x y : ℕ} : True := by
  wlog h : x ≤ y generalizing x with H
  · guard_hyp h : ¬x ≤ y
    guard_hyp H :ₛ ∀ {x : ℕ}, x ≤ y → True -- only `x` was generalized
    guard_target =ₛ True
    trivial
  · guard_hyp h :ₛ x ≤ y
    guard_target =ₛ True
    trivial

example {x y : ℕ} : True := by
  wlog! h : x ≤ y generalizing x with H
  · guard_hyp h : y < x
    guard_hyp H :ₛ ∀ {x : ℕ}, x ≤ y → True -- only `x` was generalized
    guard_target =ₛ True
    trivial
  · guard_hyp h :ₛ x ≤ y
    guard_target =ₛ True
    trivial

example {x y z : ℕ} : True := by
  wlog h : x ≤ y + z with H
  · guard_hyp h : ¬ x ≤ y + z
    guard_hyp H :ₛ ∀ {x y z : ℕ}, x ≤ y + z → True -- wlog-claim is named `H` instead of `this`
    guard_target =ₛ True
    trivial
  · guard_hyp h :ₛ x ≤ y + z
    guard_target =ₛ True
    trivial

example {x y z : ℕ} : True := by
  wlog! h : x ≤ y + z with H
  · guard_hyp h : y + z < x
    guard_hyp H :ₛ ∀ {x y z : ℕ}, x ≤ y + z → True -- wlog-claim is named `H` instead of `this`
    guard_target =ₛ True
    trivial
  · guard_hyp h :ₛ x ≤ y + z
    guard_target =ₛ True
    trivial

example : ∀ _ _ : ℕ, True := by
  intro x y
  wlog h : x ≤ y -- `wlog` finds new variables
  · trivial
  · trivial

example : ∀ _ _ : ℕ, True := by
  intro x y
  wlog! h : x ≤ y -- `wlog` finds new variables
  · trivial
  · trivial

example {x y : ℕ} : True := by
  wlog h : x ≤ y generalizing y x with H
  · guard_hyp h : ¬ x ≤ y
    guard_hyp H :ₛ ∀ {x y : ℕ}, x ≤ y → True -- order of ids in `generalizing` is ignored
    trivial
  · trivial

example {x y : ℕ} : True := by
  wlog! h : x ≤ y generalizing y x with H
  · guard_hyp h : y < x
    guard_hyp H :ₛ ∀ {x y : ℕ}, x ≤ y → True -- order of ids in `generalizing` is ignored
    trivial
  · trivial

-- metadata doesn't cause a problem
example (α : Type := ℕ) (x : Option α := none) (y : Option α := by exact 0) : True := by
  wlog h : x = y with H
  · guard_hyp h :ₛ ¬ x = y
    guard_hyp H :ₛ ∀ (α : Type), ∀ {x y : Option α}, x = y → True
    trivial
  · guard_hyp h :ₛ x = y
    guard_target =ₛ True
    trivial

-- metadata doesn't cause a problem
example (α : Type := ℕ) (x : Option α := none) (y : Option α := by exact 0) : True := by
  wlog! h : x = y with H
  · guard_hyp h :ₛ x ≠ y
    guard_hyp H :ₛ ∀ (α : Type), ∀ {x y : Option α}, x = y → True
    trivial
  · guard_hyp h :ₛ x = y
    guard_target =ₛ True
    trivial

-- inaccessible names work
example {x y : ℕ} : True := by
  wlog _ : x ≤ y
  case _ h => -- if these hypotheses weren't inaccessible, they wouldn't be renamed by `case`
    guard_hyp h :ₛ ¬x ≤ y
    guard_hyp this :ₛ ∀ {x y : ℕ}, x ≤ y → True
    guard_target =ₛ True
    trivial
  case _ h =>
    guard_hyp h :ₛ x ≤ y
    guard_target =ₛ True
    trivial

-- inaccessible names work
example {x y : ℕ} : True := by
  wlog! _ : x ≤ y
  case _ h => -- if these hypotheses weren't inaccessible, they wouldn't be renamed by `case`
    guard_hyp h : y < x
    guard_hyp this :ₛ ∀ {x y : ℕ}, x ≤ y → True
    guard_target =ₛ True
    trivial
  case _ h =>
    guard_hyp h :ₛ x ≤ y
    guard_target =ₛ True
    trivial

-- Handle ldecls properly:
example (x y : ℕ) : True := by
  let z := 0
  wlog hxy' : z ≤ y with H
  · trivial
  · trivial

-- Handle ldecls properly:
example (x y : ℕ) : True := by
  let z := 0
  wlog! hxy' : z ≤ y with H
  · trivial
  · trivial

example (x y : ℕ) : True := by
  wlog! h : x = 0 ∨ y = 0
  · guard_hyp h :ₛ x ≠ 0 ∧ y ≠ 0
    trivial
  · trivial

example (x y : ℕ) : True := by
  wlog! h : x = 0 ∧ y = 0
  · guard_hyp h :ₛ x = 0 → y ≠ 0
    trivial
  · trivial

set_option push_neg.use_distrib true in
example (x y : ℕ) : True := by
  wlog! h : x = 0 ∧ y = 0
  · guard_hyp h :ₛ x ≠ 0 ∨ y ≠ 0
    trivial
  · trivial

example (x y : ℕ) : True := by
  wlog! +distrib h : x = 0 ∧ y = 0
  · guard_hyp h :ₛ x ≠ 0 ∨ y ≠ 0
    trivial
  · trivial
