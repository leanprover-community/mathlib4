/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Tactic.Hint

open Mathlib.Tactic.Hint

example : 1 = 1 := by
  run_tac do
    let s ← `(tactic| rfl)
    let l ← tryHint
    guard <| l.elem (s, 0)
  rfl

example : if 1 = 1 then 1 = 1 else False := by
  run_tac do
    let s ← `(tactic| split_ifs)
    let l ← tryHint
    guard <| l.elem (s, 2)
  split_ifs <;> trivial

-- Check we don't provide any hints on `False`.
example : False ∨ True := by
  success_if_fail_with_msg "no hints available" left; hint
  right; trivial

-- Check that tactics are sorted by the number of goals they leave.
example : 1 = 1 ∧ 2 = 2 := by
  run_tac do
    let s₁ ← `(tactic| decide)
    let s₂ ← `(tactic| fconstructor)
    let l ← tryHint
    guard <| l.indexOf (s₁, 0) < l.indexOf (s₂, 2)
  decide

example (h : False) : False := by
  run_tac do
    let s ← `(tactic| assumption)
    let l ← tryHint
    guard <| l.elem (s, 0)
  assumption

example {P Q : Prop} (p : P) (h : P → Q) : Q := by
  run_tac do
    let s ← `(tactic| solve_by_elim)
    let l ← tryHint
    guard <| l.elem (s, 0)
  solve_by_elim

-- Check that a number of goals is counted correctly, when `hint` is called with multiple goals.
example : 1 = 1 ∧ 2 = 2 := by
  constructor
  run_tac do
    let s ← `(tactic| solve_by_elim)
    let l ← tryHint
    guard <| l.elem (s, 0)
  solve_by_elim
  run_tac do
    let s ← `(tactic| rfl)
    let l ← tryHint
    guard <| l.elem (s, 0)
  rfl
