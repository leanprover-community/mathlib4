/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.ite_simp
! leanprover-community/mathlib commit 4a03bdeb31b3688c31d02d7ff8e0ff2e5d6174db
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Data.Bool.Default

/-!
# Simplification lemmas for ite.

We don't prove them at logic.lean because it is easier to prove them using
the tactic framework.
-/


@[simp]
theorem if_true_right_eq_or (p : Prop) [h : Decidable p] (q : Prop) :
    (if p then q else True) = (¬p ∨ q) := by by_cases p <;> simp [h]
#align if_true_right_eq_or if_true_right_eq_or

@[simp]
theorem if_true_left_eq_or (p : Prop) [h : Decidable p] (q : Prop) :
    (if p then True else q) = (p ∨ q) := by by_cases p <;> simp [h]
#align if_true_left_eq_or if_true_left_eq_or

@[simp]
theorem if_false_right_eq_and (p : Prop) [h : Decidable p] (q : Prop) :
    (if p then q else False) = (p ∧ q) := by by_cases p <;> simp [h]
#align if_false_right_eq_and if_false_right_eq_and

@[simp]
theorem if_false_left_eq_and (p : Prop) [h : Decidable p] (q : Prop) :
    (if p then False else q) = (¬p ∧ q) := by by_cases p <;> simp [h]
#align if_false_left_eq_and if_false_left_eq_and

