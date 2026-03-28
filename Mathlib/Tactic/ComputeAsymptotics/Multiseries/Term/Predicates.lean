/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Tactic.MoveAdd
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Basis


/-!
In thie file we define some predicates on lists of real numbers.
TODO
-/

@[expose] public section

namespace Tactic.ComputeAsymptotics

namespace List

/-- Predicate stating that the first non-zero element of the list is positive. -/
def FirstIsPos (x : List ℝ) : Prop := match x with
| [] => False
| hd :: tl => 0 < hd ∨ (hd = 0 ∧ FirstIsPos tl)

/-- Predicate stating that the first non-zero element of the list is negative. -/
def FirstIsNeg (x : List ℝ) : Prop := match x with
| [] => False
| hd :: tl => hd < 0 ∨ (hd = 0 ∧ FirstIsNeg tl)

/-- Predicate stating that all elements of the list are zero. -/
def AllZero (x : List ℝ) : Prop := match x with
| [] => True
| hd :: tl => hd = 0 ∧ AllZero tl

theorem AllZero_of_nil : AllZero [] := by
  simp [AllZero]

theorem AllZero_of_tail {hd : ℝ} {tl : List ℝ} (h_hd : hd = 0) (h_tl : AllZero tl) :
    AllZero (hd :: tl) := by
  grind [AllZero]

theorem FirstIsPos_of_head {hd : ℝ} (tl : List ℝ) (h : 0 < hd) : FirstIsPos (hd :: tl) := by
  simp [FirstIsPos]
  grind

theorem FirstIsPos_of_tail {hd : ℝ} {tl : List ℝ} (h_hd : hd = 0) (h_tl : FirstIsPos tl) :
    FirstIsPos (hd :: tl) := by
  grind [FirstIsPos]

theorem FirstIsNeg_of_head {hd : ℝ} (tl : List ℝ) (h : hd < 0) : FirstIsNeg (hd :: tl) := by
  grind [FirstIsNeg]

theorem FirstIsNeg_of_tail {hd : ℝ} {tl : List ℝ} (h_hd : hd = 0) (h_tl : FirstIsNeg tl) :
    FirstIsNeg (hd :: tl) := by
  grind [FirstIsNeg]

theorem AllZero_of_replicate {n : ℕ} : AllZero (List.replicate n 0) := by
  cases n with
  | zero => simp [AllZero]
  | succ n =>
    simpa only [List.replicate_succ, AllZero, true_and] using AllZero_of_replicate

theorem not_FirstIsPos_of_AllZero {x : List ℝ} (h : AllZero x) : ¬ FirstIsPos x := by
  cases x with
  | nil => simp [FirstIsPos]
  | cons hd tl =>
    intro h'
    simp only [AllZero, FirstIsPos] at h h'
    simp only [h.left, lt_self_iff_false, true_and, false_or] at h'
    exact not_FirstIsPos_of_AllZero h.right h'

theorem not_FirstIsPos_of_FirstIsNeg {x : List ℝ} (h : FirstIsNeg x) : ¬ FirstIsPos x := by
  cases x with
  | nil => simp [FirstIsPos]
  | cons hd tl =>
    intro h'
    simp only [FirstIsNeg, FirstIsPos] at h h'
    by_cases h_hd : hd = 0
    · simp only [h_hd, lt_self_iff_false, true_and, false_or] at h h'
      exact not_FirstIsPos_of_FirstIsNeg h h'
    simp [h_hd] at h h'
    linarith

end List

end Tactic.ComputeAsymptotics
