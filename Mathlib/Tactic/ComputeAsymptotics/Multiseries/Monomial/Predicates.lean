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

# Predicates on monomials

In thie file we define some predicates on lists of real numbers:
1. `FirstNonzeroIsPos li` means that the firs non-zero element of the list `li` is positive.
2. `FirstNonzeroIsNeg li` means that the firs non-zero element of the list `li` is negative.
3. `AllZero li` means that all elements in `li` are zero.

When `li` is the list of exponent of the monomial in a well-formed basis, this trichotomy determines
its asymptotic behaviour: `FirstNonzeroIsPos` means it tends to infinity, `FirstNonzeroIsNeg` means
it tends to zero and `AllZero` means it tends to a constant.
-/

@[expose] public section

namespace Tactic.ComputeAsymptotics

/-- Predicate stating that the first non-zero element of the list is positive. -/
def FirstNonzeroIsPos (li : List ℝ) : Prop := match li with
  | [] => False
  | hd :: tl => 0 < hd ∨ (hd = 0 ∧ FirstNonzeroIsPos tl)

/-- Predicate stating that the first non-zero element of the list is negative. -/
def FirstNonzeroIsNeg (li : List ℝ) : Prop := match li with
  | [] => False
  | hd :: tl => hd < 0 ∨ (hd = 0 ∧ FirstNonzeroIsNeg tl)

/-- Predicate stating that all elements of the list are zero. -/
def AllZero (li : List ℝ) : Prop := ∀ x ∈ li, x = 0

theorem AllZero_of_nil : AllZero [] := by
  simp [AllZero]

@[simp]
theorem AllZero.cons_iff {hd : ℝ} {tl : List ℝ} : AllZero (hd :: tl) ↔ hd = 0 ∧ AllZero tl := by
  simp [AllZero]

theorem AllZero_of_tail {hd : ℝ} {tl : List ℝ} (h_hd : hd = 0) (h_tl : AllZero tl) :
    AllZero (hd :: tl) := by
  grind [AllZero]


theorem FirstNonzeroIsPos_of_head {hd : ℝ} (tl : List ℝ) (h : 0 < hd) :
    FirstNonzeroIsPos (hd :: tl) := by
  simp [FirstNonzeroIsPos]
  grind

theorem FirstNonzeroIsPos_of_tail {hd : ℝ} {tl : List ℝ} (h_hd : hd = 0)
    (h_tl : FirstNonzeroIsPos tl) :
    FirstNonzeroIsPos (hd :: tl) := by
  grind [FirstNonzeroIsPos]

theorem FirstNonzeroIsNeg_of_head {hd : ℝ} (tl : List ℝ) (h : hd < 0) :
    FirstNonzeroIsNeg (hd :: tl) := by
  grind [FirstNonzeroIsNeg]

theorem FirstNonzeroIsNeg_of_tail {hd : ℝ} {tl : List ℝ} (h_hd : hd = 0)
    (h_tl : FirstNonzeroIsNeg tl) :
    FirstNonzeroIsNeg (hd :: tl) := by
  grind [FirstNonzeroIsNeg]

theorem AllZero_of_replicate {n : ℕ} : AllZero (List.replicate n 0) := by
  cases n <;> simp [AllZero]

theorem not_FirstNonzeroIsPos_of_AllZero {li : List ℝ} (h : AllZero li) :
    ¬ FirstNonzeroIsPos li := by
  induction li with
  | nil => simp [FirstNonzeroIsPos]
  | cons hd tl ih =>
    simp [AllZero] at h
    grind [AllZero, FirstNonzeroIsPos]

theorem not_FirstNonzeroIsPos_of_FirstNonzeroIsNeg {li : List ℝ} (h : FirstNonzeroIsNeg li) :
    ¬ FirstNonzeroIsPos li := by
  induction li with
  | nil => simp [FirstNonzeroIsPos]
  | cons hd tl ih => grind [FirstNonzeroIsNeg, FirstNonzeroIsPos]

end Tactic.ComputeAsymptotics
