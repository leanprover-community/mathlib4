/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Data.Real.Basic

/-!

# Predicates on monomials

In this file we define `UnitMonomial`: type to represent monomials without coefficient as a list of
its exponents.  `[e₁, e₂, ..., eₙ]` corresponds to `basis[0] ^ e₁ * ... * basis[n] ^ eₙ` where
`basis` is the basis of functions.

Then we define some predicates for these lists:
1. `FirstNonzeroIsPos li` means that the first non-zero element of the list `li` is positive.
2. `FirstNonzeroIsNeg li` means that the first non-zero element of the list `li` is negative.
3. `AllZero li` means that all elements in `li` are zero.

This trichotomy determines the asymptotic behaviour of a monomial:
`FirstNonzeroIsPos` means it tends to infinity, `FirstNonzeroIsNeg` means it tends to zero and
`AllZero` means it tends to a constant.
-/

@[expose] public section

namespace Tactic.ComputeAsymptotics

/-- Unit monomial, represented as a list of its exponents. `[e₁, e₂, ..., eₙ]` corresponds to
`basis[0] ^ e₁ * ... * basis[n] ^ eₙ` where `basis` is the basis of functions. -/
abbrev UnitMonomial := List ℝ

namespace UnitMonomial

/-- Predicate stating that the first non-zero exponent is positive. -/
def FirstNonzeroIsPos (li : UnitMonomial) : Prop := match li with
  | [] => False
  | hd :: tl => 0 < hd ∨ (hd = 0 ∧ FirstNonzeroIsPos tl)

/-- Predicate stating that the first non-zero exponent is negative. -/
def FirstNonzeroIsNeg (li : UnitMonomial) : Prop := match li with
  | [] => False
  | hd :: tl => hd < 0 ∨ (hd = 0 ∧ FirstNonzeroIsNeg tl)

/-- Predicate stating that all exponents are zero. -/
def AllZero (li : UnitMonomial) : Prop := ∀ x ∈ li, x = 0

namespace AllZero


@[simp]
theorem nil : AllZero [] := by
  simp [AllZero]

@[simp]
theorem cons_iff {hd : ℝ} {tl : UnitMonomial} :
    AllZero (hd :: tl) ↔ hd = 0 ∧ AllZero tl := by
  simp [AllZero]

theorem of_head {hd : ℝ} (tl : UnitMonomial) (h : 0 < hd) :
    FirstNonzeroIsPos (hd :: tl) := by
  simp [FirstNonzeroIsPos]
  grind

theorem of_tail {hd : ℝ} {tl : UnitMonomial} (h_hd : hd = 0) (h_tl : AllZero tl) :
    AllZero (hd :: tl) := by
  grind [AllZero]

theorem replicate {n : ℕ} : AllZero (List.replicate n 0) := by
  cases n <;> simp [AllZero]

theorem not_FirstNonzeroIsPos {li : UnitMonomial} (h : AllZero li) :
    ¬ FirstNonzeroIsPos li := by
  induction li with
  | nil => simp [FirstNonzeroIsPos]
  | cons hd tl ih =>
    simp [AllZero] at h
    grind [AllZero, FirstNonzeroIsPos]

end AllZero

namespace FirstNonzeroIsPos

@[simp]
theorem not_nil : ¬ FirstNonzeroIsPos [] := by
  grind [FirstNonzeroIsPos]

theorem of_head {hd : ℝ} (tl : UnitMonomial) (h_hd : 0 < hd) :
    FirstNonzeroIsPos (hd :: tl) := by
  grind [FirstNonzeroIsPos]

theorem of_tail {hd : ℝ} {tl : UnitMonomial} (h_hd : hd = 0)
    (h_tl : FirstNonzeroIsPos tl) :
    FirstNonzeroIsPos (hd :: tl) := by
  grind [FirstNonzeroIsPos]

@[simp]
theorem cons_iff {hd : ℝ} {tl : UnitMonomial} :
    FirstNonzeroIsPos (hd :: tl) ↔ 0 < hd ∨ (hd = 0 ∧ FirstNonzeroIsPos tl) := by
  grind [FirstNonzeroIsPos]

end FirstNonzeroIsPos

namespace FirstNonzeroIsNeg

@[simp]
theorem not_nil : ¬ FirstNonzeroIsNeg [] := by
  grind [FirstNonzeroIsNeg]

theorem of_head {hd : ℝ} (tl : UnitMonomial) (h : hd < 0) :
    FirstNonzeroIsNeg (hd :: tl) := by
  grind [FirstNonzeroIsNeg]

theorem of_tail {hd : ℝ} {tl : UnitMonomial} (h_hd : hd = 0)
    (h_tl : FirstNonzeroIsNeg tl) :
    FirstNonzeroIsNeg (hd :: tl) := by
  grind [FirstNonzeroIsNeg]

@[simp]
theorem cons_iff {hd : ℝ} {tl : UnitMonomial} :
    FirstNonzeroIsNeg (hd :: tl) ↔ hd < 0 ∨ (hd = 0 ∧ FirstNonzeroIsNeg tl) := by
  grind [FirstNonzeroIsNeg]

theorem not_FirstNonzeroIsPos {li : UnitMonomial} (h : FirstNonzeroIsNeg li) :
    ¬ FirstNonzeroIsPos li := by
  induction li with
  | nil => simp [FirstNonzeroIsPos]
  | cons hd tl ih => grind [FirstNonzeroIsNeg, FirstNonzeroIsPos]

end FirstNonzeroIsNeg

end Tactic.ComputeAsymptotics.UnitMonomial
