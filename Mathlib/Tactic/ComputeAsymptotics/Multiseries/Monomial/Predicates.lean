/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

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

/-- Type representing a sign of the first non-zero exponent, returned by `sign`. -/
inductive Sign
| pos | neg | zero

/-- Sign of the first non-zero exponent of a unit monomial. -/
noncomputable def sign : UnitMonomial → Sign
  | [] => .zero
  | hd :: tl =>
    if 0 < hd then
      .pos
    else if hd < 0 then
      .neg
    else
      sign tl

/-- Predicate stating that the first non-zero exponent is positive. -/
def FirstNonzeroIsPos (m : UnitMonomial) : Prop := m.sign = .pos

/-- Predicate stating that the first non-zero exponent is negative. -/
def FirstNonzeroIsNeg (m : UnitMonomial) : Prop := m.sign = .neg

/-- Predicate stating that all exponents are zero. -/
def AllZero (m : UnitMonomial) : Prop := m.sign = .zero

namespace AllZero

theorem nil : AllZero [] :=
  rfl

@[simp]
theorem cons_iff {hd : ℝ} {tl : UnitMonomial} :
    AllZero (hd :: tl) ↔ hd = 0 ∧ AllZero tl := by
  grind [AllZero, sign]

theorem of_tail {hd : ℝ} {tl : UnitMonomial} (h_hd : hd = 0) (h_tl : AllZero tl) :
    AllZero (hd :: tl) :=
  cons_iff.mpr ⟨h_hd, h_tl⟩

theorem replicate {n : ℕ} : AllZero (List.replicate n 0) := by
  induction n <;> grind [AllZero, sign]

theorem not_FirstNonzeroIsPos {li : UnitMonomial} (h : AllZero li) :
    ¬ FirstNonzeroIsPos li := by
  grind [AllZero, FirstNonzeroIsPos]

theorem not_FirstNonzeroIsNeg {li : UnitMonomial} (h : AllZero li) :
    ¬ FirstNonzeroIsNeg li := by
  grind [AllZero, FirstNonzeroIsNeg]

end AllZero

namespace FirstNonzeroIsPos

@[simp]
theorem not_nil : ¬ FirstNonzeroIsPos [] := by simp [FirstNonzeroIsPos, sign]

@[simp]
theorem cons_iff {hd : ℝ} {tl : UnitMonomial} :
    FirstNonzeroIsPos (hd :: tl) ↔ 0 < hd ∨ (hd = 0 ∧ FirstNonzeroIsPos tl) := by
  grind [FirstNonzeroIsPos, sign]

theorem of_head {hd : ℝ} (tl : UnitMonomial) (h_hd : 0 < hd) :
    FirstNonzeroIsPos (hd :: tl) := by
  simp [h_hd]

theorem of_tail {hd : ℝ} {tl : UnitMonomial} (h_hd : hd = 0)
    (h_tl : FirstNonzeroIsPos tl) :
    FirstNonzeroIsPos (hd :: tl) := by
  simp [h_hd, h_tl]

theorem not_AllZero {li : UnitMonomial} (h : FirstNonzeroIsPos li) :
    ¬ AllZero li :=
  fun h' ↦ h'.not_FirstNonzeroIsPos h

theorem not_FirstNonzeroIsNeg {li : UnitMonomial} (h : FirstNonzeroIsPos li) :
    ¬ FirstNonzeroIsNeg li := by
  grind [FirstNonzeroIsPos, FirstNonzeroIsNeg]

end FirstNonzeroIsPos

namespace FirstNonzeroIsNeg

@[simp]
theorem not_nil : ¬ FirstNonzeroIsNeg [] := by simp [FirstNonzeroIsNeg, sign]

@[simp]
theorem cons_iff {hd : ℝ} {tl : UnitMonomial} :
    FirstNonzeroIsNeg (hd :: tl) ↔ hd < 0 ∨ (hd = 0 ∧ FirstNonzeroIsNeg tl) := by
  grind [FirstNonzeroIsNeg, sign]

theorem of_head {hd : ℝ} (tl : UnitMonomial) (h_hd : hd < 0) :
    FirstNonzeroIsNeg (hd :: tl) := by
  simp [h_hd]

theorem of_tail {hd : ℝ} {tl : UnitMonomial} (h_hd : hd = 0) (h_tl : FirstNonzeroIsNeg tl) :
    FirstNonzeroIsNeg (hd :: tl) := by
  simp [h_hd, h_tl]

theorem not_AllZero {li : UnitMonomial} (h : FirstNonzeroIsNeg li) :
    ¬ AllZero li :=
  fun h' ↦ h'.not_FirstNonzeroIsNeg h

theorem not_FirstNonzeroIsPos {li : UnitMonomial} (h : FirstNonzeroIsNeg li) :
    ¬ FirstNonzeroIsPos li :=
  fun h' ↦ h'.not_FirstNonzeroIsNeg h

end FirstNonzeroIsNeg

end Tactic.ComputeAsymptotics.UnitMonomial
