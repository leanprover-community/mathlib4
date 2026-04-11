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
theorem nil : AllZero [] :=
  List.forall_mem_nil _

@[simp]
theorem cons_iff {hd : ℝ} {tl : UnitMonomial} :
    AllZero (hd :: tl) ↔ hd = 0 ∧ AllZero tl := by
  simp [AllZero]

theorem of_head {hd : ℝ} (tl : UnitMonomial) (h : 0 < hd) :
    FirstNonzeroIsPos (hd :: tl) :=
  Or.inl h

theorem of_tail {hd : ℝ} {tl : UnitMonomial} (h_hd : hd = 0) (h_tl : AllZero tl) :
    AllZero (hd :: tl) :=
  List.forall_mem_cons.mpr ⟨h_hd, h_tl⟩

theorem replicate {n : ℕ} : AllZero (List.replicate n 0) := by
  simp [AllZero]

theorem not_FirstNonzeroIsPos {li : UnitMonomial} (h : AllZero li) :
    ¬ FirstNonzeroIsPos li := by
  induction li with
  | nil => exact not_false
  | cons hd tl ih => grind [cons_iff, FirstNonzeroIsPos]

theorem not_FirstNonzeroIsNeg {li : UnitMonomial} (h : AllZero li) :
    ¬ FirstNonzeroIsNeg li := by
  induction li with
  | nil => exact not_false
  | cons hd tl ih => grind [cons_iff, FirstNonzeroIsNeg]

end AllZero

namespace FirstNonzeroIsPos

@[simp]
theorem not_nil : ¬ FirstNonzeroIsPos [] := not_false

theorem of_head {hd : ℝ} (tl : UnitMonomial) (h_hd : 0 < hd) :
    FirstNonzeroIsPos (hd :: tl) :=
  Or.inl h_hd

theorem of_tail {hd : ℝ} {tl : UnitMonomial} (h_hd : hd = 0)
    (h_tl : FirstNonzeroIsPos tl) :
    FirstNonzeroIsPos (hd :: tl) :=
  Or.inr ⟨h_hd, h_tl⟩

@[simp]
theorem cons_iff {hd : ℝ} {tl : UnitMonomial} :
    FirstNonzeroIsPos (hd :: tl) ↔ 0 < hd ∨ (hd = 0 ∧ FirstNonzeroIsPos tl) := by
  rfl

theorem not_AllZero {li : UnitMonomial} (h : FirstNonzeroIsPos li) :
    ¬ AllZero li :=
  fun h' ↦ h'.not_FirstNonzeroIsPos h

theorem not_FirstNonzeroIsNeg {li : UnitMonomial} (h : FirstNonzeroIsPos li) :
    ¬ FirstNonzeroIsNeg li := by
  induction li with
  | nil => exact not_false
  | cons hd tl ih => grind [cons_iff, FirstNonzeroIsNeg]

end FirstNonzeroIsPos

namespace FirstNonzeroIsNeg

@[simp]
theorem not_nil : ¬ FirstNonzeroIsNeg [] := not_false

theorem of_head {hd : ℝ} (tl : UnitMonomial) (h_hd : hd < 0) :
    FirstNonzeroIsNeg (hd :: tl) :=
  Or.inl h_hd

theorem of_tail {hd : ℝ} {tl : UnitMonomial} (h_hd : hd = 0)
    (h_tl : FirstNonzeroIsNeg tl) :
    FirstNonzeroIsNeg (hd :: tl) :=
  Or.inr ⟨h_hd, h_tl⟩

@[simp]
theorem cons_iff {hd : ℝ} {tl : UnitMonomial} :
    FirstNonzeroIsNeg (hd :: tl) ↔ hd < 0 ∨ (hd = 0 ∧ FirstNonzeroIsNeg tl) := by
  rfl

theorem not_AllZero {li : UnitMonomial} (h : FirstNonzeroIsNeg li) :
    ¬ AllZero li :=
  fun h' ↦ h'.not_FirstNonzeroIsNeg h

theorem not_FirstNonzeroIsPos {li : UnitMonomial} (h : FirstNonzeroIsNeg li) :
    ¬ FirstNonzeroIsPos li :=
  fun h' ↦ h'.not_FirstNonzeroIsNeg h

end FirstNonzeroIsNeg

end Tactic.ComputeAsymptotics.UnitMonomial
