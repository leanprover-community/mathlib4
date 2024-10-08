/-
Copyright (c) 2022 Abby J. Goldberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abby J. Goldberg, Mario Carneiro, Heather Macbeth
-/
import Mathlib.Tactic.Positivity.Core
import Mathlib.Algebra.Order.Field.Basic

/-!
# Lemmas for the linear_combination tactic

These should not be used directly in user code.
-/

namespace Mathlib.Tactic.LinearCombination
open Lean

variable {α : Type*} {a a' a₁ a₂ b b' b₁ b₂ c : α}

/-! ### Addition -/

theorem add_eq_eq [Add α] (p₁ : (a₁:α) = b₁) (p₂ : a₂ = b₂) : a₁ + a₂ = b₁ + b₂ := p₁ ▸ p₂ ▸ rfl

theorem add_le_eq [OrderedAddCommMonoid α]
    (p₁ : (a₁:α) ≤ b₁) (p₂ : a₂ = b₂) : a₁ + a₂ ≤ b₁ + b₂ :=
  p₂ ▸ add_le_add_right p₁ b₂

theorem add_eq_le [OrderedAddCommMonoid α]
    (p₁ : (a₁:α) = b₁) (p₂ : a₂ ≤ b₂) : a₁ + a₂ ≤ b₁ + b₂ :=
  p₁ ▸ add_le_add_left p₂ b₁

theorem add_lt_eq [OrderedCancelAddCommMonoid α]
    (p₁ : (a₁:α) < b₁) (p₂ : a₂ = b₂) : a₁ + a₂ < b₁ + b₂ :=
  p₂ ▸ add_lt_add_right p₁ b₂

theorem add_eq_lt [OrderedCancelAddCommMonoid α] {a₁ b₁ a₂ b₂ : α}
    (p₁ : a₁ = b₁) (p₂ : a₂ < b₂) : a₁ + a₂ < b₁ + b₂ :=
  p₁ ▸ add_lt_add_left p₂ b₁

/-! ### Multiplication -/

theorem mul_eq_const [Mul α] (p : a = b) (c : α) : a * c = b * c := p ▸ rfl

theorem mul_le_const [OrderedSemiring α] (p : b ≤ c) (a : α) (ha : 0 ≤ a := by positivity) :
    b * a ≤ c * a :=
  mul_le_mul_of_nonneg_right p ha

theorem mul_lt_const [StrictOrderedSemiring α] (p : b < c) (a : α) (ha : 0 < a := by positivity) :
    b * a < c * a :=
  mul_lt_mul_of_pos_right p ha

-- FIXME allow for this variant
theorem mul_lt_const_weak [OrderedSemiring α] (p : b < c) (a : α) (ha : 0 ≤ a := by positivity) :
    b * a ≤ c * a :=
  mul_le_mul_of_nonneg_right p.le ha

theorem mul_const_eq [Mul α] (p : b = c) (a : α) : a * b = a * c := p ▸ rfl

theorem mul_const_le [OrderedSemiring α] (p : b ≤ c) (a : α) (ha : 0 ≤ a := by positivity) :
    a * b ≤ a * c :=
  mul_le_mul_of_nonneg_left p ha

theorem mul_const_lt [StrictOrderedSemiring α] (p : b < c) (a : α) (ha : 0 < a := by positivity) :
    a * b < a * c :=
  mul_lt_mul_of_pos_left p ha

-- FIXME allow for this variant
theorem mul_const_lt_weak [OrderedSemiring α] (p : b < c) (a : α) (ha : 0 ≤ a := by positivity) :
    a * b ≤ a * c :=
  mul_le_mul_of_nonneg_left p.le ha

/-! ### Division -/

theorem div_eq_const [Div α] (p : a = b) (c : α) : a / c = b / c := p ▸ rfl

theorem div_le_const [LinearOrderedSemifield α] (p : b ≤ c) (a : α)
    (ha : 0 ≤ a := by positivity) : b / a ≤ c / a :=
  div_le_div_of_nonneg_right p ha

theorem div_lt_const [LinearOrderedSemifield α] (p : b < c) (a : α)
    (ha : 0 < a := by positivity) : b / a < c / a :=
  div_lt_div_of_pos_right p ha

-- FIXME allow for this variant
theorem div_lt_const_weak [LinearOrderedSemifield α] (p : b < c) (a : α)
    (ha : 0 ≤ a := by positivity) : b / a ≤ c / a :=
  div_le_div_of_nonneg_right p.le ha

/-! ### Lemmas constructing the reduction of a goal to a specified built-up hypothesis -/

theorem eq_of_eq [Add α] [IsRightCancelAdd α] (p : (a:α) = b) (H : a' + b = b' + a) : a' = b' := by
  rw [p] at H
  exact add_right_cancel H

theorem le_of_le [OrderedCancelAddCommMonoid α] (p : (a:α) ≤ b) (H : a' + b ≤ b' + a) :
    a' ≤ b' := by
  rw [← add_le_add_iff_right b]
  apply H.trans
  apply add_le_add_left p

theorem le_of_eq [OrderedCancelAddCommMonoid α] (p : (a:α) = b) (H : a' + b ≤ b' + a) :
    a' ≤ b' := by
  rwa [p, add_le_add_iff_right] at H

theorem le_of_lt [OrderedCancelAddCommMonoid α] (p : (a:α) < b) (H : a' + b ≤ b' + a) :
    a' ≤ b' :=
  le_of_le p.le H

theorem lt_of_le [OrderedCancelAddCommMonoid α] (p : (a:α) ≤ b) (H : a' + b < b' + a) :
    a' < b' := by
  rw [← add_lt_add_iff_right b]
  apply H.trans_le
  apply add_le_add_left p

theorem lt_of_eq [OrderedCancelAddCommMonoid α] (p : (a:α) = b) (H : a' + b < b' + a) :
    a' < b' := by
  rwa [p, add_lt_add_iff_right] at H

theorem lt_of_lt [OrderedCancelAddCommMonoid α] (p : (a:α) < b) (H : a' + b ≤ b' + a) :
    a' < b' := by
  rw [← add_lt_add_iff_right b]
  apply H.trans_lt
  apply add_lt_add_left p

alias ⟨eq_rearrange, _⟩ := sub_eq_zero

theorem le_rearrange {α : Type*} [OrderedAddCommGroup α] {a b : α} (h : a - b ≤ 0) : a ≤ b :=
  sub_nonpos.mp h

theorem lt_rearrange {α : Type*} [OrderedAddCommGroup α] {a b : α} (h : a - b < 0) : a < b :=
  sub_neg.mp h

theorem eq_of_add_pow [Ring α] [NoZeroDivisors α] (n : ℕ) (p : (a:α) = b)
    (H : (a' - b')^n - (a - b) = 0) : a' = b' := by
  rw [← sub_eq_zero] at p ⊢; apply pow_eq_zero (n := n); rwa [sub_eq_zero, p] at H

/-! ### Lookup functions for lemmas by operation and relation(s) -/

/-- The type of a relation appearing in the `linear_combination` tactic: `=`, `≤` or `<`. -/
inductive RelType
  | Eq
  | Le
  | Lt
  deriving Repr, ToExpr

export RelType (Eq Le Lt)

/-- Given an expression `e`, parse it as a `=`, `≤` or `<`, and return this relation (as a
`Mathlib.Tactic.LinearCombination.RelType`) together with the type in which the (in)equality occurs.
-/
def _root_.Lean.Expr.relType (e : Expr) : Option (RelType × Expr) :=
  match e.eq? with
  | some (ty, _, _) => (Eq, ty)
  | none =>
  match e.le? with
  | some (ty, _, _) => (Le, ty)
  | none =>
  match e.lt? with
  | some (ty, _, _) => (Lt, ty)
  | none => none

/-- Given two (in)equalities, look up the lemma to add them and the relation in the result. -/
def RelType.addRelRelData : RelType → RelType → RelType × Name
  | Eq, Eq => (Eq, ``add_eq_eq)
  | Eq, Le => (Le, ``add_eq_le)
  | Eq, Lt => (Lt, ``add_eq_lt)
  | Le, Eq => (Le, ``add_le_eq)
  | Le, Le => (Le, ``add_le_add)
  | Le, Lt => (Lt, ``add_lt_add_of_le_of_lt)
  | Lt, Eq => (Lt, ``add_lt_eq)
  | Lt, Le => (Lt, ``add_lt_add_of_lt_of_le)
  | Lt, Lt => (Lt, ``add_lt_add)

/-- Given an (in)equality, look up the lemma to left-multiply it by a constant and the relation in
the result. -/
def RelType.mulConstRelData : RelType → RelType × Name
  | Eq => (Eq, ``mul_const_eq)
  | Le => (Le, ``mul_const_le)
  | Lt => (Lt, ``mul_const_lt)

/-- Given an (in)equality, look up the lemma to right-multiply it by a constant and the relation in
the result. -/
def RelType.mulRelConstData : RelType → RelType × Name
  | Eq => (Eq, ``mul_eq_const)
  | Le => (Le, ``mul_le_const)
  | Lt => (Lt, ``mul_lt_const)

/-- Given an (in)equality, look up the lemma to divide it by a constant and the relation in the
result. -/
def RelType.divRelConstData : RelType → RelType × Name
  | Eq => (Eq, ``div_eq_const)
  | Le => (Le, ``div_le_const)
  | Lt => (Lt, ``div_lt_const)

/-- Given two (in)equalities `P` and `Q`, look up the lemma to deduce `Q` from `P`, and the relation
appearing in the side condition produced by this lemma. -/
def RelType.relImpRelData : RelType → RelType → Option (Name × RelType)
  | Eq, Eq => some (``eq_of_eq, Eq)
  | Eq, Le => some (``le_of_eq, Le)
  | Eq, Lt => some (``lt_of_eq, Lt)
  | Le, Eq => none
  | Le, Le => some (``le_of_le, Le)
  | Le, Lt => some (``lt_of_le, Lt)
  | Lt, Eq => none
  | Lt, Le => some (``le_of_lt, Le)
  | Lt, Lt => some (``lt_of_lt, Le)

/-- Given an (in)equality, look up the lemma to move everything to the LHS. -/
def RelType.rearrangeData : RelType → Name
  | Eq => ``eq_rearrange
  | Le => ``le_rearrange
  | Lt => ``lt_rearrange

end Mathlib.Tactic.LinearCombination
