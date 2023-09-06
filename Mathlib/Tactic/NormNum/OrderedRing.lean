/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Algebra.Order.Field.Defs

/-!
# `norm_num` extensions for inequalities.
-/

set_option autoImplicit true

open Lean Meta Qq

namespace Mathlib.Meta.NormNum

/-- Helper function to synthesize a typed `OrderedSemiring α` expression. -/
def inferOrderedSemiring (α : Q(Type u)) : MetaM Q(OrderedSemiring $α) :=
  return ← synthInstanceQ (q(OrderedSemiring $α) : Q(Type u)) <|>
    throwError "not an ordered semiring"

/-- Helper function to synthesize a typed `OrderedRing α` expression. -/
def inferOrderedRing (α : Q(Type u)) : MetaM Q(OrderedRing $α) :=
  return ← synthInstanceQ (q(OrderedRing $α) : Q(Type u)) <|> throwError "not an ordered ring"

/-- Helper function to synthesize a typed `LinearOrderedField α` expression. -/
def inferLinearOrderedField (α : Q(Type u)) : MetaM Q(LinearOrderedField $α) :=
  return ← synthInstanceQ (q(LinearOrderedField $α) : Q(Type u)) <|>
    throwError "not a linear ordered field"

theorem isRat_le_true [LinearOrderedRing α] : {a b : α} → {na nb : ℤ} → {da db : ℕ} →
    IsRat a na da → IsRat b nb db →
    decide (Int.mul na (.ofNat db) ≤ Int.mul nb (.ofNat da)) → a ≤ b
  | _, _, _, _, da, db, ⟨_, rfl⟩, ⟨_, rfl⟩, h => by
    have h := Int.cast_mono (α := α) <| of_decide_eq_true h
    have ha : 0 ≤ ⅟(da : α) := invOf_nonneg.mpr <| Nat.cast_nonneg da
    have hb : 0 ≤ ⅟(db : α) := invOf_nonneg.mpr <| Nat.cast_nonneg db
    have h := (mul_le_mul_of_nonneg_left · hb) <| mul_le_mul_of_nonneg_right h ha
    rw [← mul_assoc, Int.commute_cast] at h
    simp at h; rwa [Int.commute_cast] at h

theorem isRat_lt_true [LinearOrderedRing α] [Nontrivial α] : {a b : α} → {na nb : ℤ} → {da db : ℕ} →
    IsRat a na da → IsRat b nb db → decide (na * db < nb * da) → a < b
  | _, _, _, _, da, db, ⟨_, rfl⟩, ⟨_, rfl⟩, h => by
    have h := Int.cast_strictMono (α := α) <| of_decide_eq_true h
    have ha : 0 < ⅟(da : α) := pos_invOf_of_invertible_cast da
    have hb : 0 < ⅟(db : α) := pos_invOf_of_invertible_cast db
    have h := (mul_lt_mul_of_pos_left · hb) <| mul_lt_mul_of_pos_right h ha
    rw [← mul_assoc, Int.commute_cast] at h
    simp at h
    rwa [Int.commute_cast] at h

theorem isRat_le_false [LinearOrderedRing α] [Nontrivial α] {a b : α} {na nb : ℤ} {da db : ℕ}
    (ha : IsRat a na da) (hb : IsRat b nb db) (h : decide (nb * da < na * db)) : ¬a ≤ b :=
  not_le_of_lt (isRat_lt_true hb ha h)

theorem isRat_lt_false [LinearOrderedRing α] {a b : α} {na nb : ℤ} {da db : ℕ}
    (ha : IsRat a na da) (hb : IsRat b nb db) (h : decide (nb * da ≤ na * db)) : ¬a < b :=
  not_lt_of_le (isRat_le_true hb ha h)

end Mathlib.Meta.NormNum
