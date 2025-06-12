/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Order.RelClasses

/-!
# Deprecated instances about order structures.
-/

variable {α : Type*}

@[deprecated "This was a leftover from Lean 3, and has not been needed." (since := "2024-11-26")]
instance isStrictTotalOrder_of_linearOrder [LinearOrder α] : IsStrictTotalOrder α (· < ·) where
  irrefl := lt_irrefl
  trichotomous := lt_trichotomy

section Preorder

variable [MulOneClass α] [Zero α] [Preorder α] {a b c : α}

/-! Lemmas of the form `b ≤ c → a ≤ 1 → b * a ≤ c`. -/

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem mul_le_of_le_of_le_one_of_nonneg [PosMulMono α] (h : b ≤ c) (ha : a ≤ 1) (hb : 0 ≤ b) :
    b * a ≤ c :=
  (mul_le_of_le_one_right hb ha).trans h

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem mul_lt_of_le_of_lt_one_of_pos [PosMulStrictMono α] (bc : b ≤ c) (ha : a < 1) (b0 : 0 < b) :
    b * a < c :=
  (mul_lt_of_lt_one_right b0 ha).trans_le bc

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem mul_lt_of_lt_of_le_one_of_nonneg [PosMulMono α] (h : b < c) (ha : a ≤ 1) (hb : 0 ≤ b) :
    b * a < c :=
  (mul_le_of_le_one_right hb ha).trans_lt h

set_option linter.deprecated false in
/-- Assumes left covariance. -/
@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem Left.mul_le_one_of_le_of_le [PosMulMono α] (ha : a ≤ 1) (hb : b ≤ 1) (a0 : 0 ≤ a) :
    a * b ≤ 1 :=
  mul_le_of_le_of_le_one_of_nonneg ha hb a0

set_option linter.deprecated false in
/-- Assumes left covariance. -/
@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem Left.mul_lt_of_le_of_lt_one_of_pos [PosMulStrictMono α] (ha : a ≤ 1) (hb : b < 1)
    (a0 : 0 < a) : a * b < 1 :=
  _root_.mul_lt_of_le_of_lt_one_of_pos ha hb a0

set_option linter.deprecated false in
/-- Assumes left covariance. -/
@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem Left.mul_lt_of_lt_of_le_one_of_nonneg [PosMulMono α] (ha : a < 1) (hb : b ≤ 1)
    (a0 : 0 ≤ a) : a * b < 1 :=
  _root_.mul_lt_of_lt_of_le_one_of_nonneg ha hb a0

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem mul_le_of_le_of_le_one' [PosMulMono α] [MulPosMono α] (bc : b ≤ c) (ha : a ≤ 1) (a0 : 0 ≤ a)
    (c0 : 0 ≤ c) : b * a ≤ c :=
  (mul_le_mul_of_nonneg_right bc a0).trans <| mul_le_of_le_one_right c0 ha

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem mul_lt_of_lt_of_le_one' [PosMulMono α] [MulPosStrictMono α] (bc : b < c) (ha : a ≤ 1)
    (a0 : 0 < a) (c0 : 0 ≤ c) : b * a < c :=
  (mul_lt_mul_of_pos_right bc a0).trans_le <| mul_le_of_le_one_right c0 ha

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem mul_lt_of_le_of_lt_one' [PosMulStrictMono α] [MulPosMono α] (bc : b ≤ c) (ha : a < 1)
    (a0 : 0 ≤ a) (c0 : 0 < c) : b * a < c :=
  (mul_le_mul_of_nonneg_right bc a0).trans_lt <| mul_lt_of_lt_one_right c0 ha

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem mul_lt_of_lt_of_lt_one_of_pos [PosMulMono α] [MulPosStrictMono α] (bc : b < c) (ha : a ≤ 1)
    (a0 : 0 < a) (c0 : 0 ≤ c) : b * a < c :=
  (mul_lt_mul_of_pos_right bc a0).trans_le <| mul_le_of_le_one_right c0 ha

/-! Lemmas of the form `b ≤ c → 1 ≤ a → b ≤ c * a`. -/


@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem le_mul_of_le_of_one_le_of_nonneg [PosMulMono α] (h : b ≤ c) (ha : 1 ≤ a) (hc : 0 ≤ c) :
    b ≤ c * a :=
  h.trans <| le_mul_of_one_le_right hc ha

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem lt_mul_of_le_of_one_lt_of_pos [PosMulStrictMono α] (bc : b ≤ c) (ha : 1 < a) (c0 : 0 < c) :
    b < c * a :=
  bc.trans_lt <| lt_mul_of_one_lt_right c0 ha

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem lt_mul_of_lt_of_one_le_of_nonneg [PosMulMono α] (h : b < c) (ha : 1 ≤ a) (hc : 0 ≤ c) :
    b < c * a :=
  h.trans_le <| le_mul_of_one_le_right hc ha

set_option linter.deprecated false in
/-- Assumes left covariance. -/
@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem Left.one_le_mul_of_le_of_le [PosMulMono α] (ha : 1 ≤ a) (hb : 1 ≤ b) (a0 : 0 ≤ a) :
    1 ≤ a * b :=
  le_mul_of_le_of_one_le_of_nonneg ha hb a0

set_option linter.deprecated false in
/-- Assumes left covariance. -/
@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem Left.one_lt_mul_of_le_of_lt_of_pos [PosMulStrictMono α] (ha : 1 ≤ a) (hb : 1 < b)
    (a0 : 0 < a) : 1 < a * b :=
  lt_mul_of_le_of_one_lt_of_pos ha hb a0

set_option linter.deprecated false in
/-- Assumes left covariance. -/
@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem Left.lt_mul_of_lt_of_one_le_of_nonneg [PosMulMono α] (ha : 1 < a) (hb : 1 ≤ b)
    (a0 : 0 ≤ a) : 1 < a * b :=
  _root_.lt_mul_of_lt_of_one_le_of_nonneg ha hb a0

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem le_mul_of_le_of_one_le' [PosMulMono α] [MulPosMono α] (bc : b ≤ c) (ha : 1 ≤ a)
    (a0 : 0 ≤ a) (b0 : 0 ≤ b) : b ≤ c * a :=
  (le_mul_of_one_le_right b0 ha).trans <| mul_le_mul_of_nonneg_right bc a0

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem lt_mul_of_le_of_one_lt' [PosMulStrictMono α] [MulPosMono α] (bc : b ≤ c) (ha : 1 < a)
    (a0 : 0 ≤ a) (b0 : 0 < b) : b < c * a :=
  (lt_mul_of_one_lt_right b0 ha).trans_le <| mul_le_mul_of_nonneg_right bc a0

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem lt_mul_of_lt_of_one_le' [PosMulMono α] [MulPosStrictMono α] (bc : b < c) (ha : 1 ≤ a)
    (a0 : 0 < a) (b0 : 0 ≤ b) : b < c * a :=
  (le_mul_of_one_le_right b0 ha).trans_lt <| mul_lt_mul_of_pos_right bc a0

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem lt_mul_of_lt_of_one_lt_of_pos [PosMulStrictMono α] [MulPosStrictMono α] (bc : b < c)
    (ha : 1 < a) (a0 : 0 < a) (b0 : 0 < b) : b < c * a :=
  (lt_mul_of_one_lt_right b0 ha).trans <| mul_lt_mul_of_pos_right bc a0

/-! Lemmas of the form `a ≤ 1 → b ≤ c → a * b ≤ c`. -/


@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem mul_le_of_le_one_of_le_of_nonneg [MulPosMono α] (ha : a ≤ 1) (h : b ≤ c) (hb : 0 ≤ b) :
    a * b ≤ c :=
  (mul_le_of_le_one_left hb ha).trans h

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem mul_lt_of_lt_one_of_le_of_pos [MulPosStrictMono α] (ha : a < 1) (h : b ≤ c) (hb : 0 < b) :
    a * b < c :=
  (mul_lt_of_lt_one_left hb ha).trans_le h

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem mul_lt_of_le_one_of_lt_of_nonneg [MulPosMono α] (ha : a ≤ 1) (h : b < c) (hb : 0 ≤ b) :
    a * b < c :=
  (mul_le_of_le_one_left hb ha).trans_lt h

set_option linter.deprecated false in
/-- Assumes right covariance. -/
@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem Right.mul_lt_one_of_lt_of_le_of_pos [MulPosStrictMono α] (ha : a < 1) (hb : b ≤ 1)
    (b0 : 0 < b) : a * b < 1 :=
  mul_lt_of_lt_one_of_le_of_pos ha hb b0

set_option linter.deprecated false in
/-- Assumes right covariance. -/
@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem Right.mul_lt_one_of_le_of_lt_of_nonneg [MulPosMono α] (ha : a ≤ 1) (hb : b < 1)
    (b0 : 0 ≤ b) : a * b < 1 :=
  mul_lt_of_le_one_of_lt_of_nonneg ha hb b0

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem mul_lt_of_lt_one_of_lt_of_pos [PosMulStrictMono α] [MulPosStrictMono α] (ha : a < 1)
    (bc : b < c) (a0 : 0 < a) (c0 : 0 < c) : a * b < c :=
  (mul_lt_mul_of_pos_left bc a0).trans <| mul_lt_of_lt_one_left c0 ha

set_option linter.deprecated false in
/-- Assumes right covariance. -/
@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem Right.mul_le_one_of_le_of_le [MulPosMono α] (ha : a ≤ 1) (hb : b ≤ 1) (b0 : 0 ≤ b) :
    a * b ≤ 1 :=
  mul_le_of_le_one_of_le_of_nonneg ha hb b0

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem mul_le_of_le_one_of_le' [PosMulMono α] [MulPosMono α] (ha : a ≤ 1) (bc : b ≤ c) (a0 : 0 ≤ a)
    (c0 : 0 ≤ c) : a * b ≤ c :=
  (mul_le_mul_of_nonneg_left bc a0).trans <| mul_le_of_le_one_left c0 ha

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem mul_lt_of_lt_one_of_le' [PosMulMono α] [MulPosStrictMono α] (ha : a < 1) (bc : b ≤ c)
    (a0 : 0 ≤ a) (c0 : 0 < c) : a * b < c :=
  (mul_le_mul_of_nonneg_left bc a0).trans_lt <| mul_lt_of_lt_one_left c0 ha

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem mul_lt_of_le_one_of_lt' [PosMulStrictMono α] [MulPosMono α] (ha : a ≤ 1) (bc : b < c)
    (a0 : 0 < a) (c0 : 0 ≤ c) : a * b < c :=
  (mul_lt_mul_of_pos_left bc a0).trans_le <| mul_le_of_le_one_left c0 ha

/-! Lemmas of the form `1 ≤ a → b ≤ c → b ≤ a * c`. -/


@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem lt_mul_of_one_lt_of_le_of_pos [MulPosStrictMono α] (ha : 1 < a) (h : b ≤ c) (hc : 0 < c) :
    b < a * c :=
  h.trans_lt <| lt_mul_of_one_lt_left hc ha

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem lt_mul_of_one_le_of_lt_of_nonneg [MulPosMono α] (ha : 1 ≤ a) (h : b < c) (hc : 0 ≤ c) :
    b < a * c :=
  h.trans_le <| le_mul_of_one_le_left hc ha

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem lt_mul_of_one_lt_of_lt_of_pos [MulPosStrictMono α] (ha : 1 < a) (h : b < c) (hc : 0 < c) :
    b < a * c :=
  h.trans <| lt_mul_of_one_lt_left hc ha

set_option linter.deprecated false in
/-- Assumes right covariance. -/
@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem Right.one_lt_mul_of_lt_of_le_of_pos [MulPosStrictMono α] (ha : 1 < a) (hb : 1 ≤ b)
    (b0 : 0 < b) : 1 < a * b :=
  lt_mul_of_one_lt_of_le_of_pos ha hb b0

set_option linter.deprecated false in
/-- Assumes right covariance. -/
@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem Right.one_lt_mul_of_le_of_lt_of_nonneg [MulPosMono α] (ha : 1 ≤ a) (hb : 1 < b)
    (b0 : 0 ≤ b) : 1 < a * b :=
  lt_mul_of_one_le_of_lt_of_nonneg ha hb b0

set_option linter.deprecated false in
/-- Assumes right covariance. -/
@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem Right.one_lt_mul_of_lt_of_lt [MulPosStrictMono α] (ha : 1 < a) (hb : 1 < b) (b0 : 0 < b) :
    1 < a * b :=
  lt_mul_of_one_lt_of_lt_of_pos ha hb b0

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem lt_mul_of_one_lt_of_lt_of_nonneg [MulPosMono α] (ha : 1 ≤ a) (h : b < c) (hc : 0 ≤ c) :
    b < a * c :=
  h.trans_le <| le_mul_of_one_le_left hc ha

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem lt_of_mul_lt_of_one_le_of_nonneg_left [PosMulMono α] (h : a * b < c) (hle : 1 ≤ b)
    (ha : 0 ≤ a) : a < c :=
  (le_mul_of_one_le_right ha hle).trans_lt h

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem lt_of_lt_mul_of_le_one_of_nonneg_left [PosMulMono α] (h : a < b * c) (hc : c ≤ 1)
    (hb : 0 ≤ b) : a < b :=
  h.trans_le <| mul_le_of_le_one_right hb hc

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem lt_of_lt_mul_of_le_one_of_nonneg_right [MulPosMono α] (h : a < b * c) (hb : b ≤ 1)
    (hc : 0 ≤ c) : a < c :=
  h.trans_le <| mul_le_of_le_one_left hc hb

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem le_mul_of_one_le_of_le_of_nonneg [MulPosMono α] (ha : 1 ≤ a) (bc : b ≤ c) (c0 : 0 ≤ c) :
    b ≤ a * c :=
  bc.trans <| le_mul_of_one_le_left c0 ha

set_option linter.deprecated false in
/-- Assumes right covariance. -/
@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem Right.one_le_mul_of_le_of_le [MulPosMono α] (ha : 1 ≤ a) (hb : 1 ≤ b) (b0 : 0 ≤ b) :
    1 ≤ a * b :=
  le_mul_of_one_le_of_le_of_nonneg ha hb b0

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem le_of_mul_le_of_one_le_of_nonneg_left [PosMulMono α] (h : a * b ≤ c) (hb : 1 ≤ b)
    (ha : 0 ≤ a) : a ≤ c :=
  (le_mul_of_one_le_right ha hb).trans h

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem le_of_le_mul_of_le_one_of_nonneg_left [PosMulMono α] (h : a ≤ b * c) (hc : c ≤ 1)
    (hb : 0 ≤ b) : a ≤ b :=
  h.trans <| mul_le_of_le_one_right hb hc

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem le_of_mul_le_of_one_le_nonneg_right [MulPosMono α] (h : a * b ≤ c) (ha : 1 ≤ a)
    (hb : 0 ≤ b) : b ≤ c :=
  (le_mul_of_one_le_left hb ha).trans h

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2025-02-27")]
theorem le_of_le_mul_of_le_one_of_nonneg_right [MulPosMono α] (h : a ≤ b * c) (hb : b ≤ 1)
    (hc : 0 ≤ c) : a ≤ c :=
  h.trans <| mul_le_of_le_one_left hc hb

end Preorder

section LinearOrder

variable [MulOneClass α] [Zero α] [LinearOrder α] {a b c : α}

-- proven with `a0 : 0 ≤ a` as `exists_square_le`
@[deprecated "No replacement." (since := "2025-02-27")]
theorem exists_square_le' [PosMulStrictMono α] (a0 : 0 < a) : ∃ b : α, b * b ≤ a := by
  obtain ha | ha := lt_or_ge a 1
  · exact ⟨a, (mul_lt_of_lt_one_right a0 ha).le⟩
  · exact ⟨1, by rwa [mul_one]⟩

end LinearOrder
