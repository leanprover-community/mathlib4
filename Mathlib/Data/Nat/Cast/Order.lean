/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Data.Nat.Cast.NeZero
import Mathlib.Data.Nat.Order.Basic

#align_import data.nat.cast.basic from "leanprover-community/mathlib"@"acebd8d49928f6ed8920e502a6c90674e75bd441"

/-!
# Cast of natural numbers: lemmas about order

-/

variable {α β : Type*}

namespace Nat

section OrderedSemiring
/- Note: even though the section indicates `OrderedSemiring`, which is the common use case,
we use a generic collection of instances so that it applies in other settings (e.g., in a
`StarOrderedRing`, or the `selfAdjoint` or `StarOrderedRing.positive` parts thereof). -/

variable [AddCommMonoidWithOne α] [PartialOrder α]
variable [CovariantClass α α (· + ·) (· ≤ ·)] [ZeroLEOneClass α]

@[mono]
theorem mono_cast : Monotone (Nat.cast : ℕ → α) :=
  monotone_nat_of_le_succ fun n ↦ by
    rw [Nat.cast_succ]; exact le_add_of_nonneg_right zero_le_one

/-- See also `Nat.cast_nonneg`, specialised for an `OrderedSemiring`. -/
@[simp low]
theorem cast_nonneg' (n : ℕ) : 0 ≤ (n : α) :=
  @Nat.cast_zero α _ ▸ mono_cast (Nat.zero_le n)

/-- Specialisation of `Nat.cast_nonneg'`, which seems to be easier for Lean to use. -/
@[simp]
theorem cast_nonneg {α} [OrderedSemiring α] (n : ℕ) : 0 ≤ (n : α) :=
  cast_nonneg' n

@[simp, norm_cast]
theorem cast_min {α} [LinearOrderedSemiring α] {a b : ℕ} : ((min a b : ℕ) : α) = min (a : α) b :=
  (@mono_cast α _).map_min

@[simp, norm_cast]
theorem cast_max {α} [LinearOrderedSemiring α] {a b : ℕ} : ((max a b : ℕ) : α) = max (a : α) b :=
  (@mono_cast α _).map_max

section Nontrivial

variable [NeZero (1 : α)]

theorem cast_add_one_pos (n : ℕ) : 0 < (n : α) + 1 :=
  zero_lt_one.trans_le <| le_add_of_nonneg_left n.cast_nonneg'

/-- See also `Nat.cast_pos`, a specialisation of this to an `OrderedSemiring`. -/
@[simp low]
theorem cast_pos' {n : ℕ} : (0 : α) < n ↔ 0 < n := by cases n <;> simp [cast_add_one_pos]

/-- Specialisation of `Nat.cast_pos'`, which seems to be easier for Lean to use. -/
@[simp]
theorem cast_pos {α} [OrderedSemiring α] [Nontrivial α] {n : ℕ} : (0 : α) < n ↔ 0 < n := cast_pos'

end Nontrivial

variable [CharZero α] {m n : ℕ}

theorem strictMono_cast : StrictMono (Nat.cast : ℕ → α) :=
  mono_cast.strictMono_of_injective cast_injective

/-- `Nat.cast : ℕ → α` as an `OrderEmbedding` -/
@[simps! (config := { fullyApplied := false })]
def castOrderEmbedding : ℕ ↪o α :=
  OrderEmbedding.ofStrictMono Nat.cast Nat.strictMono_cast

@[simp, norm_cast]
theorem cast_le : (m : α) ≤ n ↔ m ≤ n :=
  strictMono_cast.le_iff_le

@[simp, norm_cast, mono]
theorem cast_lt : (m : α) < n ↔ m < n :=
  strictMono_cast.lt_iff_lt

@[simp, norm_cast]
theorem one_lt_cast : 1 < (n : α) ↔ 1 < n := by rw [← cast_one, cast_lt]

@[simp, norm_cast]
theorem one_le_cast : 1 ≤ (n : α) ↔ 1 ≤ n := by rw [← cast_one, cast_le]

@[simp, norm_cast]
theorem cast_lt_one : (n : α) < 1 ↔ n = 0 := by
  rw [← cast_one, cast_lt, lt_succ_iff, ← bot_eq_zero, le_bot_iff]

@[simp, norm_cast]
theorem cast_le_one : (n : α) ≤ 1 ↔ n ≤ 1 := by rw [← cast_one, cast_le]

end OrderedSemiring

/-- A version of `Nat.cast_sub` that works for `ℝ≥0` and `ℚ≥0`. Note that this proof doesn't work
for `ℕ∞` and `ℝ≥0∞`, so we use type-specific lemmas for these types. -/
@[simp, norm_cast]
theorem cast_tsub [CanonicallyOrderedCommSemiring α] [Sub α] [OrderedSub α]
    [ContravariantClass α α (· + ·) (· ≤ ·)] (m n : ℕ) : ↑(m - n) = (m - n : α) := by
  cases' le_total m n with h h
  · rw [Nat.sub_eq_zero_of_le h, cast_zero, tsub_eq_zero_of_le]
    exact mono_cast h
  · rcases le_iff_exists_add'.mp h with ⟨m, rfl⟩
    rw [add_tsub_cancel_right, cast_add, add_tsub_cancel_right]

@[simp, norm_cast]
theorem abs_cast [LinearOrderedRing α] (a : ℕ) : |(a : α)| = a :=
  abs_of_nonneg (cast_nonneg a)

end Nat

instance [AddMonoidWithOne α] [CharZero α] : Nontrivial α where exists_pair_ne :=
  ⟨1, 0, (Nat.cast_one (R := α) ▸ Nat.cast_ne_zero.2 (by decide))⟩

section RingHomClass

variable {R S F : Type*} [NonAssocSemiring R] [NonAssocSemiring S]

theorem NeZero.nat_of_injective {n : ℕ} [h : NeZero (n : R)] [RingHomClass F R S] {f : F}
    (hf : Function.Injective f) : NeZero (n : S) :=
  ⟨fun h ↦ NeZero.natCast_ne n R <| hf <| by simpa only [map_natCast, map_zero f] ⟩

end RingHomClass
