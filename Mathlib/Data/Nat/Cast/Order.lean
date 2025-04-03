/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Data.Nat.Cast.NeZero
import Mathlib.Algebra.Order.Ring.Nat

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

variable [AddMonoidWithOne α] [PartialOrder α]
variable [CovariantClass α α (· + ·) (· ≤ ·)] [ZeroLEOneClass α]

@[mono]
theorem mono_cast : Monotone (Nat.cast : ℕ → α) :=
  monotone_nat_of_le_succ fun n ↦ by
    rw [Nat.cast_succ]; exact le_add_of_nonneg_right zero_le_one
#align nat.mono_cast Nat.mono_cast

@[deprecated mono_cast] -- Since 2024-02-10
theorem cast_le_cast {a b : ℕ} (h : a ≤ b) : (a : α) ≤ b := mono_cast h

@[gcongr]
theorem _root_.GCongr.natCast_le_natCast {a b : ℕ} (h : a ≤ b) : (a : α) ≤ b := mono_cast h

/-- See also `Nat.cast_nonneg`, specialised for an `OrderedSemiring`. -/
@[simp low]
theorem cast_nonneg' (n : ℕ) : 0 ≤ (n : α) :=
  @Nat.cast_zero α _ ▸ mono_cast (Nat.zero_le n)

/-- Specialisation of `Nat.cast_nonneg'`, which seems to be easier for Lean to use. -/
@[simp]
theorem cast_nonneg {α} [OrderedSemiring α] (n : ℕ) : 0 ≤ (n : α) :=
  cast_nonneg' n
#align nat.cast_nonneg Nat.cast_nonneg

/-- See also `Nat.ofNat_nonneg`, specialised for an `OrderedSemiring`. -/
-- See note [no_index around OfNat.ofNat]
@[simp low]
theorem ofNat_nonneg' (n : ℕ) [n.AtLeastTwo] : 0 ≤ (no_index (OfNat.ofNat n : α)) := cast_nonneg' n

/-- Specialisation of `Nat.ofNat_nonneg'`, which seems to be easier for Lean to use. -/
-- See note [no_index around OfNat.ofNat]
@[simp]
theorem ofNat_nonneg {α} [OrderedSemiring α] (n : ℕ) [n.AtLeastTwo] :
    0 ≤ (no_index (OfNat.ofNat n : α)) :=
  ofNat_nonneg' n

@[simp, norm_cast]
theorem cast_min {α} [LinearOrderedSemiring α] {a b : ℕ} : ((min a b : ℕ) : α) = min (a : α) b :=
  (@mono_cast α _).map_min
#align nat.cast_min Nat.cast_min

@[simp, norm_cast]
theorem cast_max {α} [LinearOrderedSemiring α] {a b : ℕ} : ((max a b : ℕ) : α) = max (a : α) b :=
  (@mono_cast α _).map_max
#align nat.cast_max Nat.cast_max

section Nontrivial

variable [NeZero (1 : α)]

theorem cast_add_one_pos (n : ℕ) : 0 < (n : α) + 1 := by
  apply zero_lt_one.trans_le
  convert (@mono_cast α _).imp (?_ : 1 ≤ n + 1)
  <;> simp
#align nat.cast_add_one_pos Nat.cast_add_one_pos

/-- See also `Nat.cast_pos`, specialised for an `OrderedSemiring`. -/
@[simp low]
theorem cast_pos' {n : ℕ} : (0 : α) < n ↔ 0 < n := by cases n <;> simp [cast_add_one_pos]

/-- Specialisation of `Nat.cast_pos'`, which seems to be easier for Lean to use. -/
@[simp]
theorem cast_pos {α} [OrderedSemiring α] [Nontrivial α] {n : ℕ} : (0 : α) < n ↔ 0 < n := cast_pos'
#align nat.cast_pos Nat.cast_pos

/-- See also `Nat.ofNat_pos`, specialised for an `OrderedSemiring`. -/
-- See note [no_index around OfNat.ofNat]
@[simp low]
theorem ofNat_pos' {n : ℕ} [n.AtLeastTwo] : 0 < (no_index (OfNat.ofNat n : α)) :=
  cast_pos'.mpr (NeZero.pos n)

/-- Specialisation of `Nat.ofNat_pos'`, which seems to be easier for Lean to use. -/
-- See note [no_index around OfNat.ofNat]
@[simp]
theorem ofNat_pos {α} [OrderedSemiring α] [Nontrivial α] {n : ℕ} [n.AtLeastTwo] :
    0 < (no_index (OfNat.ofNat n : α)) :=
  ofNat_pos'

end Nontrivial

variable [CharZero α] {m n : ℕ}

theorem strictMono_cast : StrictMono (Nat.cast : ℕ → α) :=
  mono_cast.strictMono_of_injective cast_injective
#align nat.strict_mono_cast Nat.strictMono_cast

/-- `Nat.cast : ℕ → α` as an `OrderEmbedding` -/
@[simps! (config := .asFn)]
def castOrderEmbedding : ℕ ↪o α :=
  OrderEmbedding.ofStrictMono Nat.cast Nat.strictMono_cast
#align nat.cast_order_embedding Nat.castOrderEmbedding
#align nat.cast_order_embedding_apply Nat.castOrderEmbedding_apply

@[simp, norm_cast]
theorem cast_le : (m : α) ≤ n ↔ m ≤ n :=
  strictMono_cast.le_iff_le
#align nat.cast_le Nat.cast_le

@[simp, norm_cast, mono]
theorem cast_lt : (m : α) < n ↔ m < n :=
  strictMono_cast.lt_iff_lt
#align nat.cast_lt Nat.cast_lt

@[simp, norm_cast]
theorem one_lt_cast : 1 < (n : α) ↔ 1 < n := by rw [← cast_one, cast_lt]
#align nat.one_lt_cast Nat.one_lt_cast

@[simp, norm_cast]
theorem one_le_cast : 1 ≤ (n : α) ↔ 1 ≤ n := by rw [← cast_one, cast_le]
#align nat.one_le_cast Nat.one_le_cast

@[simp, norm_cast]
theorem cast_lt_one : (n : α) < 1 ↔ n = 0 := by
  rw [← cast_one, cast_lt, Nat.lt_succ_iff, ← bot_eq_zero, le_bot_iff]
#align nat.cast_lt_one Nat.cast_lt_one

@[simp, norm_cast]
theorem cast_le_one : (n : α) ≤ 1 ↔ n ≤ 1 := by rw [← cast_one, cast_le]
#align nat.cast_le_one Nat.cast_le_one

variable [m.AtLeastTwo] [n.AtLeastTwo]


-- TODO: These lemmas need to be `@[simp]` for confluence in the presence of `cast_lt`, `cast_le`,
-- and `Nat.cast_ofNat`, but their LHSs match literally every inequality, so they're too expensive.
-- If lean4#2867 is fixed in a performant way, these can be made `@[simp]`.

-- See note [no_index around OfNat.ofNat]
-- @[simp]
theorem ofNat_le :
    (no_index (OfNat.ofNat m : α)) ≤ (no_index (OfNat.ofNat n)) ↔
      (OfNat.ofNat m : ℕ) ≤ OfNat.ofNat n :=
  cast_le

-- See note [no_index around OfNat.ofNat]
-- @[simp]
theorem ofNat_lt :
    (no_index (OfNat.ofNat m : α)) < (no_index (OfNat.ofNat n)) ↔
      (OfNat.ofNat m : ℕ) < OfNat.ofNat n :=
  cast_lt

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem ofNat_le_cast : (no_index (OfNat.ofNat m : α)) ≤ n ↔ (OfNat.ofNat m : ℕ) ≤ n :=
  cast_le

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem ofNat_lt_cast : (no_index (OfNat.ofNat m : α)) < n ↔ (OfNat.ofNat m : ℕ) < n :=
  cast_lt

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem cast_le_ofNat : (m : α) ≤ (no_index (OfNat.ofNat n)) ↔ m ≤ OfNat.ofNat n :=
  cast_le

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem cast_lt_ofNat : (m : α) < (no_index (OfNat.ofNat n)) ↔ m < OfNat.ofNat n :=
  cast_lt

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem one_lt_ofNat : 1 < (no_index (OfNat.ofNat n : α)) :=
  one_lt_cast.mpr AtLeastTwo.one_lt

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem one_le_ofNat : 1 ≤ (no_index (OfNat.ofNat n : α)) :=
  one_le_cast.mpr NeZero.one_le

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem not_ofNat_le_one : ¬(no_index (OfNat.ofNat n : α)) ≤ 1 :=
  (cast_le_one.not.trans not_le).mpr AtLeastTwo.one_lt

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem not_ofNat_lt_one : ¬(no_index (OfNat.ofNat n : α)) < 1 :=
  mt le_of_lt not_ofNat_le_one

end OrderedSemiring

/-- A version of `Nat.cast_sub` that works for `ℝ≥0` and `ℚ≥0`. Note that this proof doesn't work
for `ℕ∞` and `ℝ≥0∞`, so we use type-specific lemmas for these types. -/
@[simp, norm_cast]
theorem cast_tsub [CanonicallyOrderedCommSemiring α] [Sub α] [OrderedSub α]
    [ContravariantClass α α (· + ·) (· ≤ ·)] (m n : ℕ) : ↑(m - n) = (m - n : α) := by
  rcases le_total m n with h | h
  · rw [Nat.sub_eq_zero_of_le h, cast_zero, tsub_eq_zero_of_le]
    exact mono_cast h
  · rcases le_iff_exists_add'.mp h with ⟨m, rfl⟩
    rw [add_tsub_cancel_right, cast_add, add_tsub_cancel_right]
#align nat.cast_tsub Nat.cast_tsub

@[simp, norm_cast]
theorem abs_cast [LinearOrderedRing α] (a : ℕ) : |(a : α)| = a :=
  abs_of_nonneg (cast_nonneg a)
#align nat.abs_cast Nat.abs_cast

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem abs_ofNat [LinearOrderedRing α] (n : ℕ) [n.AtLeastTwo] :
    |(no_index (OfNat.ofNat n : α))| = OfNat.ofNat n :=
  abs_cast n

end Nat

instance [AddMonoidWithOne α] [CharZero α] : Nontrivial α where exists_pair_ne :=
  ⟨1, 0, (Nat.cast_one (R := α) ▸ Nat.cast_ne_zero.2 (by decide))⟩

section RingHomClass

variable {R S F : Type*} [NonAssocSemiring R] [NonAssocSemiring S] [FunLike F R S]

theorem NeZero.nat_of_injective {n : ℕ} [h : NeZero (n : R)] [RingHomClass F R S] {f : F}
    (hf : Function.Injective f) : NeZero (n : S) :=
  ⟨fun h ↦ NeZero.natCast_ne n R <| hf <| by simpa only [map_natCast, map_zero f]⟩
#align ne_zero.nat_of_injective NeZero.nat_of_injective

end RingHomClass
