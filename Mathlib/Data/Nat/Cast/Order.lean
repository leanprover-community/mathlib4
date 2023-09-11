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
variable [CharZero α] {m n : ℕ}

theorem strictMono_cast : StrictMono (Nat.cast : ℕ → α) :=
  mono_cast.strictMono_of_injective cast_injective
#align nat.strict_mono_cast Nat.strictMono_cast

/-- `Nat.cast : ℕ → α` as an `OrderEmbedding` -/
@[simps! (config := { fullyApplied := false })]
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
  rw [← cast_one, cast_lt, lt_succ_iff, ← bot_eq_zero, le_bot_iff]
#align nat.cast_lt_one Nat.cast_lt_one

@[simp, norm_cast]
theorem cast_le_one : (n : α) ≤ 1 ↔ n ≤ 1 := by rw [← cast_one, cast_le]
#align nat.cast_le_one Nat.cast_le_one

end OrderedSemiring

@[simp, norm_cast]
theorem abs_cast [LinearOrderedRing α] (a : ℕ) : |(a : α)| = a :=
  abs_of_nonneg (cast_nonneg a)
#align nat.abs_cast Nat.abs_cast

end Nat

instance [AddMonoidWithOne α] [CharZero α] : Nontrivial α where exists_pair_ne :=
  ⟨1, 0, (Nat.cast_one (R := α) ▸ Nat.cast_ne_zero.2 (by decide))⟩

section RingHomClass

variable {R S F : Type*} [NonAssocSemiring R] [NonAssocSemiring S]

theorem NeZero.nat_of_injective {n : ℕ} [h : NeZero (n : R)] [RingHomClass F R S] {f : F}
    (hf : Function.Injective f) : NeZero (n : S) :=
  ⟨fun h ↦ NeZero.natCast_ne n R <| hf <| by simpa only [map_natCast, map_zero f] ⟩
#align ne_zero.nat_of_injective NeZero.nat_of_injective

end RingHomClass
