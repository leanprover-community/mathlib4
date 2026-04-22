/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.NeZero
public import Mathlib.Order.Hom.Basic

/-!
# Cast of natural numbers: lemmas about order

-/

@[expose] public section

assert_not_exists IsOrderedMonoid

variable {α : Type*}

/-- A typeclass that asserts `Nat.cast : ℕ → α` is monotone. -/
class IsMonotoneNatCast (α) [AddMonoidWithOne α] [Preorder α] where
  natCast_mono : Monotone (Nat.cast : ℕ → α)

instance [AddMonoidWithOne α] [Preorder α] [AddLeftMono α] [ZeroLEOneClass α] :
    IsMonotoneNatCast α where
  natCast_mono := monotone_nat_of_le_succ fun n ↦
    Nat.cast_succ (R := α) n ▸ le_add_of_nonneg_right zero_le_one


namespace Nat

section

variable [AddMonoidWithOne α] [Preorder α] [IsMonotoneNatCast α]

@[gcongr, mono]
theorem mono_cast : Monotone (Nat.cast : ℕ → α) :=
  IsMonotoneNatCast.natCast_mono

/-- See also `Nat.cast_nonneg`, specialised for an `OrderedSemiring`. -/
@[simp low]
theorem cast_nonneg' (n : ℕ) : 0 ≤ (n : α) :=
  @Nat.cast_zero α _ ▸ mono_cast (Nat.zero_le n)

/-- See also `Nat.ofNat_nonneg`, specialised for an `OrderedSemiring`. -/
@[simp low]
theorem ofNat_nonneg' (n : ℕ) [n.AtLeastTwo] : 0 ≤ (ofNat(n) : α) := cast_nonneg' n

instance : ZeroLEOneClass α where
  zero_le_one := by simpa only [cast_one] using cast_nonneg' 1

end


variable [AddMonoidWithOne α] [PartialOrder α] [IsMonotoneNatCast α]

section

variable [NeZero (1 : α)]

theorem cast_add_one_pos (n : ℕ) : 0 < (n : α) + 1 :=
  zero_lt_one.trans_le (by simpa using mono_cast (le_add_left 1 n : 1 ≤ n + 1))

/-- See also `Nat.cast_pos`, specialised for an `OrderedSemiring`. -/
@[simp low]
theorem cast_pos' {n : ℕ} : (0 : α) < n ↔ 0 < n := by cases n <;> simp [cast_add_one_pos]

end


variable [CharZero α] {m n : ℕ}

@[gcongr]
theorem strictMono_cast : StrictMono (Nat.cast : ℕ → α) :=
  mono_cast.strictMono_of_injective cast_injective

/-- `Nat.cast : ℕ → α` as an `OrderEmbedding` -/
@[simps! -fullyApplied]
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

theorem one_le_cast_iff_ne_zero : 1 ≤ (n : α) ↔ n ≠ 0 :=
  one_le_cast.trans one_le_iff_ne_zero

@[simp, norm_cast]
theorem cast_lt_one : (n : α) < 1 ↔ n = 0 := by
  rw [← cast_one, cast_lt, Nat.lt_succ_iff, le_zero]

@[simp, norm_cast]
theorem cast_le_one : (n : α) ≤ 1 ↔ n ≤ 1 := by rw [← cast_one, cast_le]

@[simp] lemma cast_nonpos : (n : α) ≤ 0 ↔ n = 0 := by norm_cast; lia

section
variable [m.AtLeastTwo]

@[simp]
theorem ofNat_le_cast : (ofNat(m) : α) ≤ n ↔ (OfNat.ofNat m : ℕ) ≤ n :=
  cast_le

@[simp]
theorem ofNat_lt_cast : (ofNat(m) : α) < n ↔ (OfNat.ofNat m : ℕ) < n :=
  cast_lt

end

variable [n.AtLeastTwo]

@[simp]
theorem cast_le_ofNat : (m : α) ≤ (ofNat(n) : α) ↔ m ≤ OfNat.ofNat n :=
  cast_le

@[simp]
theorem cast_lt_ofNat : (m : α) < (ofNat(n) : α) ↔ m < OfNat.ofNat n :=
  cast_lt

@[simp]
theorem one_lt_ofNat : 1 < (ofNat(n) : α) :=
  one_lt_cast.mpr AtLeastTwo.one_lt

@[simp]
theorem one_le_ofNat : 1 ≤ (ofNat(n) : α) :=
  one_le_cast.mpr NeZero.one_le

@[simp]
theorem not_ofNat_le_one : ¬(ofNat(n) : α) ≤ 1 :=
  (cast_le_one.not.trans not_le).mpr AtLeastTwo.one_lt

@[simp]
theorem not_ofNat_lt_one : ¬(ofNat(n) : α) < 1 :=
  mt le_of_lt not_ofNat_le_one

variable [m.AtLeastTwo]

-- TODO: These lemmas need to be `@[simp]` for confluence in the presence of `cast_lt`, `cast_le`,
-- and `Nat.cast_ofNat`, but their LHSs match literally every inequality, so they're too expensive.
-- If https://github.com/leanprover/lean4/issues/2867 is fixed in a performant way, these can be made `@[simp]`.

-- @[simp]
theorem ofNat_le :
    (ofNat(m) : α) ≤ (ofNat(n) : α) ↔ (OfNat.ofNat m : ℕ) ≤ OfNat.ofNat n :=
  cast_le

-- @[simp]
theorem ofNat_lt :
    (ofNat(m) : α) < (ofNat(n) : α) ↔ (OfNat.ofNat m : ℕ) < OfNat.ofNat n :=
  cast_lt

end Nat

instance [AddMonoidWithOne α] [CharZero α] : Nontrivial α :=
  NeZero.nontrivial (1 : α)

section RingHomClass

variable {R S F : Type*} [NonAssocSemiring R] [NonAssocSemiring S] [FunLike F R S]

theorem NeZero.nat_of_injective {n : ℕ} [NeZero (n : R)] [RingHomClass F R S] {f : F}
    (hf : Function.Injective f) : NeZero (n : S) :=
  ⟨fun h ↦ NeZero.natCast_ne n R <| hf <| by simpa only [map_natCast, map_zero f]⟩

end RingHomClass
