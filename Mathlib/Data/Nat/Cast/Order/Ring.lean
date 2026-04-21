/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# Cast of natural numbers: lemmas about bundled ordered semirings

-/

public section

variable {R α : Type*}

namespace Nat

section OrderedSemiring
/- Note: even though the section indicates `OrderedSemiring`, which is the common use case,
we use a generic collection of instances so that it applies in other settings (e.g., in a
`StarOrderedRing`, or the `selfAdjoint` or `StarOrderedRing.positive` parts thereof). -/

variable [AddMonoidWithOne α] [PartialOrder α]
variable [AddLeftMono α] [ZeroLEOneClass α]

/-- Specialisation of `Nat.cast_nonneg'`, which seems to be easier for Lean to use. -/
@[simp]
theorem cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrderedRing α] (n : ℕ) : 0 ≤ (n : α) :=
  cast_nonneg' n

/-- Specialisation of `Nat.ofNat_nonneg'`, which seems to be easier for Lean to use. -/
@[simp]
theorem ofNat_nonneg {α} [Semiring α] [PartialOrder α] [IsOrderedRing α] (n : ℕ) [n.AtLeastTwo] :
    0 ≤ (ofNat(n) : α) :=
  ofNat_nonneg' n

@[simp, norm_cast]
theorem cast_min {α} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] (m n : ℕ) :
    (↑(min m n : ℕ) : α) = min (m : α) n :=
  (@mono_cast α _).map_min

@[simp, norm_cast]
theorem cast_max {α} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] (m n : ℕ) :
    (↑(max m n : ℕ) : α) = max (m : α) n :=
  (@mono_cast α _).map_max

section Nontrivial

variable [NeZero (1 : α)]

/-- Specialisation of `Nat.cast_pos'`, which seems to be easier for Lean to use. -/
@[simp]
theorem cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α] {n : ℕ} :
    (0 : α) < n ↔ 0 < n := cast_pos'

/-- See also `Nat.ofNat_pos`, specialised for an `OrderedSemiring`. -/
@[simp low]
theorem ofNat_pos' {n : ℕ} [n.AtLeastTwo] : 0 < (ofNat(n) : α) :=
  cast_pos'.mpr (NeZero.pos n)

/-- Specialisation of `Nat.ofNat_pos'`, which seems to be easier for Lean to use. -/
@[simp]
theorem ofNat_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α]
    {n : ℕ} [n.AtLeastTwo] :
    0 < (ofNat(n) : α) :=
  ofNat_pos'

end Nontrivial

end OrderedSemiring

/-- A version of `Nat.cast_sub` that works for `ℝ≥0` and `ℚ≥0`. Note that this proof doesn't work
for `ℕ∞` and `ℝ≥0∞`, so we use type-specific lemmas for these types. -/
@[simp, norm_cast]
theorem cast_tsub [CommSemiring α] [PartialOrder α] [IsOrderedRing α] [CanonicallyOrderedAdd α]
    [Sub α] [OrderedSub α] [AddLeftReflectLE α] (m n : ℕ) : ↑(m - n) = (m - n : α) := by
  rcases le_total m n with h | h
  · rw [Nat.sub_eq_zero_of_le h, cast_zero, tsub_eq_zero_of_le]
    exact mono_cast h
  · rcases le_iff_exists_add'.mp h with ⟨m, rfl⟩
    rw [add_tsub_cancel_right, cast_add, add_tsub_cancel_right]

section Lattice
variable [Ring R] [Lattice R] [IsOrderedRing R]

@[simp, norm_cast]
theorem abs_cast (n : ℕ) : |(n : R)| = n := abs_of_nonneg n.cast_nonneg

@[simp]
theorem abs_ofNat (n : ℕ) [n.AtLeastTwo] : |(ofNat(n) : R)| = ofNat(n) := abs_cast n

end Lattice

section PartialOrderedRing

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R] {m n : ℕ}

@[simp, norm_cast] lemma neg_cast_eq_cast : (-m : R) = n ↔ m = 0 ∧ n = 0 := by
  simp [neg_eq_iff_add_eq_zero, ← cast_add]

@[simp, norm_cast] lemma cast_eq_neg_cast : (m : R) = -n ↔ m = 0 ∧ n = 0 := by
  simp [eq_neg_iff_add_eq_zero, ← cast_add]

end PartialOrderedRing

end Nat
