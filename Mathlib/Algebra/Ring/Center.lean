/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jireh Loreaux
-/
import Mathlib.Algebra.Group.Center
import Mathlib.Data.Int.Cast.Lemmas

#align_import group_theory.subsemigroup.center from "leanprover-community/mathlib"@"1ac8d4304efba9d03fa720d06516fac845aa5353"

/-!
# Centers of rings

-/


variable {M : Type*}

namespace Set

variable (M)

@[simp]
theorem natCast_mem_center [NonAssocSemiring M] (n : ℕ) : (n : M) ∈ Set.center M where
  comm _:= by rw [Nat.commute_cast]
  left_assoc _ _ := by
    induction n with
    | zero => rw [Nat.cast_zero, zero_mul, zero_mul, zero_mul]
    | succ n ihn => rw [Nat.cast_succ, add_mul, one_mul, ihn, add_mul, add_mul, one_mul]
  mid_assoc _ _ := by
    induction n with
    | zero => rw [Nat.cast_zero, zero_mul, mul_zero, zero_mul]
    | succ n ihn => rw [Nat.cast_succ, add_mul, mul_add, add_mul, ihn, mul_add, one_mul, mul_one]
  right_assoc _ _ := by
    induction n with
    | zero => rw [Nat.cast_zero, mul_zero, mul_zero, mul_zero]
    | succ n ihn => rw [Nat.cast_succ, mul_add, ihn, mul_add, mul_add, mul_one, mul_one]

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem ofNat_mem_center [NonAssocSemiring M] (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n)) ∈ Set.center M :=
  natCast_mem_center M n

@[simp]
theorem intCast_mem_center [NonAssocRing M] (n : ℤ) : (n : M) ∈ Set.center M where
  comm _ := by rw [Int.commute_cast]
  left_assoc _ _ := match n with
    | (n : ℕ) => by rw [Int.cast_natCast, (natCast_mem_center _ n).left_assoc _ _]
    | Int.negSucc n => by
      rw [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev, add_mul, add_mul, add_mul,
        neg_mul, one_mul, neg_mul 1, one_mul, ← neg_mul, add_right_inj, neg_mul,
        (natCast_mem_center _ n).left_assoc _ _, neg_mul, neg_mul]
  mid_assoc _ _ := match n with
    | (n : ℕ) => by rw [Int.cast_natCast, (natCast_mem_center _ n).mid_assoc _ _]
    | Int.negSucc n => by
        simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev]
        rw [add_mul, mul_add, add_mul, mul_add, neg_mul, one_mul]
        rw [neg_mul, mul_neg, mul_one, mul_neg, neg_mul, neg_mul]
        rw [(natCast_mem_center _ n).mid_assoc _ _]
        simp only [mul_neg]
  right_assoc _ _ := match n with
    | (n : ℕ) => by rw [Int.cast_natCast, (natCast_mem_center _ n).right_assoc _ _]
    | Int.negSucc n => by
        simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev]
        rw [mul_add, mul_add, mul_add, mul_neg, mul_one, mul_neg, mul_neg, mul_one, mul_neg,
          add_right_inj, (natCast_mem_center _ n).right_assoc _ _, mul_neg, mul_neg]

variable {M}

@[simp]
theorem add_mem_center [Distrib M] {a b : M} (ha : a ∈ Set.center M) (hb : b ∈ Set.center M) :
    a + b ∈ Set.center M  where
  comm _ := by rw [add_mul, mul_add, ha.comm, hb.comm]
  left_assoc _ _ := by rw [add_mul, ha.left_assoc, hb.left_assoc, ← add_mul, ← add_mul]
  mid_assoc _ _ := by rw [mul_add, add_mul, ha.mid_assoc, hb.mid_assoc, ← mul_add, ← add_mul]
  right_assoc _ _ := by rw [mul_add, ha.right_assoc, hb.right_assoc, ← mul_add, ← mul_add]
#align set.add_mem_center Set.add_mem_center

@[simp]
theorem neg_mem_center [NonUnitalNonAssocRing M] {a : M} (ha : a ∈ Set.center M) :
    -a ∈ Set.center M where
  comm _ := by rw [← neg_mul_comm, ← ha.comm, neg_mul_comm]
  left_assoc _ _ := by rw [neg_mul, ha.left_assoc, neg_mul, neg_mul]
  mid_assoc _ _ := by rw [← neg_mul_comm, ha.mid_assoc, neg_mul_comm, neg_mul]
  right_assoc _ _ := by rw [mul_neg, ha.right_assoc, mul_neg, mul_neg]
#align set.neg_mem_center Set.neg_mem_centerₓ

end Set

-- Guard against import creep
assert_not_exists Finset
assert_not_exists Subsemigroup
