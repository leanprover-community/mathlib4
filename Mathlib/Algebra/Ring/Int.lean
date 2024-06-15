/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Group.Int
import Mathlib.Algebra.Ring.Parity

#align_import data.int.basic from "leanprover-community/mathlib"@"00d163e35035c3577c1c79fa53b68de17781ffc1"
#align_import data.int.units from "leanprover-community/mathlib"@"641b6a82006416ec431b2987b354af9311fed4f2"

/-!
# The integers are a ring

This file contains the commutative ring instance on `ℤ`.

See note [foundational algebra order theory].

## Note

If this file needs to be split, please create an `Algebra.Ring.Int` folder and make the first file
be `Algebra.Ring.Int.Basic`.
-/

assert_not_exists DenselyOrdered
assert_not_exists Set.Subsingleton

namespace Int

instance instCommRing : CommRing ℤ where
  __ := instAddCommGroup
  __ := instCommSemigroup
  zero_mul := Int.zero_mul
  mul_zero := Int.mul_zero
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
  mul_one := Int.mul_one
  one_mul := Int.one_mul
  npow n x := x ^ n
  npow_zero _ := rfl
  npow_succ _ _ := rfl
  natCast := (·)
  natCast_zero := rfl
  natCast_succ _ := rfl
  intCast := (·)
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl

instance instCancelCommMonoidWithZero : CancelCommMonoidWithZero ℤ where
  mul_left_cancel_of_ne_zero {_a _b _c} ha := (mul_eq_mul_left_iff ha).1

instance instCharZero : CharZero ℤ where cast_injective _ _ := ofNat.inj

instance instMulDivCancelClass : MulDivCancelClass ℤ where mul_div_cancel _ _ := mul_ediv_cancel _

@[simp, norm_cast]
lemma cast_mul {α : Type*} [NonAssocRing α] : ∀ m n, ((m * n : ℤ) : α) = m * n := fun m => by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · induction m with
    | zero => simp
    | succ m ih => simp_all [add_mul]
  · induction m with
    | zero => simp
    | succ m ih => simp_all [add_mul]
#align int.cast_mul Int.cast_mulₓ -- dubious translation, type involves HasLiftT

@[simp, norm_cast] lemma cast_pow {R : Type*} [Ring R] (n : ℤ) (m : ℕ) :
    ↑(n ^ m) = (n ^ m : R) := by
  induction' m with m ih <;> simp [_root_.pow_succ, *]
#align int.cast_pow Int.cast_pow

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances like `Int.normedCommRing` being used to construct
these instances non-computably.
-/

instance instCommSemiring : CommSemiring ℤ := inferInstance
instance instSemiring     : Semiring ℤ     := inferInstance
instance instRing         : Ring ℤ         := inferInstance
instance instDistrib      : Distrib ℤ      := inferInstance

/-! ### Miscellaneous lemmas -/

/-! #### Units -/

lemma units_eq_one_or (u : ℤˣ) : u = 1 ∨ u = -1 := by
  simpa only [Units.ext_iff] using isUnit_eq_one_or u.isUnit
#align int.units_eq_one_or Int.units_eq_one_or

lemma units_ne_iff_eq_neg {u v : ℤˣ} : u ≠ v ↔ u = -v := by
  simpa only [Ne, Units.ext_iff] using isUnit_ne_iff_eq_neg u.isUnit v.isUnit

/-! #### Parity -/

variable {m n : ℤ}

lemma odd_iff : Odd n ↔ n % 2 = 1 where
  mp := fun ⟨m, hm⟩ ↦ by simp [hm, add_emod]
  mpr h := ⟨n / 2, by rw [← h, add_comm, emod_add_ediv n 2]⟩
#align int.odd_iff Int.odd_iff

lemma not_odd_iff : ¬Odd n ↔ n % 2 = 0 := by rw [odd_iff, emod_two_ne_one]
#align int.not_odd_iff Int.not_odd_iff

lemma even_iff_not_odd : Even n ↔ ¬Odd n := by rw [not_odd_iff, even_iff]
#align int.even_iff_not_odd Int.even_iff_not_odd

@[simp] lemma odd_iff_not_even : Odd n ↔ ¬Even n := by rw [not_even_iff, odd_iff]
#align int.odd_iff_not_even Int.odd_iff_not_even

lemma even_or_odd (n : ℤ) : Even n ∨ Odd n := Or.imp_right odd_iff_not_even.2 <| em <| Even n
#align int.even_or_odd Int.even_or_odd

lemma even_or_odd' (n : ℤ) : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := by
  simpa only [two_mul, exists_or, Odd, Even] using even_or_odd n
#align int.even_or_odd' Int.even_or_odd'

lemma even_xor'_odd (n : ℤ) : Xor' (Even n) (Odd n) := by
  cases even_or_odd n with
  | inl h => exact Or.inl ⟨h, even_iff_not_odd.mp h⟩
  | inr h => exact Or.inr ⟨h, odd_iff_not_even.mp h⟩
#align int.even_xor_odd Int.even_xor'_odd

lemma even_xor'_odd' (n : ℤ) : ∃ k, Xor' (n = 2 * k) (n = 2 * k + 1) := by
  rcases even_or_odd n with (⟨k, rfl⟩ | ⟨k, rfl⟩) <;> use k
  · simpa only [← two_mul, Xor', true_and_iff, eq_self_iff_true, not_true, or_false_iff,
      and_false_iff] using (succ_ne_self (2 * k)).symm
  · simp only [Xor', add_right_eq_self, false_or_iff, eq_self_iff_true, not_true, not_false_iff,
      one_ne_zero, and_self_iff]
#align int.even_xor_odd' Int.even_xor'_odd'

instance : DecidablePred (Odd : ℤ → Prop) := fun _ => decidable_of_iff _ odd_iff_not_even.symm

lemma even_add' : Even (m + n) ↔ (Odd m ↔ Odd n) := by
  rw [even_add, even_iff_not_odd, even_iff_not_odd, not_iff_not]
#align int.even_add' Int.even_add'

set_option linter.deprecated false in

@[simp, deprecated (since := "2023-01-26")]
lemma not_even_bit1 (n : ℤ) : ¬Even (bit1 n) := by simp [bit1, parity_simps]
#align int.not_even_bit1 Int.not_even_bit1

lemma even_sub' : Even (m - n) ↔ (Odd m ↔ Odd n) := by
  rw [even_sub, even_iff_not_odd, even_iff_not_odd, not_iff_not]
#align int.even_sub' Int.even_sub'

lemma odd_mul : Odd (m * n) ↔ Odd m ∧ Odd n := by simp [not_or, parity_simps]
#align int.odd_mul Int.odd_mul

lemma Odd.of_mul_left (h : Odd (m * n)) : Odd m := (odd_mul.mp h).1
#align int.odd.of_mul_left Int.Odd.of_mul_left

lemma Odd.of_mul_right (h : Odd (m * n)) : Odd n := (odd_mul.mp h).2
#align int.odd.of_mul_right Int.Odd.of_mul_right

@[parity_simps] lemma odd_pow {n : ℕ} : Odd (m ^ n) ↔ Odd m ∨ n = 0 := by
  rw [← not_iff_not, ← even_iff_not_odd, not_or, ← even_iff_not_odd, even_pow]

lemma odd_pow' {n : ℕ} (h : n ≠ 0) : Odd (m ^ n) ↔ Odd m := odd_pow.trans <| or_iff_left h

@[parity_simps] lemma odd_add : Odd (m + n) ↔ (Odd m ↔ Even n) := by
  rw [odd_iff_not_even, even_add, not_iff, odd_iff_not_even]
#align int.odd_add Int.odd_add

lemma odd_add' : Odd (m + n) ↔ (Odd n ↔ Even m) := by rw [add_comm, odd_add]
#align int.odd_add' Int.odd_add'

lemma ne_of_odd_add (h : Odd (m + n)) : m ≠ n := fun hnot ↦ by simp [hnot, parity_simps] at h
#align int.ne_of_odd_add Int.ne_of_odd_add

@[parity_simps] lemma odd_sub : Odd (m - n) ↔ (Odd m ↔ Even n) := by
  rw [odd_iff_not_even, even_sub, not_iff, odd_iff_not_even]
#align int.odd_sub Int.odd_sub

lemma odd_sub' : Odd (m - n) ↔ (Odd n ↔ Even m) := by
  rw [odd_iff_not_even, even_sub, not_iff, not_iff_comm, odd_iff_not_even]
#align int.odd_sub' Int.odd_sub'

lemma even_mul_succ_self (n : ℤ) : Even (n * (n + 1)) := by
  simpa [even_mul, parity_simps] using n.even_or_odd
#align int.even_mul_succ_self Int.even_mul_succ_self

lemma even_mul_pred_self (n : ℤ) : Even (n * (n - 1)) := by
  simpa [even_mul, parity_simps] using n.even_or_odd

-- Porting note (#10618): was simp. simp can prove this.
@[norm_cast] lemma odd_coe_nat (n : ℕ) : Odd (n : ℤ) ↔ Odd n := by
  rw [odd_iff_not_even, Nat.odd_iff_not_even, even_coe_nat]
#align int.odd_coe_nat Int.odd_coe_nat

@[simp] lemma natAbs_even : Even n.natAbs ↔ Even n := by
  simp [even_iff_two_dvd, dvd_natAbs, natCast_dvd.symm]
#align int.nat_abs_even Int.natAbs_even

-- Porting note (#10618): was simp. simp can prove this.
--@[simp]
lemma natAbs_odd : Odd n.natAbs ↔ Odd n := by
  rw [odd_iff_not_even, Nat.odd_iff_not_even, natAbs_even]
#align int.nat_abs_odd Int.natAbs_odd

alias ⟨_, _root_.Even.natAbs⟩ := natAbs_even
#align even.nat_abs Even.natAbs

alias ⟨_, _root_.Odd.natAbs⟩ := natAbs_odd
#align odd.nat_abs Odd.natAbs

-- Porting note: "protected"-attribute not implemented yet.
-- mathlib3 had:
-- `attribute [protected] Even.natAbs Odd.natAbs`

lemma four_dvd_add_or_sub_of_odd {a b : ℤ} (ha : Odd a) (hb : Odd b) :
    4 ∣ a + b ∨ 4 ∣ a - b := by
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  obtain h | h := Int.even_or_odd (m + n)
  · right
    rw [Int.even_add, ← Int.even_sub] at h
    obtain ⟨k, hk⟩ := h
    convert dvd_mul_right 4 k using 1
    rw [eq_add_of_sub_eq hk, mul_add, add_assoc, add_sub_cancel_right, ← two_mul, ← mul_assoc]
    rfl
  · left
    obtain ⟨k, hk⟩ := h
    convert dvd_mul_right 4 (k + 1) using 1
    rw [eq_sub_of_add_eq hk, add_right_comm, ← add_sub, mul_add, mul_sub, add_assoc, add_assoc,
      sub_add, add_assoc, ← sub_sub (2 * n), sub_self, zero_sub, sub_neg_eq_add, ← mul_assoc,
      mul_add]
    rfl
#align int.four_dvd_add_or_sub_of_odd Int.four_dvd_add_or_sub_of_odd

lemma two_mul_ediv_two_add_one_of_odd : Odd n → 2 * (n / 2) + 1 = n := by
  rintro ⟨c, rfl⟩
  rw [mul_comm]
  convert Int.ediv_add_emod' (2 * c + 1) 2
  simp [Int.add_emod]
#align int.two_mul_div_two_add_one_of_odd Int.two_mul_ediv_two_add_one_of_odd

lemma ediv_two_mul_two_add_one_of_odd : Odd n → n / 2 * 2 + 1 = n := by
  rintro ⟨c, rfl⟩
  convert Int.ediv_add_emod' (2 * c + 1) 2
  simp [Int.add_emod]
#align int.div_two_mul_two_add_one_of_odd Int.ediv_two_mul_two_add_one_of_odd

lemma add_one_ediv_two_mul_two_of_odd : Odd n → 1 + n / 2 * 2 = n := by
  rintro ⟨c, rfl⟩
  rw [add_comm]
  convert Int.ediv_add_emod' (2 * c + 1) 2
  simp [Int.add_emod]
#align int.add_one_div_two_mul_two_of_odd Int.add_one_ediv_two_mul_two_of_odd

lemma two_mul_ediv_two_of_odd (h : Odd n) : 2 * (n / 2) = n - 1 :=
  eq_sub_of_add_eq (two_mul_ediv_two_add_one_of_odd h)
#align int.two_mul_div_two_of_odd Int.two_mul_ediv_two_of_odd

@[norm_cast, simp]
theorem isSquare_natCast_iff {n : ℕ} : IsSquare (n : ℤ) ↔ IsSquare n := by
  constructor <;> rintro ⟨x, h⟩
  · exact ⟨x.natAbs, (natAbs_mul_natAbs_eq h.symm).symm⟩
  · exact ⟨x, mod_cast h⟩

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem isSquare_ofNat_iff {n : ℕ} :
    IsSquare (no_index (OfNat.ofNat n) : ℤ) ↔ IsSquare (OfNat.ofNat n : ℕ) :=
  isSquare_natCast_iff

end Int
