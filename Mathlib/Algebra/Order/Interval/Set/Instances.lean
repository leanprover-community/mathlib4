/-
Copyright (c) 2022 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell, Eric Wieser, Yaël Dillies, Patrick Massot, Scott Morrison
-/
import Mathlib.Algebra.GroupPower.Order
import Mathlib.Algebra.Ring.Regular
import Mathlib.Order.Interval.Set.Basic

#align_import data.set.intervals.instances from "leanprover-community/mathlib"@"d012cd09a9b256d870751284dd6a29882b0be105"

/-!
# Algebraic instances for unit intervals

For suitably structured underlying type `α`, we exhibit the structure of
the unit intervals (`Set.Icc`, `Set.Ioc`, `Set.Ioc`, and `Set.Ioo`) from `0` to `1`.
Note: Instances for the interval `Ici 0` are dealt with in `Algebra/Order/Nonneg.lean`.

## Main definitions

The strongest typeclass provided on each interval is:
* `Set.Icc.cancelCommMonoidWithZero`
* `Set.Ico.commSemigroup`
* `Set.Ioc.commMonoid`
* `Set.Ioo.commSemigroup`

## TODO

* algebraic instances for intervals -1 to 1
* algebraic instances for `Ici 1`
* algebraic instances for `(Ioo (-1) 1)ᶜ`
* provide `distribNeg` instances where applicable
* prove versions of `mul_le_{left,right}` for other intervals
* prove versions of the lemmas in `Topology/UnitInterval` with `ℝ` generalized to
  some arbitrary ordered semiring
-/


open Set

variable {α : Type*}

section OrderedSemiring

variable [OrderedSemiring α]

/-! ### Instances for `↥(Set.Icc 0 1)` -/


namespace Set.Icc

instance zero : Zero (Icc (0 : α) 1) where zero := ⟨0, left_mem_Icc.2 zero_le_one⟩
#align set.Icc.has_zero Set.Icc.zero

instance one : One (Icc (0 : α) 1) where one := ⟨1, right_mem_Icc.2 zero_le_one⟩
#align set.Icc.has_one Set.Icc.one

@[simp, norm_cast]
theorem coe_zero : ↑(0 : Icc (0 : α) 1) = (0 : α) :=
  rfl
#align set.Icc.coe_zero Set.Icc.coe_zero

@[simp, norm_cast]
theorem coe_one : ↑(1 : Icc (0 : α) 1) = (1 : α) :=
  rfl
#align set.Icc.coe_one Set.Icc.coe_one

@[simp]
theorem mk_zero (h : (0 : α) ∈ Icc (0 : α) 1) : (⟨0, h⟩ : Icc (0 : α) 1) = 0 :=
  rfl
#align set.Icc.mk_zero Set.Icc.mk_zero

@[simp]
theorem mk_one (h : (1 : α) ∈ Icc (0 : α) 1) : (⟨1, h⟩ : Icc (0 : α) 1) = 1 :=
  rfl
#align set.Icc.mk_one Set.Icc.mk_one

@[simp, norm_cast]
theorem coe_eq_zero {x : Icc (0 : α) 1} : (x : α) = 0 ↔ x = 0 := by
  symm
  exact Subtype.ext_iff
#align set.Icc.coe_eq_zero Set.Icc.coe_eq_zero

theorem coe_ne_zero {x : Icc (0 : α) 1} : (x : α) ≠ 0 ↔ x ≠ 0 :=
  not_iff_not.mpr coe_eq_zero
#align set.Icc.coe_ne_zero Set.Icc.coe_ne_zero

@[simp, norm_cast]
theorem coe_eq_one {x : Icc (0 : α) 1} : (x : α) = 1 ↔ x = 1 := by
  symm
  exact Subtype.ext_iff
#align set.Icc.coe_eq_one Set.Icc.coe_eq_one

theorem coe_ne_one {x : Icc (0 : α) 1} : (x : α) ≠ 1 ↔ x ≠ 1 :=
  not_iff_not.mpr coe_eq_one
#align set.Icc.coe_ne_one Set.Icc.coe_ne_one

theorem coe_nonneg (x : Icc (0 : α) 1) : 0 ≤ (x : α) :=
  x.2.1
#align set.Icc.coe_nonneg Set.Icc.coe_nonneg

theorem coe_le_one (x : Icc (0 : α) 1) : (x : α) ≤ 1 :=
  x.2.2
#align set.Icc.coe_le_one Set.Icc.coe_le_one

/-- like `coe_nonneg`, but with the inequality in `Icc (0:α) 1`. -/
theorem nonneg {t : Icc (0 : α) 1} : 0 ≤ t :=
  t.2.1
#align set.Icc.nonneg Set.Icc.nonneg

/-- like `coe_le_one`, but with the inequality in `Icc (0:α) 1`. -/
theorem le_one {t : Icc (0 : α) 1} : t ≤ 1 :=
  t.2.2
#align set.Icc.le_one Set.Icc.le_one

instance mul : Mul (Icc (0 : α) 1) where
  mul p q := ⟨p * q, ⟨mul_nonneg p.2.1 q.2.1, mul_le_one p.2.2 q.2.1 q.2.2⟩⟩
#align set.Icc.has_mul Set.Icc.mul

instance pow : Pow (Icc (0 : α) 1) ℕ where
  pow p n := ⟨p.1 ^ n, ⟨pow_nonneg p.2.1 n, pow_le_one n p.2.1 p.2.2⟩⟩
#align set.Icc.has_pow Set.Icc.pow

@[simp, norm_cast]
theorem coe_mul (x y : Icc (0 : α) 1) : ↑(x * y) = (x * y : α) :=
  rfl
#align set.Icc.coe_mul Set.Icc.coe_mul

@[simp, norm_cast]
theorem coe_pow (x : Icc (0 : α) 1) (n : ℕ) : ↑(x ^ n) = ((x : α) ^ n) :=
  rfl
#align set.Icc.coe_pow Set.Icc.coe_pow

theorem mul_le_left {x y : Icc (0 : α) 1} : x * y ≤ x :=
  (mul_le_mul_of_nonneg_left y.2.2 x.2.1).trans_eq (mul_one _)
#align set.Icc.mul_le_left Set.Icc.mul_le_left

theorem mul_le_right {x y : Icc (0 : α) 1} : x * y ≤ y :=
  (mul_le_mul_of_nonneg_right x.2.2 y.2.1).trans_eq (one_mul _)
#align set.Icc.mul_le_right Set.Icc.mul_le_right

instance monoidWithZero : MonoidWithZero (Icc (0 : α) 1) :=
  Subtype.coe_injective.monoidWithZero _ coe_zero coe_one coe_mul coe_pow
#align set.Icc.monoid_with_zero Set.Icc.monoidWithZero

instance commMonoidWithZero {α : Type*} [OrderedCommSemiring α] :
    CommMonoidWithZero (Icc (0 : α) 1) :=
  Subtype.coe_injective.commMonoidWithZero _ coe_zero coe_one coe_mul coe_pow
#align set.Icc.comm_monoid_with_zero Set.Icc.commMonoidWithZero

instance cancelMonoidWithZero {α : Type*} [OrderedRing α] [NoZeroDivisors α] :
    CancelMonoidWithZero (Icc (0 : α) 1) :=
  @Function.Injective.cancelMonoidWithZero α _ NoZeroDivisors.toCancelMonoidWithZero _ _ _ _
    (fun v => v.val) Subtype.coe_injective coe_zero coe_one coe_mul coe_pow
#align set.Icc.cancel_monoid_with_zero Set.Icc.cancelMonoidWithZero

instance cancelCommMonoidWithZero {α : Type*} [OrderedCommRing α] [NoZeroDivisors α] :
    CancelCommMonoidWithZero (Icc (0 : α) 1) :=
  @Function.Injective.cancelCommMonoidWithZero α _ NoZeroDivisors.toCancelCommMonoidWithZero _ _ _ _
    (fun v => v.val) Subtype.coe_injective coe_zero coe_one coe_mul coe_pow
#align set.Icc.cancel_comm_monoid_with_zero Set.Icc.cancelCommMonoidWithZero

variable {β : Type*} [OrderedRing β]

theorem one_sub_mem {t : β} (ht : t ∈ Icc (0 : β) 1) : 1 - t ∈ Icc (0 : β) 1 := by
  rw [mem_Icc] at *
  exact ⟨sub_nonneg.2 ht.2, (sub_le_self_iff _).2 ht.1⟩
#align set.Icc.one_sub_mem Set.Icc.one_sub_mem

theorem mem_iff_one_sub_mem {t : β} : t ∈ Icc (0 : β) 1 ↔ 1 - t ∈ Icc (0 : β) 1 :=
  ⟨one_sub_mem, fun h => sub_sub_cancel 1 t ▸ one_sub_mem h⟩
#align set.Icc.mem_iff_one_sub_mem Set.Icc.mem_iff_one_sub_mem

theorem one_sub_nonneg (x : Icc (0 : β) 1) : 0 ≤ 1 - (x : β) := by simpa using x.2.2
#align set.Icc.one_sub_nonneg Set.Icc.one_sub_nonneg

theorem one_sub_le_one (x : Icc (0 : β) 1) : 1 - (x : β) ≤ 1 := by simpa using x.2.1
#align set.Icc.one_sub_le_one Set.Icc.one_sub_le_one

end Set.Icc

/-! ### Instances for `↥(Set.Ico 0 1)` -/


namespace Set.Ico

instance zero [Nontrivial α] : Zero (Ico (0 : α) 1) where zero := ⟨0, left_mem_Ico.2 zero_lt_one⟩
#align set.Ico.has_zero Set.Ico.zero

@[simp, norm_cast]
theorem coe_zero [Nontrivial α] : ↑(0 : Ico (0 : α) 1) = (0 : α) :=
  rfl
#align set.Ico.coe_zero Set.Ico.coe_zero

@[simp]
theorem mk_zero [Nontrivial α] (h : (0 : α) ∈ Ico (0 : α) 1) : (⟨0, h⟩ : Ico (0 : α) 1) = 0 :=
  rfl
#align set.Ico.mk_zero Set.Ico.mk_zero

@[simp, norm_cast]
theorem coe_eq_zero [Nontrivial α] {x : Ico (0 : α) 1} : (x : α) = 0 ↔ x = 0 := by
  symm
  exact Subtype.ext_iff
#align set.Ico.coe_eq_zero Set.Ico.coe_eq_zero

theorem coe_ne_zero [Nontrivial α] {x : Ico (0 : α) 1} : (x : α) ≠ 0 ↔ x ≠ 0 :=
  not_iff_not.mpr coe_eq_zero
#align set.Ico.coe_ne_zero Set.Ico.coe_ne_zero

theorem coe_nonneg (x : Ico (0 : α) 1) : 0 ≤ (x : α) :=
  x.2.1
#align set.Ico.coe_nonneg Set.Ico.coe_nonneg

theorem coe_lt_one (x : Ico (0 : α) 1) : (x : α) < 1 :=
  x.2.2
#align set.Ico.coe_lt_one Set.Ico.coe_lt_one

/-- like `coe_nonneg`, but with the inequality in `Ico (0:α) 1`. -/
theorem nonneg [Nontrivial α] {t : Ico (0 : α) 1} : 0 ≤ t :=
  t.2.1
#align set.Ico.nonneg Set.Ico.nonneg

instance mul : Mul (Ico (0 : α) 1) where
  mul p q :=
    ⟨p * q, ⟨mul_nonneg p.2.1 q.2.1, mul_lt_one_of_nonneg_of_lt_one_right p.2.2.le q.2.1 q.2.2⟩⟩
#align set.Ico.has_mul Set.Ico.mul

@[simp, norm_cast]
theorem coe_mul (x y : Ico (0 : α) 1) : ↑(x * y) = (x * y : α) :=
  rfl
#align set.Ico.coe_mul Set.Ico.coe_mul

instance semigroup : Semigroup (Ico (0 : α) 1) :=
  Subtype.coe_injective.semigroup _ coe_mul
#align set.Ico.semigroup Set.Ico.semigroup

instance commSemigroup {α : Type*} [OrderedCommSemiring α] : CommSemigroup (Ico (0 : α) 1) :=
  Subtype.coe_injective.commSemigroup _ coe_mul
#align set.Ico.comm_semigroup Set.Ico.commSemigroup

end Set.Ico

end OrderedSemiring

variable [StrictOrderedSemiring α]

/-! ### Instances for `↥(Set.Ioc 0 1)` -/


namespace Set.Ioc

instance one [Nontrivial α] : One (Ioc (0 : α) 1) where one := ⟨1, ⟨zero_lt_one, le_refl 1⟩⟩
#align set.Ioc.has_one Set.Ioc.one

@[simp, norm_cast]
theorem coe_one [Nontrivial α] : ↑(1 : Ioc (0 : α) 1) = (1 : α) :=
  rfl
#align set.Ioc.coe_one Set.Ioc.coe_one

@[simp]
theorem mk_one [Nontrivial α] (h : (1 : α) ∈ Ioc (0 : α) 1) : (⟨1, h⟩ : Ioc (0 : α) 1) = 1 :=
  rfl
#align set.Ioc.mk_one Set.Ioc.mk_one

@[simp, norm_cast]
theorem coe_eq_one [Nontrivial α] {x : Ioc (0 : α) 1} : (x : α) = 1 ↔ x = 1 := by
  symm
  exact Subtype.ext_iff
#align set.Ioc.coe_eq_one Set.Ioc.coe_eq_one

theorem coe_ne_one [Nontrivial α] {x : Ioc (0 : α) 1} : (x : α) ≠ 1 ↔ x ≠ 1 :=
  not_iff_not.mpr coe_eq_one
#align set.Ioc.coe_ne_one Set.Ioc.coe_ne_one

theorem coe_pos (x : Ioc (0 : α) 1) : 0 < (x : α) :=
  x.2.1
#align set.Ioc.coe_pos Set.Ioc.coe_pos

theorem coe_le_one (x : Ioc (0 : α) 1) : (x : α) ≤ 1 :=
  x.2.2
#align set.Ioc.coe_le_one Set.Ioc.coe_le_one

/-- like `coe_le_one`, but with the inequality in `Ioc (0:α) 1`. -/
theorem le_one [Nontrivial α] {t : Ioc (0 : α) 1} : t ≤ 1 :=
  t.2.2
#align set.Ioc.le_one Set.Ioc.le_one

instance mul : Mul (Ioc (0 : α) 1) where
  mul p q := ⟨p.1 * q.1, ⟨mul_pos p.2.1 q.2.1, mul_le_one p.2.2 (le_of_lt q.2.1) q.2.2⟩⟩
#align set.Ioc.has_mul Set.Ioc.mul

instance pow : Pow (Ioc (0 : α) 1) ℕ where
  pow p n := ⟨p.1 ^ n, ⟨pow_pos p.2.1 n, pow_le_one n (le_of_lt p.2.1) p.2.2⟩⟩
#align set.Ioc.has_pow Set.Ioc.pow

@[simp, norm_cast]
theorem coe_mul (x y : Ioc (0 : α) 1) : ↑(x * y) = (x * y : α) :=
  rfl
#align set.Ioc.coe_mul Set.Ioc.coe_mul

@[simp, norm_cast]
theorem coe_pow (x : Ioc (0 : α) 1) (n : ℕ) : ↑(x ^ n) = ((x : α) ^ n) :=
  rfl
#align set.Ioc.coe_pow Set.Ioc.coe_pow

instance semigroup : Semigroup (Ioc (0 : α) 1) :=
  Subtype.coe_injective.semigroup _ coe_mul
#align set.Ioc.semigroup Set.Ioc.semigroup

instance monoid [Nontrivial α] : Monoid (Ioc (0 : α) 1) :=
  Subtype.coe_injective.monoid _ coe_one coe_mul coe_pow
#align set.Ioc.monoid Set.Ioc.monoid

instance commSemigroup {α : Type*} [StrictOrderedCommSemiring α] : CommSemigroup (Ioc (0 : α) 1) :=
  Subtype.coe_injective.commSemigroup _ coe_mul
#align set.Ioc.comm_semigroup Set.Ioc.commSemigroup

instance commMonoid {α : Type*} [StrictOrderedCommSemiring α] [Nontrivial α] :
    CommMonoid (Ioc (0 : α) 1) :=
  Subtype.coe_injective.commMonoid _ coe_one coe_mul coe_pow
#align set.Ioc.comm_monoid Set.Ioc.commMonoid

instance cancelMonoid {α : Type*} [StrictOrderedRing α] [IsDomain α] :
    CancelMonoid (Ioc (0 : α) 1) :=
  { Set.Ioc.monoid with
    mul_left_cancel := fun a _ _ h =>
      Subtype.ext <| mul_left_cancel₀ a.prop.1.ne' <| (congr_arg Subtype.val h : _)
    mul_right_cancel := fun _ b _ h =>
      Subtype.ext <| mul_right_cancel₀ b.prop.1.ne' <| (congr_arg Subtype.val h : _) }
#align set.Ioc.cancel_monoid Set.Ioc.cancelMonoid

instance cancelCommMonoid {α : Type*} [StrictOrderedCommRing α] [IsDomain α] :
    CancelCommMonoid (Ioc (0 : α) 1) :=
  { Set.Ioc.cancelMonoid, Set.Ioc.commMonoid with }
#align set.Ioc.cancel_comm_monoid Set.Ioc.cancelCommMonoid

end Set.Ioc

/-! ### Instances for `↥(Set.Ioo 0 1)` -/


namespace Set.Ioo

theorem pos (x : Ioo (0 : α) 1) : 0 < (x : α) :=
  x.2.1
#align set.Ioo.pos Set.Ioo.pos

theorem lt_one (x : Ioo (0 : α) 1) : (x : α) < 1 :=
  x.2.2
#align set.Ioo.lt_one Set.Ioo.lt_one

instance mul : Mul (Ioo (0 : α) 1) where
  mul p q :=
    ⟨p.1 * q.1, ⟨mul_pos p.2.1 q.2.1, mul_lt_one_of_nonneg_of_lt_one_right p.2.2.le q.2.1.le q.2.2⟩⟩
#align set.Ioo.has_mul Set.Ioo.mul

@[simp, norm_cast]
theorem coe_mul (x y : Ioo (0 : α) 1) : ↑(x * y) = (x * y : α) :=
  rfl
#align set.Ioo.coe_mul Set.Ioo.coe_mul

instance semigroup : Semigroup (Ioo (0 : α) 1) :=
  Subtype.coe_injective.semigroup _ coe_mul
#align set.Ioo.semigroup Set.Ioo.semigroup

instance commSemigroup {α : Type*} [StrictOrderedCommSemiring α] : CommSemigroup (Ioo (0 : α) 1) :=
  Subtype.coe_injective.commSemigroup _ coe_mul
#align set.Ioo.comm_semigroup Set.Ioo.commSemigroup

variable {β : Type*} [OrderedRing β]

theorem one_sub_mem {t : β} (ht : t ∈ Ioo (0 : β) 1) : 1 - t ∈ Ioo (0 : β) 1 := by
  rw [mem_Ioo] at *
  refine ⟨sub_pos.2 ht.2, ?_⟩
  exact lt_of_le_of_ne ((sub_le_self_iff 1).2 ht.1.le) (mt sub_eq_self.mp ht.1.ne')
#align set.Ioo.one_sub_mem Set.Ioo.one_sub_mem

theorem mem_iff_one_sub_mem {t : β} : t ∈ Ioo (0 : β) 1 ↔ 1 - t ∈ Ioo (0 : β) 1 :=
  ⟨one_sub_mem, fun h => sub_sub_cancel 1 t ▸ one_sub_mem h⟩
#align set.Ioo.mem_iff_one_sub_mem Set.Ioo.mem_iff_one_sub_mem

theorem one_minus_pos (x : Ioo (0 : β) 1) : 0 < 1 - (x : β) := by simpa using x.2.2
#align set.Ioo.one_minus_pos Set.Ioo.one_minus_pos

theorem one_minus_lt_one (x : Ioo (0 : β) 1) : 1 - (x : β) < 1 := by simpa using x.2.1
#align set.Ioo.one_minus_lt_one Set.Ioo.one_minus_lt_one

end Set.Ioo
