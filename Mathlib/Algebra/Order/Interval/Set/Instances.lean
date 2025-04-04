/-
Copyright (c) 2022 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell, Eric Wieser, Yaël Dillies, Patrick Massot, Kim Morrison
-/
import Mathlib.Algebra.GroupWithZero.InjSurj
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Regular
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FastInstance

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

assert_not_exists RelIso

open Set

variable {α : Type*}

section OrderedSemiring

variable [Semiring α] [PartialOrder α] [IsOrderedRing α]

/-! ### Instances for `↥(Set.Icc 0 1)` -/


namespace Set.Icc

instance zero : Zero (Icc (0 : α) 1) where zero := ⟨0, left_mem_Icc.2 zero_le_one⟩

instance one : One (Icc (0 : α) 1) where one := ⟨1, right_mem_Icc.2 zero_le_one⟩

@[simp, norm_cast]
theorem coe_zero : ↑(0 : Icc (0 : α) 1) = (0 : α) :=
  rfl

@[simp, norm_cast]
theorem coe_one : ↑(1 : Icc (0 : α) 1) = (1 : α) :=
  rfl

@[simp]
theorem mk_zero (h : (0 : α) ∈ Icc (0 : α) 1) : (⟨0, h⟩ : Icc (0 : α) 1) = 0 :=
  rfl

@[simp]
theorem mk_one (h : (1 : α) ∈ Icc (0 : α) 1) : (⟨1, h⟩ : Icc (0 : α) 1) = 1 :=
  rfl

@[simp, norm_cast]
theorem coe_eq_zero {x : Icc (0 : α) 1} : (x : α) = 0 ↔ x = 0 := by
  symm
  exact Subtype.ext_iff

theorem coe_ne_zero {x : Icc (0 : α) 1} : (x : α) ≠ 0 ↔ x ≠ 0 :=
  not_iff_not.mpr coe_eq_zero

@[simp, norm_cast]
theorem coe_eq_one {x : Icc (0 : α) 1} : (x : α) = 1 ↔ x = 1 := by
  symm
  exact Subtype.ext_iff

theorem coe_ne_one {x : Icc (0 : α) 1} : (x : α) ≠ 1 ↔ x ≠ 1 :=
  not_iff_not.mpr coe_eq_one

omit [IsOrderedRing α] in
theorem coe_nonneg (x : Icc (0 : α) 1) : 0 ≤ (x : α) :=
  x.2.1

omit [IsOrderedRing α] in
theorem coe_le_one (x : Icc (0 : α) 1) : (x : α) ≤ 1 :=
  x.2.2

/-- like `coe_nonneg`, but with the inequality in `Icc (0:α) 1`. -/
theorem nonneg {t : Icc (0 : α) 1} : 0 ≤ t :=
  t.2.1

/-- like `coe_le_one`, but with the inequality in `Icc (0:α) 1`. -/
theorem le_one {t : Icc (0 : α) 1} : t ≤ 1 :=
  t.2.2

instance mul : Mul (Icc (0 : α) 1) where
  mul p q := ⟨p * q, ⟨mul_nonneg p.2.1 q.2.1, mul_le_one₀ p.2.2 q.2.1 q.2.2⟩⟩

instance pow : Pow (Icc (0 : α) 1) ℕ where
  pow p n := ⟨p.1 ^ n, ⟨pow_nonneg p.2.1 n, pow_le_one₀ p.2.1 p.2.2⟩⟩

@[simp, norm_cast]
theorem coe_mul (x y : Icc (0 : α) 1) : ↑(x * y) = (x * y : α) :=
  rfl

@[simp, norm_cast]
theorem coe_pow (x : Icc (0 : α) 1) (n : ℕ) : ↑(x ^ n) = ((x : α) ^ n) :=
  rfl

theorem mul_le_left {x y : Icc (0 : α) 1} : x * y ≤ x :=
  (mul_le_mul_of_nonneg_left y.2.2 x.2.1).trans_eq (mul_one _)

theorem mul_le_right {x y : Icc (0 : α) 1} : x * y ≤ y :=
  (mul_le_mul_of_nonneg_right x.2.2 y.2.1).trans_eq (one_mul _)

instance monoidWithZero : MonoidWithZero (Icc (0 : α) 1) := fast_instance%
  Subtype.coe_injective.monoidWithZero _ coe_zero coe_one coe_mul coe_pow

instance commMonoidWithZero {α : Type*} [CommSemiring α] [PartialOrder α] [IsOrderedRing α] :
    CommMonoidWithZero (Icc (0 : α) 1) := fast_instance%
  Subtype.coe_injective.commMonoidWithZero _ coe_zero coe_one coe_mul coe_pow

instance cancelMonoidWithZero {α : Type*} [Ring α] [PartialOrder α] [IsOrderedRing α]
    [NoZeroDivisors α] :
    CancelMonoidWithZero (Icc (0 : α) 1) := fast_instance%
  @Function.Injective.cancelMonoidWithZero α _ NoZeroDivisors.toCancelMonoidWithZero _ _ _ _
    (fun v => v.val) Subtype.coe_injective coe_zero coe_one coe_mul coe_pow

instance cancelCommMonoidWithZero {α : Type*} [CommRing α] [PartialOrder α] [IsOrderedRing α]
    [NoZeroDivisors α] :
    CancelCommMonoidWithZero (Icc (0 : α) 1) := fast_instance%
  @Function.Injective.cancelCommMonoidWithZero α _ NoZeroDivisors.toCancelCommMonoidWithZero _ _ _ _
    (fun v => v.val) Subtype.coe_injective coe_zero coe_one coe_mul coe_pow

variable {β : Type*} [Ring β] [PartialOrder β] [IsOrderedRing β]

theorem one_sub_mem {t : β} (ht : t ∈ Icc (0 : β) 1) : 1 - t ∈ Icc (0 : β) 1 := by
  rw [mem_Icc] at *
  exact ⟨sub_nonneg.2 ht.2, (sub_le_self_iff _).2 ht.1⟩

theorem mem_iff_one_sub_mem {t : β} : t ∈ Icc (0 : β) 1 ↔ 1 - t ∈ Icc (0 : β) 1 :=
  ⟨one_sub_mem, fun h => sub_sub_cancel 1 t ▸ one_sub_mem h⟩

theorem one_sub_nonneg (x : Icc (0 : β) 1) : 0 ≤ 1 - (x : β) := by simpa using x.2.2

theorem one_sub_le_one (x : Icc (0 : β) 1) : 1 - (x : β) ≤ 1 := by simpa using x.2.1

end Set.Icc

/-! ### Instances for `↥(Set.Ico 0 1)` -/


namespace Set.Ico

instance zero [Nontrivial α] : Zero (Ico (0 : α) 1) where zero := ⟨0, left_mem_Ico.2 zero_lt_one⟩

@[simp, norm_cast]
theorem coe_zero [Nontrivial α] : ↑(0 : Ico (0 : α) 1) = (0 : α) :=
  rfl

@[simp]
theorem mk_zero [Nontrivial α] (h : (0 : α) ∈ Ico (0 : α) 1) : (⟨0, h⟩ : Ico (0 : α) 1) = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_eq_zero [Nontrivial α] {x : Ico (0 : α) 1} : (x : α) = 0 ↔ x = 0 := by
  symm
  exact Subtype.ext_iff

theorem coe_ne_zero [Nontrivial α] {x : Ico (0 : α) 1} : (x : α) ≠ 0 ↔ x ≠ 0 :=
  not_iff_not.mpr coe_eq_zero

omit [IsOrderedRing α] in
theorem coe_nonneg (x : Ico (0 : α) 1) : 0 ≤ (x : α) :=
  x.2.1

omit [IsOrderedRing α] in
theorem coe_lt_one (x : Ico (0 : α) 1) : (x : α) < 1 :=
  x.2.2

/-- like `coe_nonneg`, but with the inequality in `Ico (0:α) 1`. -/
theorem nonneg [Nontrivial α] {t : Ico (0 : α) 1} : 0 ≤ t :=
  t.2.1

instance mul : Mul (Ico (0 : α) 1) where
  mul p q :=
    ⟨p * q, ⟨mul_nonneg p.2.1 q.2.1, mul_lt_one_of_nonneg_of_lt_one_right p.2.2.le q.2.1 q.2.2⟩⟩

@[simp, norm_cast]
theorem coe_mul (x y : Ico (0 : α) 1) : ↑(x * y) = (x * y : α) :=
  rfl

instance semigroup : Semigroup (Ico (0 : α) 1) := fast_instance%
  Subtype.coe_injective.semigroup _ coe_mul

instance commSemigroup {α : Type*} [CommSemiring α] [PartialOrder α] [IsOrderedRing α] :
    CommSemigroup (Ico (0 : α) 1) :=
  Subtype.coe_injective.commSemigroup _ coe_mul

end Set.Ico

end OrderedSemiring

variable [Semiring α] [PartialOrder α] [IsStrictOrderedRing α]

/-! ### Instances for `↥(Set.Ioc 0 1)` -/


namespace Set.Ioc

instance one : One (Ioc (0 : α) 1) where one := ⟨1, ⟨zero_lt_one, le_refl 1⟩⟩

@[simp, norm_cast]
theorem coe_one : ↑(1 : Ioc (0 : α) 1) = (1 : α) :=
  rfl

@[simp]
theorem mk_one (h : (1 : α) ∈ Ioc (0 : α) 1) : (⟨1, h⟩ : Ioc (0 : α) 1) = 1 :=
  rfl

@[simp, norm_cast]
theorem coe_eq_one {x : Ioc (0 : α) 1} : (x : α) = 1 ↔ x = 1 := by
  symm
  exact Subtype.ext_iff

theorem coe_ne_one {x : Ioc (0 : α) 1} : (x : α) ≠ 1 ↔ x ≠ 1 :=
  not_iff_not.mpr coe_eq_one

omit [IsStrictOrderedRing α] in
theorem coe_pos (x : Ioc (0 : α) 1) : 0 < (x : α) :=
  x.2.1

omit [IsStrictOrderedRing α] in
theorem coe_le_one (x : Ioc (0 : α) 1) : (x : α) ≤ 1 :=
  x.2.2

/-- like `coe_le_one`, but with the inequality in `Ioc (0:α) 1`. -/
theorem le_one {t : Ioc (0 : α) 1} : t ≤ 1 :=
  t.2.2

instance mul : Mul (Ioc (0 : α) 1) where
  mul p q := ⟨p.1 * q.1, ⟨mul_pos p.2.1 q.2.1, mul_le_one₀ p.2.2 (le_of_lt q.2.1) q.2.2⟩⟩

instance pow : Pow (Ioc (0 : α) 1) ℕ where
  pow p n := ⟨p.1 ^ n, ⟨pow_pos p.2.1 n, pow_le_one₀ (le_of_lt p.2.1) p.2.2⟩⟩

@[simp, norm_cast]
theorem coe_mul (x y : Ioc (0 : α) 1) : ↑(x * y) = (x * y : α) :=
  rfl

@[simp, norm_cast]
theorem coe_pow (x : Ioc (0 : α) 1) (n : ℕ) : ↑(x ^ n) = ((x : α) ^ n) :=
  rfl

instance semigroup : Semigroup (Ioc (0 : α) 1) := fast_instance%
  Subtype.coe_injective.semigroup _ coe_mul

instance monoid : Monoid (Ioc (0 : α) 1) := fast_instance%
  Subtype.coe_injective.monoid _ coe_one coe_mul coe_pow

instance commSemigroup {α : Type*} [CommSemiring α] [PartialOrder α] [IsStrictOrderedRing α] :
    CommSemigroup (Ioc (0 : α) 1) :=
  Subtype.coe_injective.commSemigroup _ coe_mul

instance commMonoid {α : Type*} [CommSemiring α] [PartialOrder α] [IsStrictOrderedRing α] :
    CommMonoid (Ioc (0 : α) 1) :=
  Subtype.coe_injective.commMonoid _ coe_one coe_mul coe_pow

instance cancelMonoid {α : Type*} [Ring α] [PartialOrder α] [IsStrictOrderedRing α] [IsDomain α] :
    CancelMonoid (Ioc (0 : α) 1) :=
  { Set.Ioc.monoid with
    mul_left_cancel := fun a _ _ h =>
      Subtype.ext <| mul_left_cancel₀ a.prop.1.ne' <| (congr_arg Subtype.val h :)
    mul_right_cancel := fun _ b _ h =>
      Subtype.ext <| mul_right_cancel₀ b.prop.1.ne' <| (congr_arg Subtype.val h :) }

instance cancelCommMonoid {α : Type*} [CommRing α] [PartialOrder α] [IsStrictOrderedRing α]
    [IsDomain α] :
    CancelCommMonoid (Ioc (0 : α) 1) :=
  { Set.Ioc.cancelMonoid, Set.Ioc.commMonoid with }

end Set.Ioc

/-! ### Instances for `↥(Set.Ioo 0 1)` -/


namespace Set.Ioo

omit [IsStrictOrderedRing α] in
theorem pos (x : Ioo (0 : α) 1) : 0 < (x : α) :=
  x.2.1

omit [IsStrictOrderedRing α] in
theorem lt_one (x : Ioo (0 : α) 1) : (x : α) < 1 :=
  x.2.2

instance mul : Mul (Ioo (0 : α) 1) where
  mul p q :=
    ⟨p.1 * q.1, ⟨mul_pos p.2.1 q.2.1, mul_lt_one_of_nonneg_of_lt_one_right p.2.2.le q.2.1.le q.2.2⟩⟩

@[simp, norm_cast]
theorem coe_mul (x y : Ioo (0 : α) 1) : ↑(x * y) = (x * y : α) :=
  rfl

instance semigroup : Semigroup (Ioo (0 : α) 1) := fast_instance%
  Subtype.coe_injective.semigroup _ coe_mul

instance commSemigroup {α : Type*} [CommSemiring α] [PartialOrder α] [IsStrictOrderedRing α] :
    CommSemigroup (Ioo (0 : α) 1) :=
  Subtype.coe_injective.commSemigroup _ coe_mul

variable {β : Type*} [Ring β] [PartialOrder β] [IsOrderedRing β]

theorem one_sub_mem {t : β} (ht : t ∈ Ioo (0 : β) 1) : 1 - t ∈ Ioo (0 : β) 1 := by
  rw [mem_Ioo] at *
  refine ⟨sub_pos.2 ht.2, ?_⟩
  exact lt_of_le_of_ne ((sub_le_self_iff 1).2 ht.1.le) (mt sub_eq_self.mp ht.1.ne')

theorem mem_iff_one_sub_mem {t : β} : t ∈ Ioo (0 : β) 1 ↔ 1 - t ∈ Ioo (0 : β) 1 :=
  ⟨one_sub_mem, fun h => sub_sub_cancel 1 t ▸ one_sub_mem h⟩

theorem one_minus_pos (x : Ioo (0 : β) 1) : 0 < 1 - (x : β) := by simpa using x.2.2

theorem one_minus_lt_one (x : Ioo (0 : β) 1) : 1 - (x : β) < 1 := by simpa using x.2.1

end Set.Ioo
