/-
Copyright (c) 2022 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell, Eric Wieser, Yaël Dillies, Patrick Massot, Kim Morrison
-/
module

public import Mathlib.Algebra.GroupWithZero.InjSurj
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Regular
public import Mathlib.Order.Interval.Set.Basic

/-!
# Algebraic instances for unit intervals

For suitably structured underlying type `α`, we exhibit the structure of
the unit intervals (`Set.Icc`, `Set.Ioc`, `Set.Ioc`, and `Set.Ioo`) from `0` to `1`.
Note: Instances for the interval `Ici 0` are dealt with in
`Mathlib/Algebra/Order/Nonneg/Basic.lean`.

## Main definitions

The strongest typeclass provided on each interval is:
* `Set.Icc.commMonoidWithZero`
* `Set.Icc.instIsCancelMulZero`
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

@[expose] public section

assert_not_exists RelIso

open Set

variable {R : Type*}

/-! ### Instances for `↥(Set.Icc 0 1)` -/


namespace Set.Icc

section Preorder
variable [Zero R] [One R] [Preorder R]

theorem coe_nonneg (x : Icc (0 : R) 1) : 0 ≤ (x : R) :=
  x.2.1

theorem coe_le_one (x : Icc (0 : R) 1) : (x : R) ≤ 1 :=
  x.2.2

end Preorder

section ZeroLEOneClass
variable [Zero R] [One R] [Preorder R] [ZeroLEOneClass R]

instance instZero : Zero (Icc (0 : R) 1) where zero := ⟨0, left_mem_Icc.2 zero_le_one⟩

instance instOne : One (Icc (0 : R) 1) where one := ⟨1, right_mem_Icc.2 zero_le_one⟩

instance instZeroLEOneClass : ZeroLEOneClass (Icc (0 : R) 1) := ⟨Subtype.coe_le_coe.mp zero_le_one⟩

instance : IsBotZeroClass (Icc (0 : R) 1) where isBot_zero := coe_nonneg

@[simp, norm_cast]
theorem coe_zero : ↑(0 : Icc (0 : R) 1) = (0 : R) :=
  rfl

@[simp, norm_cast]
theorem coe_one : ↑(1 : Icc (0 : R) 1) = (1 : R) :=
  rfl

@[simp, grind =]
theorem mk_zero (h : (0 : R) ∈ Icc (0 : R) 1) : (⟨0, h⟩ : Icc (0 : R) 1) = 0 :=
  rfl

@[simp, grind =]
theorem mk_one (h : (1 : R) ∈ Icc (0 : R) 1) : (⟨1, h⟩ : Icc (0 : R) 1) = 1 :=
  rfl

@[simp, norm_cast]
theorem coe_eq_zero {x : Icc (0 : R) 1} : (x : R) = 0 ↔ x = 0 := by
  symm
  exact Subtype.ext_iff

theorem coe_ne_zero {x : Icc (0 : R) 1} : (x : R) ≠ 0 ↔ x ≠ 0 :=
  not_iff_not.mpr coe_eq_zero

@[simp, norm_cast]
theorem coe_eq_one {x : Icc (0 : R) 1} : (x : R) = 1 ↔ x = 1 := by
  symm
  exact Subtype.ext_iff

theorem coe_ne_one {x : Icc (0 : R) 1} : (x : R) ≠ 1 ↔ x ≠ 1 :=
  not_iff_not.mpr coe_eq_one

/-- like `coe_nonneg`, but with the inequality in `Icc (0:R) 1`. -/
theorem nonneg {t : Icc (0 : R) 1} : 0 ≤ t :=
  t.2.1

/-- like `coe_le_one`, but with the inequality in `Icc (0:R) 1`. -/
theorem le_one {t : Icc (0 : R) 1} : t ≤ 1 :=
  t.2.2

end ZeroLEOneClass

section OrderedSemiring
variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

instance instMul : Mul (Icc (0 : R) 1) where
  mul p q := ⟨p * q, ⟨mul_nonneg p.2.1 q.2.1, by grw [p.2.2, one_mul, q.2.2]; exact q.2.1⟩⟩

instance instPow : Pow (Icc (0 : R) 1) ℕ where
  pow p n := ⟨p.1 ^ n, ⟨pow_nonneg p.2.1 n, pow_le_one₀ p.2.1 p.2.2⟩⟩

@[simp, norm_cast]
theorem coe_mul (x y : Icc (0 : R) 1) : ↑(x * y) = (x * y : R) :=
  rfl

@[simp, norm_cast]
theorem coe_pow (x : Icc (0 : R) 1) (n : ℕ) : ↑(x ^ n) = ((x : R) ^ n) :=
  rfl

instance : MulLeftMono (Icc (0 : R) 1) where
  elim x y z h := (mul_le_mul_of_nonneg_left (show y.1 ≤ z.1 from h) x.2.1 :)

instance : MulRightMono (Icc (0 : R) 1) where
  elim x y z h := (mul_le_mul_of_nonneg_right (show y.1 ≤ z.1 from h) x.2.1 :)

theorem mul_le_left {x y : Icc (0 : R) 1} : x * y ≤ x :=
  (mul_le_mul_of_nonneg_left y.2.2 x.2.1).trans_eq (mul_one _)

theorem mul_le_right {x y : Icc (0 : R) 1} : x * y ≤ y :=
  (mul_le_mul_of_nonneg_right x.2.2 y.2.1).trans_eq (one_mul _)

instance instMonoidWithZero : MonoidWithZero (Icc (0 : R) 1) := fast_instance%
  Subtype.coe_injective.monoidWithZero _ coe_zero coe_one coe_mul coe_pow

/-- The coercion from `Set.Icc 0 1` as a `MonoidWithZeroHom`. -/
@[simps]
def coeMonoidWithZeroHom : (Icc (0 : R) 1) →*₀ R where
  toFun := (↑)
  map_mul' := coe_mul
  map_one' := rfl
  map_zero' := rfl

instance [IsLeftCancelMulZero R] : IsLeftCancelMulZero (Icc (0 : R) 1) where
  mul_left_cancel_of_ne_zero ha _ _ h :=
    Subtype.ext <| mul_left_cancel₀ (coe_eq_zero.not.mpr ha) (congr_arg Subtype.val h)

instance [IsRightCancelMulZero R] : IsRightCancelMulZero (Icc (0 : R) 1) where
  mul_right_cancel_of_ne_zero ha _ _ h :=
    Subtype.ext <| mul_right_cancel₀ (coe_eq_zero.not.mpr ha) (congr_arg Subtype.val h)

instance [IsCancelMulZero R] : IsCancelMulZero (Icc (0 : R) 1) where

end OrderedSemiring

instance instCommMonoidWithZero {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R] :
    CommMonoidWithZero (Icc (0 : R) 1) := fast_instance%
  Subtype.coe_injective.commMonoidWithZero _ coe_zero coe_one coe_mul coe_pow

instance {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R] :
    IsOrderedMonoid (Icc (0 : R) 1) := .of_mulLeftMono

instance instIsCancelMulZero {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
    [NoZeroDivisors R] :
    IsCancelMulZero (Icc (0 : R) 1) :=
  @Function.Injective.isCancelMulZero _ R _ _ _ _ _ Subtype.coe_injective coe_zero coe_mul
    NoZeroDivisors.toIsCancelMulZero

section OrderedAddCommGroup
variable [AddCommGroupWithOne R] [Preorder R] [IsOrderedAddMonoid R]

theorem one_sub_mem {t : R} (ht : t ∈ Icc (0 : R) 1) : 1 - t ∈ Icc (0 : R) 1 := by
  rw [mem_Icc] at *
  exact ⟨sub_nonneg.2 ht.2, (sub_le_self_iff _).2 ht.1⟩

theorem mem_iff_one_sub_mem {t : R} : t ∈ Icc (0 : R) 1 ↔ 1 - t ∈ Icc (0 : R) 1 :=
  ⟨one_sub_mem, fun h => sub_sub_cancel 1 t ▸ one_sub_mem h⟩

theorem one_sub_nonneg (x : Icc (0 : R) 1) : 0 ≤ 1 - (x : R) := by simpa using x.2.2

theorem one_sub_le_one (x : Icc (0 : R) 1) : 1 - (x : R) ≤ 1 := by simpa using x.2.1

end OrderedAddCommGroup

end Set.Icc

/-! ### Instances for `↥(Set.Ico 0 1)` -/


namespace Set.Ico

section Preorder
variable [Zero R] [One R] [Preorder R]

theorem coe_nonneg (x : Ico (0 : R) 1) : 0 ≤ (x : R) :=
  x.2.1

theorem coe_lt_one (x : Ico (0 : R) 1) : (x : R) < 1 :=
  x.2.2

end Preorder

section ZeroLEOneClass
variable [Zero R] [One R] [PartialOrder R] [ZeroLEOneClass R] [NeZero (1 : R)]

instance instZero : Zero (Ico (0 : R) 1) where zero := ⟨0, le_rfl, zero_lt_one⟩

@[simp, norm_cast]
theorem coe_zero : ↑(0 : Ico (0 : R) 1) = (0 : R) :=
  rfl

@[simp, grind =]
theorem mk_zero (h : (0 : R) ∈ Ico (0 : R) 1) : (⟨0, h⟩ : Ico (0 : R) 1) = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_eq_zero {x : Ico (0 : R) 1} : (x : R) = 0 ↔ x = 0 := by
  symm
  exact Subtype.ext_iff

theorem coe_ne_zero {x : Ico (0 : R) 1} : (x : R) ≠ 0 ↔ x ≠ 0 :=
  not_iff_not.mpr coe_eq_zero

/-- like `coe_nonneg`, but with the inequality in `Ico (0:R) 1`. -/
theorem nonneg {t : Ico (0 : R) 1} : 0 ≤ t :=
  t.2.1

instance : IsBotZeroClass (Ico (0 : R) 1) where isBot_zero := coe_nonneg

end ZeroLEOneClass

section OrderedSemiring
variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

instance instMul : Mul (Ico (0 : R) 1) where
  mul p q :=
    ⟨p * q, ⟨mul_nonneg p.2.1 q.2.1, by grw [p.2.2, one_mul, q.2.2]; exact q.2.1⟩⟩

@[simp, norm_cast]
theorem coe_mul (x y : Ico (0 : R) 1) : ↑(x * y) = (x * y : R) :=
  rfl

instance : MulLeftMono (Icc (0 : R) 1) where
  elim x y z h := (mul_le_mul_of_nonneg_left (show y.1 ≤ z.1 from h) x.2.1 :)

instance : MulRightMono (Icc (0 : R) 1) where
  elim x y z h := (mul_le_mul_of_nonneg_right (show y.1 ≤ z.1 from h) x.2.1 :)

instance instSemigroup : Semigroup (Ico (0 : R) 1) := fast_instance%
  Subtype.coe_injective.semigroup _ coe_mul

instance instCommSemigroup {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R] :
    CommSemigroup (Ico (0 : R) 1) := fast_instance%
  Subtype.coe_injective.commSemigroup _ coe_mul

/-- The coercion from `Set.Ico 0 1` as a `MulHom`. -/
@[simps]
def coeMulHom : (Ico (0 : R) 1) →ₙ* R where
  toFun := (↑)
  map_mul' := coe_mul

instance [NeZero (1 : R)] [IsLeftCancelMulZero R] : IsLeftCancelMulZero (Ico (0 : R) 1) where
  mul_left_cancel_of_ne_zero ha _ _ h :=
    Subtype.ext <| mul_left_cancel₀ (coe_eq_zero.not.mpr ha) (congr_arg Subtype.val h)

instance [NeZero (1 : R)] [IsRightCancelMulZero R] : IsRightCancelMulZero (Ico (0 : R) 1) where
  mul_right_cancel_of_ne_zero ha _ _ h :=
    Subtype.ext <| mul_right_cancel₀ (coe_eq_zero.not.mpr ha) (congr_arg Subtype.val h)

instance [NeZero (1 : R)] [IsCancelMulZero R] : IsCancelMulZero (Ico (0 : R) 1) where

end OrderedSemiring

end Set.Ico

/-! ### Instances for `↥(Set.Ioc 0 1)` -/

namespace Set.Ioc

section Preorder
variable [Zero R] [One R] [Preorder R]

theorem coe_pos (x : Ioc (0 : R) 1) : 0 < (x : R) :=
  x.2.1

theorem coe_le_one (x : Ioc (0 : R) 1) : (x : R) ≤ 1 :=
  x.2.2

end Preorder

section ZeroLEOneClass
variable [Zero R] [One R] [PartialOrder R] [ZeroLEOneClass R] [NeZero (1 : R)]

instance instOne : One (Ioc (0 : R) 1) where one := ⟨1, ⟨zero_lt_one, le_refl 1⟩⟩

@[simp, norm_cast]
theorem coe_one : ↑(1 : Ioc (0 : R) 1) = (1 : R) :=
  rfl

@[simp, grind =]
theorem mk_one (h : (1 : R) ∈ Ioc (0 : R) 1) : (⟨1, h⟩ : Ioc (0 : R) 1) = 1 :=
  rfl

@[simp, norm_cast]
theorem coe_eq_one {x : Ioc (0 : R) 1} : (x : R) = 1 ↔ x = 1 := by
  symm
  exact Subtype.ext_iff

theorem coe_ne_one {x : Ioc (0 : R) 1} : (x : R) ≠ 1 ↔ x ≠ 1 :=
  not_iff_not.mpr coe_eq_one

/-- like `coe_le_one`, but with the inequality in `Ioc (0:R) 1`. -/
theorem le_one {t : Ioc (0 : R) 1} : t ≤ 1 :=
  t.2.2

end ZeroLEOneClass

section OrderedSemiring
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

instance instMul : Mul (Ioc (0 : R) 1) where
  mul p q := ⟨p.1 * q.1, ⟨mul_pos p.2.1 q.2.1, by grw [p.2.2, one_mul, q.2.2]; exact q.2.1.le⟩⟩

instance instPow : Pow (Ioc (0 : R) 1) ℕ where
  pow p n := ⟨p.1 ^ n, ⟨pow_pos p.2.1 n, pow_le_one₀ (le_of_lt p.2.1) p.2.2⟩⟩

@[simp, norm_cast]
theorem coe_mul (x y : Ioc (0 : R) 1) : ↑(x * y) = (x * y : R) :=
  rfl

@[simp, norm_cast]
theorem coe_pow (x : Ioc (0 : R) 1) (n : ℕ) : ↑(x ^ n) = ((x : R) ^ n) :=
  rfl

instance : MulLeftStrictMono (Ioc (0 : R) 1) where
  elim x y z h := (mul_lt_mul_of_pos_left (show y.1 < z.1 from h) x.2.1 :)

instance : MulRightStrictMono (Ioc (0 : R) 1) where
  elim x y z h := (mul_lt_mul_of_pos_right (show y.1 < z.1 from h) x.2.1 :)

instance : MulLeftMono (Ioc (0 : R) 1) := mulLeftMono_of_mulLeftStrictMono _

instance : MulRightMono (Ioc (0 : R) 1) := mulRightMono_of_mulRightStrictMono _

instance instSemigroup : Semigroup (Ioc (0 : R) 1) := fast_instance%
  Subtype.coe_injective.semigroup _ coe_mul

instance instMonoid : Monoid (Ioc (0 : R) 1) := fast_instance%
  Subtype.coe_injective.monoid _ coe_one coe_mul coe_pow

/-- The coercion from `Set.Ioc 0 1` as a `MonoidHom`. -/
@[simps]
def coeMonoidHom : (Ioc (0 : R) 1) →* R where
  toFun := (↑)
  map_mul' := coe_mul
  map_one' := rfl

instance [IsLeftCancelMulZero R] : IsLeftCancelMul (Ioc (0 : R) 1) where
  mul_left_cancel a _ _ h :=
    Subtype.ext <| mul_left_cancel₀ a.prop.1.ne' (congr_arg Subtype.val h)

instance [IsRightCancelMulZero R] : IsRightCancelMul (Ioc (0 : R) 1) where
  mul_right_cancel a _ _ h :=
    Subtype.ext <| mul_right_cancel₀ a.prop.1.ne' (congr_arg Subtype.val h)

instance [IsCancelMulZero R] : IsCancelMul (Ioc (0 : R) 1) where

instance instCancelMonoid [IsCancelMulZero R] : CancelMonoid (Ioc (0 : R) 1) :=
  { Set.Ioc.instMonoid with
    mul_left_cancel _ _ _ := mul_left_cancel
    mul_right_cancel _ _ _ := mul_right_cancel }

end OrderedSemiring

instance instCommSemigroup {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] :
    CommSemigroup (Ioc (0 : R) 1) := fast_instance%
  Subtype.coe_injective.commSemigroup _ coe_mul

instance instCommMonoid {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] :
    CommMonoid (Ioc (0 : R) 1) := fast_instance%
  Subtype.coe_injective.commMonoid _ coe_one coe_mul coe_pow

instance {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] :
    IsOrderedMonoid (Ioc (0 : R) 1) := .of_mulLeftMono

instance instCancelCommMonoid {R : Type*} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]
    [IsDomain R] :
    CancelCommMonoid (Ioc (0 : R) 1) :=
  { Set.Ioc.instCommMonoid, Set.Ioc.instCancelMonoid with }

end Set.Ioc

/-! ### Instances for `↥(Set.Ioo 0 1)` -/


namespace Set.Ioo

section Preorder
variable [Zero R] [One R] [Preorder R]

theorem pos (x : Ioo (0 : R) 1) : 0 < (x : R) :=
  x.2.1

theorem lt_one (x : Ioo (0 : R) 1) : (x : R) < 1 :=
  x.2.2

end Preorder

section OrderedSemiring
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

instance instMul : Mul (Ioo (0 : R) 1) where
  mul p q :=
    ⟨p.1 * q.1, ⟨mul_pos p.2.1 q.2.1, by grw [p.2.2, one_mul, q.2.2]; exact q.2.1⟩⟩

@[simp, norm_cast]
theorem coe_mul (x y : Ioo (0 : R) 1) : ↑(x * y) = (x * y : R) :=
  rfl

instance instSemigroup : Semigroup (Ioo (0 : R) 1) := fast_instance%
  Subtype.coe_injective.semigroup _ coe_mul

instance instCommSemigroup {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] :
    CommSemigroup (Ioo (0 : R) 1) := fast_instance%
  Subtype.coe_injective.commSemigroup _ coe_mul

/-- The coercion from `Set.Ioo 0 1` as a `MulHom`. -/
@[simps]
def coeMulHom : (Ioo (0 : R) 1) →ₙ* R where
  toFun := (↑)
  map_mul' := coe_mul

end OrderedSemiring

section OrderedAddCommGroup
variable [AddCommGroupWithOne R] [PartialOrder R] [IsOrderedAddMonoid R]

theorem one_sub_mem {t : R} (ht : t ∈ Ioo (0 : R) 1) : 1 - t ∈ Ioo (0 : R) 1 := by
  simp_all only [mem_Ioo, sub_pos, sub_lt_self_iff, and_self]

theorem mem_iff_one_sub_mem {t : R} : t ∈ Ioo (0 : R) 1 ↔ 1 - t ∈ Ioo (0 : R) 1 :=
  ⟨one_sub_mem, fun h => sub_sub_cancel 1 t ▸ one_sub_mem h⟩

theorem one_sub_pos (x : Ioo (0 : R) 1) : 0 < 1 - (x : R) := by simpa using x.2.2

theorem one_sub_lt_one (x : Ioo (0 : R) 1) : 1 - (x : R) < 1 := by simpa using x.2.1

@[deprecated (since := "2026-10-06")] alias one_minus_pos := one_sub_pos
@[deprecated (since := "2026-10-06")] alias one_minus_lt_one := one_sub_lt_one

end OrderedAddCommGroup

end Set.Ioo
