/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Yaël Dillies, Yuyang Zhao
-/
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.NatCast
import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.GrindInstances
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE

/-!
# Ordered rings and semirings

This file develops the basics of ordered (semi)rings.

Each typeclass here comprises
* an algebraic class (`Semiring`, `CommSemiring`, `Ring`, `CommRing`)
* an order class (`PartialOrder`, `LinearOrder`)
* assumptions on how both interact ((strict) monotonicity, canonicity)

For short,
* "`+` respects `≤`" means "monotonicity of addition"
* "`+` respects `<`" means "strict monotonicity of addition"
* "`*` respects `≤`" means "monotonicity of multiplication by a nonnegative number".
* "`*` respects `<`" means "strict monotonicity of multiplication by a positive number".

## Typeclasses

* `OrderedSemiring`: Semiring with a partial order such that `+` and `*` respect `≤`.
* `StrictOrderedSemiring`: Nontrivial semiring with a partial order such that `+` and `*` respects
  `<`.
* `OrderedCommSemiring`: Commutative semiring with a partial order such that `+` and `*` respect
  `≤`.
* `StrictOrderedCommSemiring`: Nontrivial commutative semiring with a partial order such that `+`
  and `*` respect `<`.
* `OrderedRing`: Ring with a partial order such that `+` respects `≤` and `*` respects `<`.
* `OrderedCommRing`: Commutative ring with a partial order such that `+` respects `≤` and
  `*` respects `<`.
* `LinearOrderedSemiring`: Nontrivial semiring with a linear order such that `+` respects `≤` and
  `*` respects `<`.
* `LinearOrderedCommSemiring`: Nontrivial commutative semiring with a linear order such that `+`
  respects `≤` and `*` respects `<`.
* `LinearOrderedRing`: Nontrivial ring with a linear order such that `+` respects `≤` and `*`
  respects `<`.
* `LinearOrderedCommRing`: Nontrivial commutative ring with a linear order such that `+` respects
  `≤` and `*` respects `<`.

## Hierarchy

The hardest part of proving order lemmas might be to figure out the correct generality and its
corresponding typeclass. Here's an attempt at demystifying it. For each typeclass, we list its
immediate predecessors and what conditions are added to each of them.

* `OrderedSemiring`
  - `OrderedAddCommMonoid` & multiplication & `*` respects `≤`
  - `Semiring` & partial order structure & `+` respects `≤` & `*` respects `≤`
* `StrictOrderedSemiring`
  - `OrderedCancelAddCommMonoid` & multiplication & `*` respects `<` & nontriviality
  - `OrderedSemiring` & `+` respects `<` & `*` respects `<` & nontriviality
* `OrderedCommSemiring`
  - `OrderedSemiring` & commutativity of multiplication
  - `CommSemiring` & partial order structure & `+` respects `≤` & `*` respects `<`
* `StrictOrderedCommSemiring`
  - `StrictOrderedSemiring` & commutativity of multiplication
  - `OrderedCommSemiring` & `+` respects `<` & `*` respects `<` & nontriviality
* `OrderedRing`
  - `OrderedSemiring` & additive inverses
  - `OrderedAddCommGroup` & multiplication & `*` respects `<`
  - `Ring` & partial order structure & `+` respects `≤` & `*` respects `<`
* `StrictOrderedRing`
  - `StrictOrderedSemiring` & additive inverses
  - `OrderedSemiring` & `+` respects `<` & `*` respects `<` & nontriviality
* `OrderedCommRing`
  - `OrderedRing` & commutativity of multiplication
  - `OrderedCommSemiring` & additive inverses
  - `CommRing` & partial order structure & `+` respects `≤` & `*` respects `<`
* `StrictOrderedCommRing`
  - `StrictOrderedCommSemiring` & additive inverses
  - `StrictOrderedRing` & commutativity of multiplication
  - `OrderedCommRing` & `+` respects `<` & `*` respects `<` & nontriviality
* `LinearOrderedSemiring`
  - `StrictOrderedSemiring` & totality of the order
  - `LinearOrderedAddCommMonoid` & multiplication & nontriviality & `*` respects `<`
* `LinearOrderedCommSemiring`
  - `StrictOrderedCommSemiring` & totality of the order
  - `LinearOrderedSemiring` & commutativity of multiplication
* `LinearOrderedRing`
  - `StrictOrderedRing` & totality of the order
  - `LinearOrderedSemiring` & additive inverses
  - `LinearOrderedAddCommGroup` & multiplication & `*` respects `<`
  - `Ring` & `IsDomain` & linear order structure
* `LinearOrderedCommRing`
  - `StrictOrderedCommRing` & totality of the order
  - `LinearOrderedRing` & commutativity of multiplication
  - `LinearOrderedCommSemiring` & additive inverses
  - `CommRing` & `IsDomain` & linear order structure
-/

assert_not_exists MonoidHom

open Function

universe u

variable {R : Type u}

-- TODO: assume weaker typeclasses

/-- An ordered semiring is a semiring with a partial order such that addition is monotone and
multiplication by a nonnegative number is monotone. -/
class IsOrderedRing (R : Type*) [Semiring R] [PartialOrder R] extends
    IsOrderedAddMonoid R, ZeroLEOneClass R, PosMulMono R, MulPosMono R where

-- See note [lower instance priority]
attribute [instance 100] IsOrderedRing.toZeroLEOneClass
attribute [instance 200] IsOrderedRing.toPosMulMono
attribute [instance 200] IsOrderedRing.toMulPosMono

/-- A strict ordered semiring is a nontrivial semiring with a partial order such that addition is
strictly monotone and multiplication by a positive number is strictly monotone. -/
class IsStrictOrderedRing (R : Type*) [Semiring R] [PartialOrder R] extends
    IsOrderedCancelAddMonoid R, ZeroLEOneClass R, Nontrivial R, PosMulStrictMono R,
    MulPosStrictMono R where

-- See note [lower instance priority]
attribute [instance 100] IsStrictOrderedRing.toZeroLEOneClass
attribute [instance 100] IsStrictOrderedRing.toNontrivial
attribute [instance 200] IsStrictOrderedRing.toPosMulStrictMono
attribute [instance 200] IsStrictOrderedRing.toMulPosStrictMono

instance [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] : Lean.Grind.OrderedRing R where
  zero_lt_one := zero_lt_one
  mul_lt_mul_of_pos_left := mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right := mul_lt_mul_of_pos_right

lemma IsOrderedRing.of_mul_nonneg [Ring R] [PartialOrder R] [IsOrderedAddMonoid R]
    [ZeroLEOneClass R] (mul_nonneg : ∀ a b : R, 0 ≤ a → 0 ≤ b → 0 ≤ a * b) :
    IsOrderedRing R where
  mul_le_mul_of_nonneg_left a ha b c hbc := by
    simpa only [mul_sub, sub_nonneg] using mul_nonneg _ _ ha (sub_nonneg.2 hbc)
  mul_le_mul_of_nonneg_right a ha b c hbc := by
    simpa only [sub_mul, sub_nonneg] using mul_nonneg _ _ (sub_nonneg.2 hbc) ha

lemma IsStrictOrderedRing.of_mul_pos [Ring R] [PartialOrder R] [IsOrderedAddMonoid R]
    [ZeroLEOneClass R] [Nontrivial R] (mul_pos : ∀ a b : R, 0 < a → 0 < b → 0 < a * b) :
    IsStrictOrderedRing R where
  mul_lt_mul_of_pos_left a ha b c hbc := by
    simpa only [mul_sub, sub_pos] using mul_pos _ _ ha (sub_pos.2 hbc)
  mul_lt_mul_of_pos_right a ha b c hbc := by
    simpa only [sub_mul, sub_pos] using mul_pos _ _ (sub_pos.2 hbc) ha

-- see Note [lower instance priority]
/-- Turn an ordered domain into a strict ordered ring. -/
instance (priority := 50) IsOrderedRing.toIsStrictOrderedRing (R : Type*)
    [Ring R] [PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R] :
    IsStrictOrderedRing R :=
  .of_mul_pos fun _ _ ap bp ↦ (mul_nonneg ap.le bp.le).lt_of_ne' (mul_ne_zero ap.ne' bp.ne')

section IsStrictOrderedRing
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

-- see Note [lower instance priority]
instance (priority := 100) IsStrictOrderedRing.toIsOrderedRing : IsOrderedRing R where
  __ := ‹IsStrictOrderedRing R›

/-- This is not an instance, as it would loop with `NeZero.charZero_one`. -/
theorem AddMonoidWithOne.toCharZero {R}
    [AddMonoidWithOne R] [PartialOrder R] [ZeroLEOneClass R]
    [NeZero (1 : R)] [AddLeftStrictMono R] : CharZero R where
  cast_injective :=
    (strictMono_nat_of_lt_succ fun n ↦ by rw [Nat.cast_succ]; apply lt_add_one).injective

-- see Note [lower instance priority]
instance (priority := 100) IsStrictOrderedRing.toCharZero :
    CharZero R := AddMonoidWithOne.toCharZero

-- see Note [lower instance priority]
instance (priority := 100) IsStrictOrderedRing.toNoMaxOrder : NoMaxOrder R :=
  ⟨fun a => ⟨a + 1, lt_add_of_pos_right _ one_pos⟩⟩

end IsStrictOrderedRing

section LinearOrder

variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R]

-- See note [lower instance priority]
instance (priority := 100) IsStrictOrderedRing.noZeroDivisors : NoZeroDivisors R where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} hab := by
    contrapose! hab
    obtain ha | ha := hab.1.lt_or_gt <;> obtain hb | hb := hab.2.lt_or_gt
    exacts [(mul_pos_of_neg_of_neg ha hb).ne', (mul_neg_of_neg_of_pos ha hb).ne,
      (mul_neg_of_pos_of_neg ha hb).ne, (mul_pos ha hb).ne']

-- Note that we can't use `NoZeroDivisors.to_isDomain` since we are merely in a semiring.
-- See note [lower instance priority]
instance (priority := 100) IsStrictOrderedRing.isDomain : IsDomain R where
  mul_left_cancel_of_ne_zero {a} ha _ _ h := by
    obtain ha | ha := ha.lt_or_gt
    exacts [(strictAnti_mul_left ha).injective h, (strictMono_mul_left_of_pos ha).injective h]
  mul_right_cancel_of_ne_zero {a} ha _ _ h := by
    obtain ha | ha := ha.lt_or_gt
    exacts [(strictAnti_mul_right ha).injective h, (strictMono_mul_right_of_pos ha).injective h]

end LinearOrder

/-! Note that `OrderDual` does not satisfy any of the ordered ring typeclasses due to the
`zero_le_one` field. -/

set_option linter.deprecated false in
/-- An `OrderedSemiring` is a semiring with a partial order such that addition is monotone and
multiplication by a nonnegative number is monotone. -/
@[deprecated "Use `[Semiring R] [PartialOrder R] [IsOrderedRing R]` instead."
  (since := "2025-04-10")]
structure OrderedSemiring (R : Type u) extends Semiring R, OrderedAddCommMonoid R where
  /-- `0 ≤ 1` in any ordered semiring. -/
  protected zero_le_one : (0 : R) ≤ 1
  /-- In an ordered semiring, we can multiply an inequality `a ≤ b` on the left
  by a non-negative element `0 ≤ c` to obtain `c * a ≤ c * b`. -/
  protected mul_le_mul_of_nonneg_left : ∀ a b c : R, a ≤ b → 0 ≤ c → c * a ≤ c * b
  /-- In an ordered semiring, we can multiply an inequality `a ≤ b` on the right
  by a non-negative element `0 ≤ c` to obtain `a * c ≤ b * c`. -/
  protected mul_le_mul_of_nonneg_right : ∀ a b c : R, a ≤ b → 0 ≤ c → a * c ≤ b * c

set_option linter.deprecated false in
/-- An `OrderedCommSemiring` is a commutative semiring with a partial order such that addition is
monotone and multiplication by a nonnegative number is monotone. -/
@[deprecated "Use `[CommSemiring R] [PartialOrder R] [IsOrderedRing R]` instead."
  (since := "2025-04-10")]
structure OrderedCommSemiring (R : Type u) extends OrderedSemiring R, CommSemiring R where
  mul_le_mul_of_nonneg_right a b c ha hc :=
    -- parentheses ensure this generates an `optParam` rather than an `autoParam`
    (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left a b c ha hc)

set_option linter.deprecated false in
/-- An `OrderedRing` is a ring with a partial order such that addition is monotone and
multiplication by a nonnegative number is monotone. -/
@[deprecated "Use `[Ring R] [PartialOrder R] [IsOrderedRing R]` instead."
  (since := "2025-04-10")]
structure OrderedRing (R : Type u) extends Ring R, OrderedAddCommGroup R where
  /-- `0 ≤ 1` in any ordered ring. -/
  protected zero_le_one : 0 ≤ (1 : R)
  /-- The product of non-negative elements is non-negative. -/
  protected mul_nonneg : ∀ a b : R, 0 ≤ a → 0 ≤ b → 0 ≤ a * b

set_option linter.deprecated false in
/-- An `OrderedCommRing` is a commutative ring with a partial order such that addition is monotone
and multiplication by a nonnegative number is monotone. -/
@[deprecated "Use `[CommRing R] [PartialOrder R] [IsOrderedRing R]` instead."
  (since := "2025-04-10")]
structure OrderedCommRing (R : Type u) extends OrderedRing R, CommRing R

set_option linter.deprecated false in
/-- A `StrictOrderedSemiring` is a nontrivial semiring with a partial order such that addition is
strictly monotone and multiplication by a positive number is strictly monotone. -/
@[deprecated "Use `[Semiring R] [PartialOrder R] [IsStrictOrderedRing R]` instead."
  (since := "2025-04-10")]
structure StrictOrderedSemiring (R : Type u) extends Semiring R, OrderedCancelAddCommMonoid R,
    Nontrivial R where
  /-- In a strict ordered semiring, `0 ≤ 1`. -/
  protected zero_le_one : (0 : R) ≤ 1
  /-- Left multiplication by a positive element is strictly monotone. -/
  protected mul_lt_mul_of_pos_left : ∀ a b c : R, a < b → 0 < c → c * a < c * b
  /-- Right multiplication by a positive element is strictly monotone. -/
  protected mul_lt_mul_of_pos_right : ∀ a b c : R, a < b → 0 < c → a * c < b * c

set_option linter.deprecated false in
/-- A `StrictOrderedCommSemiring` is a commutative semiring with a partial order such that
addition is strictly monotone and multiplication by a positive number is strictly monotone. -/
@[deprecated "Use `[CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]` instead."
  (since := "2025-04-10")]
structure StrictOrderedCommSemiring (R : Type u) extends StrictOrderedSemiring R, CommSemiring R

set_option linter.deprecated false in
/-- A `StrictOrderedRing` is a ring with a partial order such that addition is strictly monotone
and multiplication by a positive number is strictly monotone. -/
@[deprecated "Use `[Ring R] [PartialOrder R] [IsStrictOrderedRing R]` instead."
  (since := "2025-04-10")]
structure StrictOrderedRing (R : Type u) extends Ring R, OrderedAddCommGroup R, Nontrivial R where
  /-- In a strict ordered ring, `0 ≤ 1`. -/
  protected zero_le_one : 0 ≤ (1 : R)
  /-- The product of two positive elements is positive. -/
  protected mul_pos : ∀ a b : R, 0 < a → 0 < b → 0 < a * b

set_option linter.deprecated false in
/-- A `StrictOrderedCommRing` is a commutative ring with a partial order such that addition is
strictly monotone and multiplication by a positive number is strictly monotone. -/
@[deprecated "Use `[CommRing R] [PartialOrder R] [IsStrictOrderedRing R]` instead."
  (since := "2025-04-10")]
structure StrictOrderedCommRing (R : Type*) extends StrictOrderedRing R, CommRing R

/- It's not entirely clear we should assume `Nontrivial` at this point; it would be reasonable to
explore changing this, but be warned that the instances involving `Domain` may cause typeclass
search loops. -/
set_option linter.deprecated false in
/-- A `LinearOrderedSemiring` is a nontrivial semiring with a linear order such that
addition is monotone and multiplication by a positive number is strictly monotone. -/
@[deprecated "Use `[Semiring R] [LinearOrder R] [IsStrictOrderedRing R]` instead."
  (since := "2025-04-10")]
structure LinearOrderedSemiring (R : Type u) extends StrictOrderedSemiring R,
  LinearOrderedAddCommMonoid R

set_option linter.deprecated false in
/-- A `LinearOrderedCommSemiring` is a nontrivial commutative semiring with a linear order such
that addition is monotone and multiplication by a positive number is strictly monotone. -/
@[deprecated "Use `[CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]` instead."
  (since := "2025-04-10")]
structure LinearOrderedCommSemiring (R : Type*) extends StrictOrderedCommSemiring R,
  LinearOrderedSemiring R

set_option linter.deprecated false in
/-- A `LinearOrderedRing` is a ring with a linear order such that addition is monotone and
multiplication by a positive number is strictly monotone. -/
@[deprecated "Use `[Ring R] [LinearOrder R] [IsStrictOrderedRing R]` instead."
  (since := "2025-04-10")]
structure LinearOrderedRing (R : Type u) extends StrictOrderedRing R, LinearOrder R

set_option linter.deprecated false in
/-- A `LinearOrderedCommRing` is a commutative ring with a linear order such that addition is
monotone and multiplication by a positive number is strictly monotone. -/
@[deprecated "Use `[CommRing R] [LinearOrder R] [IsStrictOrderedRing R]` instead."
  (since := "2025-04-10")]
structure LinearOrderedCommRing (R : Type u) extends LinearOrderedRing R, CommMonoid R

attribute [nolint docBlame]
  StrictOrderedSemiring.toOrderedCancelAddCommMonoid
  StrictOrderedCommSemiring.toCommSemiring
  LinearOrderedSemiring.toLinearOrderedAddCommMonoid
  LinearOrderedRing.toLinearOrder
  OrderedSemiring.toOrderedAddCommMonoid
  OrderedCommSemiring.toCommSemiring
  StrictOrderedCommRing.toCommRing
  OrderedRing.toOrderedAddCommGroup
  OrderedCommRing.toCommRing
  StrictOrderedRing.toOrderedAddCommGroup
  LinearOrderedCommSemiring.toLinearOrderedSemiring
  LinearOrderedCommRing.toCommMonoid

section OrderedRing

variable [Ring R] [PartialOrder R] [IsOrderedRing R] {a b c : R}

lemma one_add_le_one_sub_mul_one_add (h : a + b + b * c ≤ c) : 1 + a ≤ (1 - b) * (1 + c) := by
  rw [one_sub_mul, mul_one_add, le_sub_iff_add_le, add_assoc, ← add_assoc a]
  gcongr

lemma one_add_le_one_add_mul_one_sub (h : a + c + b * c ≤ b) : 1 + a ≤ (1 + b) * (1 - c) := by
  rw [mul_one_sub, one_add_mul, le_sub_iff_add_le, add_assoc, ← add_assoc a]
  gcongr

lemma one_sub_le_one_sub_mul_one_add (h : b + b * c ≤ a + c) : 1 - a ≤ (1 - b) * (1 + c) := by
  rw [one_sub_mul, mul_one_add, sub_le_sub_iff, add_assoc, add_comm c]
  gcongr

lemma one_sub_le_one_add_mul_one_sub (h : c + b * c ≤ a + b) : 1 - a ≤ (1 + b) * (1 - c) := by
  rw [mul_one_sub, one_add_mul, sub_le_sub_iff, add_assoc, add_comm b]
  gcongr

end OrderedRing
