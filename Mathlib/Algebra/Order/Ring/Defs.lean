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

variable {α : Type u}

-- TODO: assume weaker typeclasses

/-- An ordered semiring is a semiring with a partial order such that addition is monotone and
multiplication by a nonnegative number is monotone. -/
class IsOrderedRing (α : Type*) [Semiring α] [PartialOrder α] extends
    IsOrderedAddMonoid α, ZeroLEOneClass α where
  /-- In an ordered semiring, we can multiply an inequality `a ≤ b` on the left
  by a non-negative element `0 ≤ c` to obtain `c * a ≤ c * b`. -/
  protected mul_le_mul_of_nonneg_left : ∀ a b c : α, a ≤ b → 0 ≤ c → c * a ≤ c * b
  /-- In an ordered semiring, we can multiply an inequality `a ≤ b` on the right
  by a non-negative element `0 ≤ c` to obtain `a * c ≤ b * c`. -/
  protected mul_le_mul_of_nonneg_right : ∀ a b c : α, a ≤ b → 0 ≤ c → a * c ≤ b * c

attribute [instance 100] IsOrderedRing.toZeroLEOneClass

/-- A strict ordered semiring is a nontrivial semiring with a partial order such that addition is
strictly monotone and multiplication by a positive number is strictly monotone. -/
class IsStrictOrderedRing (α : Type*) [Semiring α] [PartialOrder α] extends
    IsOrderedCancelAddMonoid α, ZeroLEOneClass α, Nontrivial α where
  /-- In a strict ordered semiring, we can multiply an inequality `a < b` on the left
  by a positive element `0 < c` to obtain `c * a < c * b`. -/
  protected mul_lt_mul_of_pos_left : ∀ a b c : α, a < b → 0 < c → c * a < c * b
  /-- In a strict ordered semiring, we can multiply an inequality `a < b` on the right
  by a positive element `0 < c` to obtain `a * c < b * c`. -/
  protected mul_lt_mul_of_pos_right : ∀ a b c : α, a < b → 0 < c → a * c < b * c

attribute [instance 100] IsStrictOrderedRing.toZeroLEOneClass
attribute [instance 100] IsStrictOrderedRing.toNontrivial

lemma IsOrderedRing.of_mul_nonneg [Ring α] [PartialOrder α] [IsOrderedAddMonoid α]
    [ZeroLEOneClass α] (mul_nonneg : ∀ a b : α, 0 ≤ a → 0 ≤ b → 0 ≤ a * b) :
    IsOrderedRing α where
  mul_le_mul_of_nonneg_left a b c ab hc := by
    simpa only [mul_sub, sub_nonneg] using mul_nonneg _ _ hc (sub_nonneg.2 ab)
  mul_le_mul_of_nonneg_right a b c ab hc := by
    simpa only [sub_mul, sub_nonneg] using mul_nonneg _ _ (sub_nonneg.2 ab) hc

lemma IsStrictOrderedRing.of_mul_pos [Ring α] [PartialOrder α] [IsOrderedAddMonoid α]
    [ZeroLEOneClass α] [Nontrivial α] (mul_pos : ∀ a b : α, 0 < a → 0 < b → 0 < a * b) :
    IsStrictOrderedRing α where
  mul_lt_mul_of_pos_left a b c ab hc := by
    simpa only [mul_sub, sub_pos] using mul_pos _ _ hc (sub_pos.2 ab)
  mul_lt_mul_of_pos_right a b c ab hc := by
    simpa only [sub_mul, sub_pos] using mul_pos _ _ (sub_pos.2 ab) hc

section IsOrderedRing
variable [Semiring α] [PartialOrder α] [IsOrderedRing α]

-- see Note [lower instance priority]
instance (priority := 200) IsOrderedRing.toPosMulMono : PosMulMono α where
  elim x _ _ h := IsOrderedRing.mul_le_mul_of_nonneg_left _ _ _ h x.2

-- see Note [lower instance priority]
instance (priority := 200) IsOrderedRing.toMulPosMono : MulPosMono α where
  elim x _ _ h := IsOrderedRing.mul_le_mul_of_nonneg_right _ _ _ h x.2

end IsOrderedRing

/-- Turn an ordered domain into a strict ordered ring. -/
lemma IsOrderedRing.toIsStrictOrderedRing (α : Type*)
    [Ring α] [PartialOrder α] [IsOrderedRing α] [NoZeroDivisors α] [Nontrivial α] :
    IsStrictOrderedRing α :=
  .of_mul_pos fun _ _ ap bp ↦ (mul_nonneg ap.le bp.le).lt_of_ne' (mul_ne_zero ap.ne' bp.ne')

section IsStrictOrderedRing
variable [Semiring α] [PartialOrder α] [IsStrictOrderedRing α]

-- see Note [lower instance priority]
instance (priority := 200) IsStrictOrderedRing.toPosMulStrictMono : PosMulStrictMono α where
  elim x _ _ h := IsStrictOrderedRing.mul_lt_mul_of_pos_left _ _ _ h x.prop

-- see Note [lower instance priority]
instance (priority := 200) IsStrictOrderedRing.toMulPosStrictMono : MulPosStrictMono α where
  elim x _ _ h := IsStrictOrderedRing.mul_lt_mul_of_pos_right _ _ _ h x.prop

-- see Note [lower instance priority]
instance (priority := 100) IsStrictOrderedRing.toIsOrderedRing : IsOrderedRing α where
  __ := ‹IsStrictOrderedRing α›
  mul_le_mul_of_nonneg_left _ _ _ := mul_le_mul_of_nonneg_left
  mul_le_mul_of_nonneg_right _ _ _ := mul_le_mul_of_nonneg_right

-- see Note [lower instance priority]
instance (priority := 100) IsStrictOrderedRing.toCharZero :
    CharZero α where
  cast_injective :=
    (strictMono_nat_of_lt_succ fun n ↦ by rw [Nat.cast_succ]; apply lt_add_one).injective

-- see Note [lower instance priority]
instance (priority := 100) IsStrictOrderedRing.toNoMaxOrder : NoMaxOrder α :=
  ⟨fun a => ⟨a + 1, lt_add_of_pos_right _ one_pos⟩⟩

end IsStrictOrderedRing

section LinearOrder

variable [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]

-- See note [lower instance priority]
instance (priority := 100) IsStrictOrderedRing.noZeroDivisors : NoZeroDivisors α where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} hab := by
    contrapose! hab
    obtain ha | ha := hab.1.lt_or_lt <;> obtain hb | hb := hab.2.lt_or_lt
    exacts [(mul_pos_of_neg_of_neg ha hb).ne', (mul_neg_of_neg_of_pos ha hb).ne,
      (mul_neg_of_pos_of_neg ha hb).ne, (mul_pos ha hb).ne']

-- Note that we can't use `NoZeroDivisors.to_isDomain` since we are merely in a semiring.
-- See note [lower instance priority]
instance (priority := 100) IsStrictOrderedRing.isDomain : IsDomain α where
  mul_left_cancel_of_ne_zero {a b c} ha h := by
    obtain ha | ha := ha.lt_or_lt
    exacts [(strictAnti_mul_left ha).injective h, (strictMono_mul_left_of_pos ha).injective h]
  mul_right_cancel_of_ne_zero {b a c} ha h := by
    obtain ha | ha := ha.lt_or_lt
    exacts [(strictAnti_mul_right ha).injective h, (strictMono_mul_right_of_pos ha).injective h]

end LinearOrder

/-! Note that `OrderDual` does not satisfy any of the ordered ring typeclasses due to the
`zero_le_one` field. -/

set_option linter.deprecated false in
/-- An `OrderedSemiring` is a semiring with a partial order such that addition is monotone and
multiplication by a nonnegative number is monotone. -/
@[deprecated "Use `[Semiring α] [PartialOrder α] [IsOrderedRing α]` instead."
  (since := "2025-01-05")]
structure OrderedSemiring (α : Type u) extends Semiring α, OrderedAddCommMonoid α where
  /-- `0 ≤ 1` in any ordered semiring. -/
  protected zero_le_one : (0 : α) ≤ 1
  /-- In an ordered semiring, we can multiply an inequality `a ≤ b` on the left
  by a non-negative element `0 ≤ c` to obtain `c * a ≤ c * b`. -/
  protected mul_le_mul_of_nonneg_left : ∀ a b c : α, a ≤ b → 0 ≤ c → c * a ≤ c * b
  /-- In an ordered semiring, we can multiply an inequality `a ≤ b` on the right
  by a non-negative element `0 ≤ c` to obtain `a * c ≤ b * c`. -/
  protected mul_le_mul_of_nonneg_right : ∀ a b c : α, a ≤ b → 0 ≤ c → a * c ≤ b * c

set_option linter.deprecated false in
/-- An `OrderedCommSemiring` is a commutative semiring with a partial order such that addition is
monotone and multiplication by a nonnegative number is monotone. -/
@[deprecated "Use `[CommSemiring α] [PartialOrder α] [IsOrderedRing α]` instead."
  (since := "2025-01-05")]
structure OrderedCommSemiring (α : Type u) extends OrderedSemiring α, CommSemiring α where
  mul_le_mul_of_nonneg_right a b c ha hc :=
    -- parentheses ensure this generates an `optParam` rather than an `autoParam`
    (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left a b c ha hc)

set_option linter.deprecated false in
/-- An `OrderedRing` is a ring with a partial order such that addition is monotone and
multiplication by a nonnegative number is monotone. -/
@[deprecated "Use `[Ring α] [PartialOrder α] [IsOrderedRing α]` instead."
  (since := "2025-01-05")]
structure OrderedRing (α : Type u) extends Ring α, OrderedAddCommGroup α where
  /-- `0 ≤ 1` in any ordered ring. -/
  protected zero_le_one : 0 ≤ (1 : α)
  /-- The product of non-negative elements is non-negative. -/
  protected mul_nonneg : ∀ a b : α, 0 ≤ a → 0 ≤ b → 0 ≤ a * b

set_option linter.deprecated false in
/-- An `OrderedCommRing` is a commutative ring with a partial order such that addition is monotone
and multiplication by a nonnegative number is monotone. -/
@[deprecated "Use `[CommRing α] [PartialOrder α] [IsOrderedRing α]` instead."
  (since := "2025-01-05")]
structure OrderedCommRing (α : Type u) extends OrderedRing α, CommRing α

set_option linter.deprecated false in
/-- A `StrictOrderedSemiring` is a nontrivial semiring with a partial order such that addition is
strictly monotone and multiplication by a positive number is strictly monotone. -/
@[deprecated "Use `[Semiring α] [PartialOrder α] [IsStrictOrderedRing α]` instead."
  (since := "2025-01-05")]
structure StrictOrderedSemiring (α : Type u) extends Semiring α, OrderedCancelAddCommMonoid α,
    Nontrivial α where
  /-- In a strict ordered semiring, `0 ≤ 1`. -/
  protected zero_le_one : (0 : α) ≤ 1
  /-- Left multiplication by a positive element is strictly monotone. -/
  protected mul_lt_mul_of_pos_left : ∀ a b c : α, a < b → 0 < c → c * a < c * b
  /-- Right multiplication by a positive element is strictly monotone. -/
  protected mul_lt_mul_of_pos_right : ∀ a b c : α, a < b → 0 < c → a * c < b * c

set_option linter.deprecated false in
/-- A `StrictOrderedCommSemiring` is a commutative semiring with a partial order such that
addition is strictly monotone and multiplication by a positive number is strictly monotone. -/
@[deprecated "Use `[CommSemiring α] [PartialOrder α] [IsStrictOrderedRing α]` instead."
  (since := "2025-01-05")]
structure StrictOrderedCommSemiring (α : Type u) extends StrictOrderedSemiring α, CommSemiring α

set_option linter.deprecated false in
/-- A `StrictOrderedRing` is a ring with a partial order such that addition is strictly monotone
and multiplication by a positive number is strictly monotone. -/
@[deprecated "Use `[Ring α] [PartialOrder α] [IsStrictOrderedRing α]` instead."
  (since := "2025-01-05")]
structure StrictOrderedRing (α : Type u) extends Ring α, OrderedAddCommGroup α, Nontrivial α where
  /-- In a strict ordered ring, `0 ≤ 1`. -/
  protected zero_le_one : 0 ≤ (1 : α)
  /-- The product of two positive elements is positive. -/
  protected mul_pos : ∀ a b : α, 0 < a → 0 < b → 0 < a * b

set_option linter.deprecated false in
/-- A `StrictOrderedCommRing` is a commutative ring with a partial order such that addition is
strictly monotone and multiplication by a positive number is strictly monotone. -/
@[deprecated "Use `[CommRing α] [PartialOrder α] [IsStrictOrderedRing α]` instead."
  (since := "2025-01-05")]
structure StrictOrderedCommRing (α : Type*) extends StrictOrderedRing α, CommRing α

/- It's not entirely clear we should assume `Nontrivial` at this point; it would be reasonable to
explore changing this, but be warned that the instances involving `Domain` may cause typeclass
search loops. -/
set_option linter.deprecated false in
/-- A `LinearOrderedSemiring` is a nontrivial semiring with a linear order such that
addition is monotone and multiplication by a positive number is strictly monotone. -/
@[deprecated "Use `[Semiring α] [LinearOrder α] [IsStrictOrderedRing α]` instead."
  (since := "2025-01-05")]
structure LinearOrderedSemiring (α : Type u) extends StrictOrderedSemiring α,
  LinearOrderedAddCommMonoid α

set_option linter.deprecated false in
/-- A `LinearOrderedCommSemiring` is a nontrivial commutative semiring with a linear order such
that addition is monotone and multiplication by a positive number is strictly monotone. -/
@[deprecated "Use `[CommSemiring α] [LinearOrder α] [IsStrictOrderedRing α]` instead."
  (since := "2025-01-05")]
structure LinearOrderedCommSemiring (α : Type*) extends StrictOrderedCommSemiring α,
  LinearOrderedSemiring α

set_option linter.deprecated false in
/-- A `LinearOrderedRing` is a ring with a linear order such that addition is monotone and
multiplication by a positive number is strictly monotone. -/
@[deprecated "Use `[Ring α] [LinearOrder α] [IsStrictOrderedRing α]` instead."
  (since := "2025-01-05")]
structure LinearOrderedRing (α : Type u) extends StrictOrderedRing α, LinearOrder α

set_option linter.deprecated false in
/-- A `LinearOrderedCommRing` is a commutative ring with a linear order such that addition is
monotone and multiplication by a positive number is strictly monotone. -/
@[deprecated "Use `[CommRing α] [LinearOrder α] [IsStrictOrderedRing α]` instead."
  (since := "2025-01-05")]
structure LinearOrderedCommRing (α : Type u) extends LinearOrderedRing α, CommMonoid α

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

variable [Ring α] [PartialOrder α] [IsOrderedRing α] {a b c : α}

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
