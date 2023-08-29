/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Yaël Dillies
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Monoid.Cancel.Defs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Monoid.NatCast
import Mathlib.Algebra.Order.Monoid.WithZero.Defs
import Mathlib.Algebra.Order.Ring.Lemmas
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.MinMax
import Mathlib.Tactic.Nontriviality
import Mathlib.Data.Pi.Algebra
import Mathlib.Algebra.Group.Units

#align_import algebra.order.ring.defs from "leanprover-community/mathlib"@"44e29dbcff83ba7114a464d592b8c3743987c1e5"

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
* `CanonicallyOrderedCommSemiring`: Commutative semiring with a partial order such that `+`
  respects `≤`, `*` respects `<`, and `a ≤ b ↔ ∃ c, b = a + c`.

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
  - `Domain` & linear order structure
* `LinearOrderedCommRing`
  - `StrictOrderedCommRing` & totality of the order
  - `LinearOrderedRing` & commutativity of multiplication
  - `LinearOrderedCommSemiring` & additive inverses
  - `IsDomain` & linear order structure

-/

open Function

universe u

variable {α : Type u} {β : Type*}

/-! Note that `OrderDual` does not satisfy any of the ordered ring typeclasses due to the
`zero_le_one` field. -/


theorem add_one_le_two_mul [LE α] [Semiring α] [CovariantClass α α (· + ·) (· ≤ ·)] {a : α}
    (a1 : 1 ≤ a) : a + 1 ≤ 2 * a :=
  calc
    a + 1 ≤ a + a := add_le_add_left a1 a
    _ = 2 * a := (two_mul _).symm
#align add_one_le_two_mul add_one_le_two_mul

/-- An `OrderedSemiring` is a semiring with a partial order such that addition is monotone and
multiplication by a nonnegative number is monotone. -/
class OrderedSemiring (α : Type u) extends Semiring α, OrderedAddCommMonoid α where
  /-- `0 ≤ 1` in any ordered semiring. -/
  protected zero_le_one : (0 : α) ≤ 1
  /-- In an ordered semiring, we can multiply an inequality `a ≤ b` on the left
  by a non-negative element `0 ≤ c` to obtain `c * a ≤ c * b`. -/
  protected mul_le_mul_of_nonneg_left : ∀ a b c : α, a ≤ b → 0 ≤ c → c * a ≤ c * b
  /-- In an ordered semiring, we can multiply an inequality `a ≤ b` on the right
  by a non-negative element `0 ≤ c` to obtain `a * c ≤ b * c`. -/
  protected mul_le_mul_of_nonneg_right : ∀ a b c : α, a ≤ b → 0 ≤ c → a * c ≤ b * c
#align ordered_semiring OrderedSemiring

/-- An `OrderedCommSemiring` is a commutative semiring with a partial order such that addition is
monotone and multiplication by a nonnegative number is monotone. -/
class OrderedCommSemiring (α : Type u) extends OrderedSemiring α, CommSemiring α
#align ordered_comm_semiring OrderedCommSemiring

/-- An `OrderedRing` is a ring with a partial order such that addition is monotone and
multiplication by a nonnegative number is monotone. -/
class OrderedRing (α : Type u) extends Ring α, OrderedAddCommGroup α where
  /-- `0 ≤ 1` in any ordered ring. -/
  protected zero_le_one : 0 ≤ (1 : α)
  /-- The product of non-negative elements is non-negative. -/
  protected mul_nonneg : ∀ a b : α, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
#align ordered_ring OrderedRing

/-- An `OrderedCommRing` is a commutative ring with a partial order such that addition is monotone
and multiplication by a nonnegative number is monotone. -/
class OrderedCommRing (α : Type u) extends OrderedRing α, CommRing α
#align ordered_comm_ring OrderedCommRing

/-- A `StrictOrderedSemiring` is a nontrivial semiring with a partial order such that addition is
strictly monotone and multiplication by a positive number is strictly monotone. -/
class StrictOrderedSemiring (α : Type u) extends Semiring α, OrderedCancelAddCommMonoid α,
    Nontrivial α where
  /-- In a strict ordered semiring, `0 ≤ 1`. -/
  protected zero_le_one : (0 : α) ≤ 1
  /-- Left multiplication by a positive element is strictly monotone. -/
  protected mul_lt_mul_of_pos_left : ∀ a b c : α, a < b → 0 < c → c * a < c * b
  /-- Right multiplication by a positive element is strictly monotone. -/
  protected mul_lt_mul_of_pos_right : ∀ a b c : α, a < b → 0 < c → a * c < b * c
#align strict_ordered_semiring StrictOrderedSemiring

/-- A `StrictOrderedCommSemiring` is a commutative semiring with a partial order such that
addition is strictly monotone and multiplication by a positive number is strictly monotone. -/
class StrictOrderedCommSemiring (α : Type u) extends StrictOrderedSemiring α, CommSemiring α
#align strict_ordered_comm_semiring StrictOrderedCommSemiring

/-- A `StrictOrderedRing` is a ring with a partial order such that addition is strictly monotone
and multiplication by a positive number is strictly monotone. -/
class StrictOrderedRing (α : Type u) extends Ring α, OrderedAddCommGroup α, Nontrivial α where
  /-- In a strict ordered ring, `0 ≤ 1`. -/
  protected zero_le_one : 0 ≤ (1 : α)
  /-- The product of two positive elements is positive. -/
  protected mul_pos : ∀ a b : α, 0 < a → 0 < b → 0 < a * b
#align strict_ordered_ring StrictOrderedRing

/-- A `StrictOrderedCommRing` is a commutative ring with a partial order such that addition is
strictly monotone and multiplication by a positive number is strictly monotone. -/
class StrictOrderedCommRing (α : Type*) extends StrictOrderedRing α, CommRing α
#align strict_ordered_comm_ring StrictOrderedCommRing

/- It's not entirely clear we should assume `Nontrivial` at this point; it would be reasonable to
explore changing this, but be warned that the instances involving `Domain` may cause typeclass
search loops. -/
/-- A `LinearOrderedSemiring` is a nontrivial semiring with a linear order such that
addition is monotone and multiplication by a positive number is strictly monotone. -/
class LinearOrderedSemiring (α : Type u) extends StrictOrderedSemiring α,
  LinearOrderedAddCommMonoid α
#align linear_ordered_semiring LinearOrderedSemiring

/-- A `LinearOrderedCommSemiring` is a nontrivial commutative semiring with a linear order such
that addition is monotone and multiplication by a positive number is strictly monotone. -/
class LinearOrderedCommSemiring (α : Type*) extends StrictOrderedCommSemiring α,
  LinearOrderedSemiring α
#align linear_ordered_comm_semiring LinearOrderedCommSemiring

/-- A `LinearOrderedRing` is a ring with a linear order such that addition is monotone and
multiplication by a positive number is strictly monotone. -/
class LinearOrderedRing (α : Type u) extends StrictOrderedRing α, LinearOrder α
#align linear_ordered_ring LinearOrderedRing

/-- A `LinearOrderedCommRing` is a commutative ring with a linear order such that addition is
monotone and multiplication by a positive number is strictly monotone. -/
class LinearOrderedCommRing (α : Type u) extends LinearOrderedRing α, CommMonoid α
#align linear_ordered_comm_ring LinearOrderedCommRing

section OrderedSemiring

variable [OrderedSemiring α] {a b c d : α}

-- see Note [lower instance priority]
instance (priority := 100) OrderedSemiring.zeroLEOneClass : ZeroLEOneClass α :=
  { ‹OrderedSemiring α› with }
#align ordered_semiring.zero_le_one_class OrderedSemiring.zeroLEOneClass

-- see Note [lower instance priority]
instance (priority := 200) OrderedSemiring.toPosMulMono : PosMulMono α :=
  ⟨fun x _ _ h => OrderedSemiring.mul_le_mul_of_nonneg_left _ _ _ h x.2⟩
#align ordered_semiring.to_pos_mul_mono OrderedSemiring.toPosMulMono

-- see Note [lower instance priority]
instance (priority := 200) OrderedSemiring.toMulPosMono : MulPosMono α :=
  ⟨fun x _ _ h => OrderedSemiring.mul_le_mul_of_nonneg_right _ _ _ h x.2⟩
#align ordered_semiring.to_mul_pos_mono OrderedSemiring.toMulPosMono

set_option linter.deprecated false in
theorem bit1_mono : Monotone (bit1 : α → α) := fun _ _ h => add_le_add_right (bit0_mono h) _
#align bit1_mono bit1_mono

@[simp]
theorem pow_nonneg (H : 0 ≤ a) : ∀ n : ℕ, 0 ≤ a ^ n
  | 0 => by
    rw [pow_zero]
    -- ⊢ 0 ≤ 1
    exact zero_le_one
    -- 🎉 no goals
  | n + 1 => by
    rw [pow_succ]
    -- ⊢ 0 ≤ a * a ^ n
    exact mul_nonneg H (pow_nonneg H _)
    -- 🎉 no goals
#align pow_nonneg pow_nonneg

-- Porting note: it's unfortunate we need to write `(@one_le_two α)` here.
theorem add_le_mul_two_add (a2 : 2 ≤ a) (b0 : 0 ≤ b) : a + (2 + b) ≤ a * (2 + b) :=
  calc
    a + (2 + b) ≤ a + (a + a * b) :=
      add_le_add_left (add_le_add a2 <| le_mul_of_one_le_left b0 <| (@one_le_two α).trans a2) a
    _ ≤ a * (2 + b) := by rw [mul_add, mul_two, add_assoc]
                          -- 🎉 no goals
#align add_le_mul_two_add add_le_mul_two_add

theorem one_le_mul_of_one_le_of_one_le (ha : 1 ≤ a) (hb : 1 ≤ b) : (1 : α) ≤ a * b :=
  Left.one_le_mul_of_le_of_le ha hb <| zero_le_one.trans ha
#align one_le_mul_of_one_le_of_one_le one_le_mul_of_one_le_of_one_le

section Monotone

variable [Preorder β] {f g : β → α}

theorem monotone_mul_left_of_nonneg (ha : 0 ≤ a) : Monotone fun x => a * x := fun _ _ h =>
  mul_le_mul_of_nonneg_left h ha
#align monotone_mul_left_of_nonneg monotone_mul_left_of_nonneg

theorem monotone_mul_right_of_nonneg (ha : 0 ≤ a) : Monotone fun x => x * a := fun _ _ h =>
  mul_le_mul_of_nonneg_right h ha
#align monotone_mul_right_of_nonneg monotone_mul_right_of_nonneg

theorem Monotone.mul_const (hf : Monotone f) (ha : 0 ≤ a) : Monotone fun x => f x * a :=
  (monotone_mul_right_of_nonneg ha).comp hf
#align monotone.mul_const Monotone.mul_const

theorem Monotone.const_mul (hf : Monotone f) (ha : 0 ≤ a) : Monotone fun x => a * f x :=
  (monotone_mul_left_of_nonneg ha).comp hf
#align monotone.const_mul Monotone.const_mul

theorem Antitone.mul_const (hf : Antitone f) (ha : 0 ≤ a) : Antitone fun x => f x * a :=
  (monotone_mul_right_of_nonneg ha).comp_antitone hf
#align antitone.mul_const Antitone.mul_const

theorem Antitone.const_mul (hf : Antitone f) (ha : 0 ≤ a) : Antitone fun x => a * f x :=
  (monotone_mul_left_of_nonneg ha).comp_antitone hf
#align antitone.const_mul Antitone.const_mul

theorem Monotone.mul (hf : Monotone f) (hg : Monotone g) (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 ≤ g x) :
    Monotone (f * g) := fun _ _ h => mul_le_mul (hf h) (hg h) (hg₀ _) (hf₀ _)
#align monotone.mul Monotone.mul

end Monotone

section
set_option linter.deprecated false

theorem bit1_pos [Nontrivial α] (h : 0 ≤ a) : 0 < bit1 a :=
  zero_lt_one.trans_le <| bit1_zero.symm.trans_le <| bit1_mono h
#align bit1_pos bit1_pos

theorem bit1_pos' (h : 0 < a) : 0 < bit1 a := by
  nontriviality
  -- ⊢ 0 < bit1 a
  exact bit1_pos h.le
  -- 🎉 no goals
#align bit1_pos' bit1_pos'

end

theorem mul_le_one (ha : a ≤ 1) (hb' : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
  one_mul (1 : α) ▸ mul_le_mul ha hb hb' zero_le_one
#align mul_le_one mul_le_one

theorem one_lt_mul_of_le_of_lt (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b :=
  hb.trans_le <| le_mul_of_one_le_left (zero_le_one.trans hb.le) ha
#align one_lt_mul_of_le_of_lt one_lt_mul_of_le_of_lt

theorem one_lt_mul_of_lt_of_le (ha : 1 < a) (hb : 1 ≤ b) : 1 < a * b :=
  ha.trans_le <| le_mul_of_one_le_right (zero_le_one.trans ha.le) hb
#align one_lt_mul_of_lt_of_le one_lt_mul_of_lt_of_le

alias one_lt_mul := one_lt_mul_of_le_of_lt
#align one_lt_mul one_lt_mul

theorem mul_lt_one_of_nonneg_of_lt_one_left (ha₀ : 0 ≤ a) (ha : a < 1) (hb : b ≤ 1) : a * b < 1 :=
  (mul_le_of_le_one_right ha₀ hb).trans_lt ha
#align mul_lt_one_of_nonneg_of_lt_one_left mul_lt_one_of_nonneg_of_lt_one_left

theorem mul_lt_one_of_nonneg_of_lt_one_right (ha : a ≤ 1) (hb₀ : 0 ≤ b) (hb : b < 1) : a * b < 1 :=
  (mul_le_of_le_one_left hb₀ ha).trans_lt hb
#align mul_lt_one_of_nonneg_of_lt_one_right mul_lt_one_of_nonneg_of_lt_one_right

end OrderedSemiring

section OrderedRing

variable [OrderedRing α] {a b c d : α}

-- see Note [lower instance priority]
instance (priority := 100) OrderedRing.toOrderedSemiring : OrderedSemiring α :=
  { ‹OrderedRing α›, (Ring.toSemiring : Semiring α) with
    mul_le_mul_of_nonneg_left := fun a b c h hc => by
      simpa only [mul_sub, sub_nonneg] using OrderedRing.mul_nonneg _ _ hc (sub_nonneg.2 h),
      -- 🎉 no goals
    mul_le_mul_of_nonneg_right := fun a b c h hc => by
      simpa only [sub_mul, sub_nonneg] using OrderedRing.mul_nonneg _ _ (sub_nonneg.2 h) hc }
      -- 🎉 no goals
#align ordered_ring.to_ordered_semiring OrderedRing.toOrderedSemiring

theorem mul_le_mul_of_nonpos_left (h : b ≤ a) (hc : c ≤ 0) : c * a ≤ c * b := by
  simpa only [neg_mul, neg_le_neg_iff] using mul_le_mul_of_nonneg_left h (neg_nonneg.2 hc)
  -- 🎉 no goals
#align mul_le_mul_of_nonpos_left mul_le_mul_of_nonpos_left

theorem mul_le_mul_of_nonpos_right (h : b ≤ a) (hc : c ≤ 0) : a * c ≤ b * c := by
  simpa only [mul_neg, neg_le_neg_iff] using mul_le_mul_of_nonneg_right h (neg_nonneg.2 hc)
  -- 🎉 no goals
#align mul_le_mul_of_nonpos_right mul_le_mul_of_nonpos_right

theorem mul_nonneg_of_nonpos_of_nonpos (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b := by
  simpa only [zero_mul] using mul_le_mul_of_nonpos_right ha hb
  -- 🎉 no goals
#align mul_nonneg_of_nonpos_of_nonpos mul_nonneg_of_nonpos_of_nonpos

theorem mul_le_mul_of_nonneg_of_nonpos (hca : c ≤ a) (hbd : b ≤ d) (hc : 0 ≤ c) (hb : b ≤ 0) :
    a * b ≤ c * d :=
  (mul_le_mul_of_nonpos_right hca hb).trans <| mul_le_mul_of_nonneg_left hbd hc
#align mul_le_mul_of_nonneg_of_nonpos mul_le_mul_of_nonneg_of_nonpos

theorem mul_le_mul_of_nonneg_of_nonpos' (hca : c ≤ a) (hbd : b ≤ d) (ha : 0 ≤ a) (hd : d ≤ 0) :
    a * b ≤ c * d :=
  (mul_le_mul_of_nonneg_left hbd ha).trans <| mul_le_mul_of_nonpos_right hca hd
#align mul_le_mul_of_nonneg_of_nonpos' mul_le_mul_of_nonneg_of_nonpos'

theorem mul_le_mul_of_nonpos_of_nonneg (hac : a ≤ c) (hdb : d ≤ b) (hc : c ≤ 0) (hb : 0 ≤ b) :
    a * b ≤ c * d :=
  (mul_le_mul_of_nonneg_right hac hb).trans <| mul_le_mul_of_nonpos_left hdb hc
#align mul_le_mul_of_nonpos_of_nonneg mul_le_mul_of_nonpos_of_nonneg

theorem mul_le_mul_of_nonpos_of_nonneg' (hca : c ≤ a) (hbd : b ≤ d) (ha : 0 ≤ a) (hd : d ≤ 0) :
    a * b ≤ c * d :=
  (mul_le_mul_of_nonneg_left hbd ha).trans <| mul_le_mul_of_nonpos_right hca hd
#align mul_le_mul_of_nonpos_of_nonneg' mul_le_mul_of_nonpos_of_nonneg'

theorem mul_le_mul_of_nonpos_of_nonpos (hca : c ≤ a) (hdb : d ≤ b) (hc : c ≤ 0) (hb : b ≤ 0) :
    a * b ≤ c * d :=
  (mul_le_mul_of_nonpos_right hca hb).trans <| mul_le_mul_of_nonpos_left hdb hc
#align mul_le_mul_of_nonpos_of_nonpos mul_le_mul_of_nonpos_of_nonpos

theorem mul_le_mul_of_nonpos_of_nonpos' (hca : c ≤ a) (hdb : d ≤ b) (ha : a ≤ 0) (hd : d ≤ 0) :
    a * b ≤ c * d :=
  (mul_le_mul_of_nonpos_left hdb ha).trans <| mul_le_mul_of_nonpos_right hca hd
#align mul_le_mul_of_nonpos_of_nonpos' mul_le_mul_of_nonpos_of_nonpos'

/-- Variant of `mul_le_of_le_one_left` for `b` non-positive instead of non-negative.  -/
theorem le_mul_of_le_one_left (hb : b ≤ 0) (h : a ≤ 1) : b ≤ a * b := by
  simpa only [one_mul] using mul_le_mul_of_nonpos_right h hb
  -- 🎉 no goals
#align le_mul_of_le_one_left le_mul_of_le_one_left

/-- Variant of `le_mul_of_one_le_left` for `b` non-positive instead of non-negative. -/
theorem mul_le_of_one_le_left (hb : b ≤ 0) (h : 1 ≤ a) : a * b ≤ b := by
  simpa only [one_mul] using mul_le_mul_of_nonpos_right h hb
  -- 🎉 no goals
#align mul_le_of_one_le_left mul_le_of_one_le_left

/-- Variant of `mul_le_of_le_one_right` for `a` non-positive instead of non-negative. -/
theorem le_mul_of_le_one_right (ha : a ≤ 0) (h : b ≤ 1) : a ≤ a * b := by
  simpa only [mul_one] using mul_le_mul_of_nonpos_left h ha
  -- 🎉 no goals
#align le_mul_of_le_one_right le_mul_of_le_one_right

/-- Variant of `le_mul_of_one_le_right` for `a` non-positive instead of non-negative. -/
theorem mul_le_of_one_le_right (ha : a ≤ 0) (h : 1 ≤ b) : a * b ≤ a := by
  simpa only [mul_one] using mul_le_mul_of_nonpos_left h ha
  -- 🎉 no goals
#align mul_le_of_one_le_right mul_le_of_one_le_right

section Monotone

variable [Preorder β] {f g : β → α}

theorem antitone_mul_left {a : α} (ha : a ≤ 0) : Antitone ((· * ·) a) := fun _ _ b_le_c =>
  mul_le_mul_of_nonpos_left b_le_c ha
#align antitone_mul_left antitone_mul_left

theorem antitone_mul_right {a : α} (ha : a ≤ 0) : Antitone fun x => x * a := fun _ _ b_le_c =>
  mul_le_mul_of_nonpos_right b_le_c ha
#align antitone_mul_right antitone_mul_right

theorem Monotone.const_mul_of_nonpos (hf : Monotone f) (ha : a ≤ 0) : Antitone fun x => a * f x :=
  (antitone_mul_left ha).comp_monotone hf
#align monotone.const_mul_of_nonpos Monotone.const_mul_of_nonpos

theorem Monotone.mul_const_of_nonpos (hf : Monotone f) (ha : a ≤ 0) : Antitone fun x => f x * a :=
  (antitone_mul_right ha).comp_monotone hf
#align monotone.mul_const_of_nonpos Monotone.mul_const_of_nonpos

theorem Antitone.const_mul_of_nonpos (hf : Antitone f) (ha : a ≤ 0) : Monotone fun x => a * f x :=
  (antitone_mul_left ha).comp hf
#align antitone.const_mul_of_nonpos Antitone.const_mul_of_nonpos

theorem Antitone.mul_const_of_nonpos (hf : Antitone f) (ha : a ≤ 0) : Monotone fun x => f x * a :=
  (antitone_mul_right ha).comp hf
#align antitone.mul_const_of_nonpos Antitone.mul_const_of_nonpos

theorem Antitone.mul_monotone (hf : Antitone f) (hg : Monotone g) (hf₀ : ∀ x, f x ≤ 0)
    (hg₀ : ∀ x, 0 ≤ g x) : Antitone (f * g) := fun _ _ h =>
  mul_le_mul_of_nonpos_of_nonneg (hf h) (hg h) (hf₀ _) (hg₀ _)
#align antitone.mul_monotone Antitone.mul_monotone

theorem Monotone.mul_antitone (hf : Monotone f) (hg : Antitone g) (hf₀ : ∀ x, 0 ≤ f x)
    (hg₀ : ∀ x, g x ≤ 0) : Antitone (f * g) := fun _ _ h =>
  mul_le_mul_of_nonneg_of_nonpos (hf h) (hg h) (hf₀ _) (hg₀ _)
#align monotone.mul_antitone Monotone.mul_antitone

theorem Antitone.mul (hf : Antitone f) (hg : Antitone g) (hf₀ : ∀ x, f x ≤ 0) (hg₀ : ∀ x, g x ≤ 0) :
    Monotone (f * g) := fun _ _ h => mul_le_mul_of_nonpos_of_nonpos (hf h) (hg h) (hf₀ _) (hg₀ _)
#align antitone.mul Antitone.mul

end Monotone

theorem le_iff_exists_nonneg_add (a b : α) : a ≤ b ↔ ∃ c ≥ 0, b = a + c :=
  ⟨fun h => ⟨b - a, sub_nonneg.mpr h, by simp⟩, fun ⟨c, hc, h⟩ => by
                                         -- 🎉 no goals
    rw [h, le_add_iff_nonneg_right]
    -- ⊢ 0 ≤ c
    exact hc⟩
    -- 🎉 no goals
#align le_iff_exists_nonneg_add le_iff_exists_nonneg_add

end OrderedRing

section OrderedCommRing

variable [OrderedCommRing α]

-- See note [lower instance priority]
instance (priority := 100) OrderedCommRing.toOrderedCommSemiring : OrderedCommSemiring α :=
  { OrderedRing.toOrderedSemiring, ‹OrderedCommRing α› with }
#align ordered_comm_ring.to_ordered_comm_semiring OrderedCommRing.toOrderedCommSemiring

end OrderedCommRing

section StrictOrderedSemiring

variable [StrictOrderedSemiring α] {a b c d : α}

-- see Note [lower instance priority]
instance (priority := 200) StrictOrderedSemiring.toPosMulStrictMono : PosMulStrictMono α :=
  ⟨fun x _ _ h => StrictOrderedSemiring.mul_lt_mul_of_pos_left _ _ _ h x.prop⟩
#align strict_ordered_semiring.to_pos_mul_strict_mono StrictOrderedSemiring.toPosMulStrictMono

-- see Note [lower instance priority]
instance (priority := 200) StrictOrderedSemiring.toMulPosStrictMono : MulPosStrictMono α :=
  ⟨fun x _ _ h => StrictOrderedSemiring.mul_lt_mul_of_pos_right _ _ _ h x.prop⟩
#align strict_ordered_semiring.to_mul_pos_strict_mono StrictOrderedSemiring.toMulPosStrictMono

-- See note [reducible non-instances]
/-- A choice-free version of `StrictOrderedSemiring.toOrderedSemiring` to avoid using choice in
basic `Nat` lemmas. -/
@[reducible]
def StrictOrderedSemiring.toOrderedSemiring' [@DecidableRel α (· ≤ ·)] : OrderedSemiring α :=
  { ‹StrictOrderedSemiring α› with
    mul_le_mul_of_nonneg_left := fun a b c hab hc => by
      obtain rfl | hab := Decidable.eq_or_lt_of_le hab
      -- ⊢ c * a ≤ c * a
      · rfl
        -- 🎉 no goals
      obtain rfl | hc := Decidable.eq_or_lt_of_le hc
      -- ⊢ 0 * a ≤ 0 * b
      · simp
        -- 🎉 no goals
      · exact (mul_lt_mul_of_pos_left hab hc).le,
        -- 🎉 no goals
    mul_le_mul_of_nonneg_right := fun a b c hab hc => by
      obtain rfl | hab := Decidable.eq_or_lt_of_le hab
      -- ⊢ a * c ≤ a * c
      · rfl
        -- 🎉 no goals
      obtain rfl | hc := Decidable.eq_or_lt_of_le hc
      -- ⊢ a * 0 ≤ b * 0
      · simp
        -- 🎉 no goals
      · exact (mul_lt_mul_of_pos_right hab hc).le }
        -- 🎉 no goals
#align strict_ordered_semiring.to_ordered_semiring' StrictOrderedSemiring.toOrderedSemiring'

-- see Note [lower instance priority]
instance (priority := 100) StrictOrderedSemiring.toOrderedSemiring : OrderedSemiring α :=
  { ‹StrictOrderedSemiring α› with
    mul_le_mul_of_nonneg_left := fun _ _ _ =>
      letI := @StrictOrderedSemiring.toOrderedSemiring' α _ (Classical.decRel _)
      mul_le_mul_of_nonneg_left,
    mul_le_mul_of_nonneg_right := fun _ _ _ =>
      letI := @StrictOrderedSemiring.toOrderedSemiring' α _ (Classical.decRel _)
      mul_le_mul_of_nonneg_right }
#align strict_ordered_semiring.to_ordered_semiring StrictOrderedSemiring.toOrderedSemiring

theorem mul_lt_mul (hac : a < c) (hbd : b ≤ d) (hb : 0 < b) (hc : 0 ≤ c) : a * b < c * d :=
  (mul_lt_mul_of_pos_right hac hb).trans_le <| mul_le_mul_of_nonneg_left hbd hc
#align mul_lt_mul mul_lt_mul

theorem mul_lt_mul' (hac : a ≤ c) (hbd : b < d) (hb : 0 ≤ b) (hc : 0 < c) : a * b < c * d :=
  (mul_le_mul_of_nonneg_right hac hb).trans_lt <| mul_lt_mul_of_pos_left hbd hc
#align mul_lt_mul' mul_lt_mul'

@[simp]
theorem pow_pos (H : 0 < a) : ∀ n : ℕ, 0 < a ^ n
  | 0 => by
    nontriviality
    -- ⊢ 0 < a ^ 0
    rw [pow_zero]
    -- ⊢ 0 < 1
    exact zero_lt_one
    -- 🎉 no goals
  | n + 1 => by
    rw [pow_succ]
    -- ⊢ 0 < a * a ^ n
    exact mul_pos H (pow_pos H _)
    -- 🎉 no goals
#align pow_pos pow_pos

theorem mul_self_lt_mul_self (h1 : 0 ≤ a) (h2 : a < b) : a * a < b * b :=
  mul_lt_mul' h2.le h2 h1 <| h1.trans_lt h2
#align mul_self_lt_mul_self mul_self_lt_mul_self

-- In the next lemma, we used to write `Set.Ici 0` instead of `{x | 0 ≤ x}`.
-- As this lemma is not used outside this file,
-- and the import for `Set.Ici` is not otherwise needed until later,
-- we choose not to use it here.
theorem strictMonoOn_mul_self : StrictMonoOn (fun x : α => x * x) { x | 0 ≤ x } :=
  fun _ hx _ _ hxy => mul_self_lt_mul_self hx hxy
#align strict_mono_on_mul_self strictMonoOn_mul_self

-- See Note [decidable namespace]
protected theorem Decidable.mul_lt_mul'' [@DecidableRel α (· ≤ ·)] (h1 : a < c) (h2 : b < d)
    (h3 : 0 ≤ a) (h4 : 0 ≤ b) : a * b < c * d :=
  h4.lt_or_eq_dec.elim (fun b0 => mul_lt_mul h1 h2.le b0 <| h3.trans h1.le) fun b0 => by
    rw [← b0, mul_zero]; exact mul_pos (h3.trans_lt h1) (h4.trans_lt h2)
    -- ⊢ 0 < c * d
                         -- 🎉 no goals
#align decidable.mul_lt_mul'' Decidable.mul_lt_mul''

theorem mul_lt_mul'' : a < c → b < d → 0 ≤ a → 0 ≤ b → a * b < c * d := by classical
  exact Decidable.mul_lt_mul''
#align mul_lt_mul'' mul_lt_mul''

theorem lt_mul_left (hn : 0 < a) (hm : 1 < b) : a < b * a := by
  convert mul_lt_mul_of_pos_right hm hn
  -- ⊢ a = 1 * a
  rw [one_mul]
  -- 🎉 no goals
#align lt_mul_left lt_mul_left

theorem lt_mul_right (hn : 0 < a) (hm : 1 < b) : a < a * b := by
  convert mul_lt_mul_of_pos_left hm hn
  -- ⊢ a = a * 1
  rw [mul_one]
  -- 🎉 no goals
#align lt_mul_right lt_mul_right

theorem lt_mul_self (hn : 1 < a) : a < a * a :=
  lt_mul_left (hn.trans_le' zero_le_one) hn
#align lt_mul_self lt_mul_self

section Monotone

variable [Preorder β] {f g : β → α}

theorem strictMono_mul_left_of_pos (ha : 0 < a) : StrictMono fun x => a * x := fun _ _ b_lt_c =>
  mul_lt_mul_of_pos_left b_lt_c ha
#align strict_mono_mul_left_of_pos strictMono_mul_left_of_pos

theorem strictMono_mul_right_of_pos (ha : 0 < a) : StrictMono fun x => x * a := fun _ _ b_lt_c =>
  mul_lt_mul_of_pos_right b_lt_c ha
#align strict_mono_mul_right_of_pos strictMono_mul_right_of_pos

theorem StrictMono.mul_const (hf : StrictMono f) (ha : 0 < a) : StrictMono fun x => f x * a :=
  (strictMono_mul_right_of_pos ha).comp hf
#align strict_mono.mul_const StrictMono.mul_const

theorem StrictMono.const_mul (hf : StrictMono f) (ha : 0 < a) : StrictMono fun x => a * f x :=
  (strictMono_mul_left_of_pos ha).comp hf
#align strict_mono.const_mul StrictMono.const_mul

theorem StrictAnti.mul_const (hf : StrictAnti f) (ha : 0 < a) : StrictAnti fun x => f x * a :=
  (strictMono_mul_right_of_pos ha).comp_strictAnti hf
#align strict_anti.mul_const StrictAnti.mul_const

theorem StrictAnti.const_mul (hf : StrictAnti f) (ha : 0 < a) : StrictAnti fun x => a * f x :=
  (strictMono_mul_left_of_pos ha).comp_strictAnti hf
#align strict_anti.const_mul StrictAnti.const_mul

theorem StrictMono.mul_monotone (hf : StrictMono f) (hg : Monotone g) (hf₀ : ∀ x, 0 ≤ f x)
    (hg₀ : ∀ x, 0 < g x) : StrictMono (f * g) := fun _ _ h =>
  mul_lt_mul (hf h) (hg h.le) (hg₀ _) (hf₀ _)
#align strict_mono.mul_monotone StrictMono.mul_monotone

theorem Monotone.mul_strictMono (hf : Monotone f) (hg : StrictMono g) (hf₀ : ∀ x, 0 < f x)
    (hg₀ : ∀ x, 0 ≤ g x) : StrictMono (f * g) := fun _ _ h =>
  mul_lt_mul' (hf h.le) (hg h) (hg₀ _) (hf₀ _)
#align monotone.mul_strict_mono Monotone.mul_strictMono

theorem StrictMono.mul (hf : StrictMono f) (hg : StrictMono g) (hf₀ : ∀ x, 0 ≤ f x)
    (hg₀ : ∀ x, 0 ≤ g x) : StrictMono (f * g) := fun _ _ h =>
  mul_lt_mul'' (hf h) (hg h) (hf₀ _) (hg₀ _)
#align strict_mono.mul StrictMono.mul

end Monotone

theorem lt_two_mul_self (ha : 0 < a) : a < 2 * a :=
  lt_mul_of_one_lt_left ha one_lt_two
#align lt_two_mul_self lt_two_mul_self

-- see Note [lower instance priority]
instance (priority := 100) StrictOrderedSemiring.toNoMaxOrder : NoMaxOrder α :=
  ⟨fun a => ⟨a + 1, lt_add_of_pos_right _ one_pos⟩⟩
#align strict_ordered_semiring.to_no_max_order StrictOrderedSemiring.toNoMaxOrder

end StrictOrderedSemiring

section StrictOrderedCommSemiring

variable [StrictOrderedCommSemiring α]

-- See note [reducible non-instances]
/-- A choice-free version of `StrictOrderedCommSemiring.toOrderedCommSemiring'` to avoid using
choice in basic `Nat` lemmas. -/
@[reducible]
def StrictOrderedCommSemiring.toOrderedCommSemiring' [@DecidableRel α (· ≤ ·)] :
    OrderedCommSemiring α :=
  { ‹StrictOrderedCommSemiring α›, StrictOrderedSemiring.toOrderedSemiring' with }
#align strict_ordered_comm_semiring.to_ordered_comm_semiring' StrictOrderedCommSemiring.toOrderedCommSemiring'

-- see Note [lower instance priority]
instance (priority := 100) StrictOrderedCommSemiring.toOrderedCommSemiring :
    OrderedCommSemiring α :=
  { ‹StrictOrderedCommSemiring α›, StrictOrderedSemiring.toOrderedSemiring with }
#align strict_ordered_comm_semiring.to_ordered_comm_semiring StrictOrderedCommSemiring.toOrderedCommSemiring

end StrictOrderedCommSemiring

section StrictOrderedRing

variable [StrictOrderedRing α] {a b c : α}

-- see Note [lower instance priority]
instance (priority := 100) StrictOrderedRing.toStrictOrderedSemiring : StrictOrderedSemiring α :=
  { ‹StrictOrderedRing α›, (Ring.toSemiring : Semiring α) with
    le_of_add_le_add_left := @le_of_add_le_add_left α _ _ _,
    mul_lt_mul_of_pos_left := fun a b c h hc => by
      simpa only [mul_sub, sub_pos] using StrictOrderedRing.mul_pos _ _ hc (sub_pos.2 h),
      -- 🎉 no goals
    mul_lt_mul_of_pos_right := fun a b c h hc => by
      simpa only [sub_mul, sub_pos] using StrictOrderedRing.mul_pos _ _ (sub_pos.2 h) hc }
      -- 🎉 no goals
#align strict_ordered_ring.to_strict_ordered_semiring StrictOrderedRing.toStrictOrderedSemiring

-- See note [reducible non-instances]
/-- A choice-free version of `StrictOrderedRing.toOrderedRing` to avoid using choice in basic
`Int` lemmas. -/
@[reducible]
def StrictOrderedRing.toOrderedRing' [@DecidableRel α (· ≤ ·)] : OrderedRing α :=
  { ‹StrictOrderedRing α›, (Ring.toSemiring : Semiring α) with
    mul_nonneg := fun a b ha hb => by
      obtain ha | ha := Decidable.eq_or_lt_of_le ha
      -- ⊢ 0 ≤ a * b
      · rw [← ha, zero_mul]
        -- 🎉 no goals
      obtain hb | hb := Decidable.eq_or_lt_of_le hb
      -- ⊢ 0 ≤ a * b
      · rw [← hb, mul_zero]
        -- 🎉 no goals
      · exact (StrictOrderedRing.mul_pos _ _ ha hb).le }
        -- 🎉 no goals
#align strict_ordered_ring.to_ordered_ring' StrictOrderedRing.toOrderedRing'

-- see Note [lower instance priority]
instance (priority := 100) StrictOrderedRing.toOrderedRing : OrderedRing α :=
  { ‹StrictOrderedRing α› with
    mul_nonneg := fun a b =>
      letI := @StrictOrderedRing.toOrderedRing' α _ (Classical.decRel _)
      mul_nonneg }
#align strict_ordered_ring.to_ordered_ring StrictOrderedRing.toOrderedRing

theorem mul_lt_mul_of_neg_left (h : b < a) (hc : c < 0) : c * a < c * b := by
  simpa only [neg_mul, neg_lt_neg_iff] using mul_lt_mul_of_pos_left h (neg_pos_of_neg hc)
  -- 🎉 no goals
#align mul_lt_mul_of_neg_left mul_lt_mul_of_neg_left

theorem mul_lt_mul_of_neg_right (h : b < a) (hc : c < 0) : a * c < b * c := by
  simpa only [mul_neg, neg_lt_neg_iff] using mul_lt_mul_of_pos_right h (neg_pos_of_neg hc)
  -- 🎉 no goals
#align mul_lt_mul_of_neg_right mul_lt_mul_of_neg_right

theorem mul_pos_of_neg_of_neg {a b : α} (ha : a < 0) (hb : b < 0) : 0 < a * b := by
  simpa only [zero_mul] using mul_lt_mul_of_neg_right ha hb
  -- 🎉 no goals
#align mul_pos_of_neg_of_neg mul_pos_of_neg_of_neg

/-- Variant of `mul_lt_of_lt_one_left` for `b` negative instead of positive. -/
theorem lt_mul_of_lt_one_left (hb : b < 0) (h : a < 1) : b < a * b := by
  simpa only [one_mul] using mul_lt_mul_of_neg_right h hb
  -- 🎉 no goals
#align lt_mul_of_lt_one_left lt_mul_of_lt_one_left

/-- Variant of `lt_mul_of_one_lt_left` for `b` negative instead of positive. -/
theorem mul_lt_of_one_lt_left (hb : b < 0) (h : 1 < a) : a * b < b := by
  simpa only [one_mul] using mul_lt_mul_of_neg_right h hb
  -- 🎉 no goals
#align mul_lt_of_one_lt_left mul_lt_of_one_lt_left

/-- Variant of `mul_lt_of_lt_one_right` for `a` negative instead of positive. -/
theorem lt_mul_of_lt_one_right (ha : a < 0) (h : b < 1) : a < a * b := by
  simpa only [mul_one] using mul_lt_mul_of_neg_left h ha
  -- 🎉 no goals
#align lt_mul_of_lt_one_right lt_mul_of_lt_one_right

/-- Variant of `lt_mul_of_lt_one_right` for `a` negative instead of positive. -/
theorem mul_lt_of_one_lt_right (ha : a < 0) (h : 1 < b) : a * b < a := by
  simpa only [mul_one] using mul_lt_mul_of_neg_left h ha
  -- 🎉 no goals
#align mul_lt_of_one_lt_right mul_lt_of_one_lt_right

section Monotone

variable [Preorder β] {f g : β → α}

theorem strictAnti_mul_left {a : α} (ha : a < 0) : StrictAnti ((· * ·) a) := fun _ _ b_lt_c =>
  mul_lt_mul_of_neg_left b_lt_c ha
#align strict_anti_mul_left strictAnti_mul_left

theorem strictAnti_mul_right {a : α} (ha : a < 0) : StrictAnti fun x => x * a := fun _ _ b_lt_c =>
  mul_lt_mul_of_neg_right b_lt_c ha
#align strict_anti_mul_right strictAnti_mul_right

theorem StrictMono.const_mul_of_neg (hf : StrictMono f) (ha : a < 0) :
    StrictAnti fun x => a * f x :=
  (strictAnti_mul_left ha).comp_strictMono hf
#align strict_mono.const_mul_of_neg StrictMono.const_mul_of_neg

theorem StrictMono.mul_const_of_neg (hf : StrictMono f) (ha : a < 0) :
    StrictAnti fun x => f x * a :=
  (strictAnti_mul_right ha).comp_strictMono hf
#align strict_mono.mul_const_of_neg StrictMono.mul_const_of_neg

theorem StrictAnti.const_mul_of_neg (hf : StrictAnti f) (ha : a < 0) :
    StrictMono fun x => a * f x :=
  (strictAnti_mul_left ha).comp hf
#align strict_anti.const_mul_of_neg StrictAnti.const_mul_of_neg

theorem StrictAnti.mul_const_of_neg (hf : StrictAnti f) (ha : a < 0) :
    StrictMono fun x => f x * a :=
  (strictAnti_mul_right ha).comp hf
#align strict_anti.mul_const_of_neg StrictAnti.mul_const_of_neg

end Monotone

end StrictOrderedRing

section StrictOrderedCommRing

variable [StrictOrderedCommRing α]

-- See note [reducible non-instances]
/-- A choice-free version of `StrictOrderedCommRing.toOrderedCommRing` to avoid using
choice in basic `Int` lemmas. -/
@[reducible]
def StrictOrderedCommRing.toOrderedCommRing' [@DecidableRel α (· ≤ ·)] : OrderedCommRing α :=
  { ‹StrictOrderedCommRing α›, StrictOrderedRing.toOrderedRing' with }
#align strict_ordered_comm_ring.to_ordered_comm_ring' StrictOrderedCommRing.toOrderedCommRing'

-- See note [lower instance priority]
instance (priority := 100) StrictOrderedCommRing.toStrictOrderedCommSemiring :
    StrictOrderedCommSemiring α :=
  { ‹StrictOrderedCommRing α›, StrictOrderedRing.toStrictOrderedSemiring with }
#align strict_ordered_comm_ring.to_strict_ordered_comm_semiring StrictOrderedCommRing.toStrictOrderedCommSemiring

-- See note [lower instance priority]
instance (priority := 100) StrictOrderedCommRing.toOrderedCommRing : OrderedCommRing α :=
  { ‹StrictOrderedCommRing α›, StrictOrderedRing.toOrderedRing with }
#align strict_ordered_comm_ring.to_ordered_comm_ring StrictOrderedCommRing.toOrderedCommRing

end StrictOrderedCommRing

section LinearOrderedSemiring

variable [LinearOrderedSemiring α] {a b c d : α}

-- see Note [lower instance priority]
instance (priority := 200) LinearOrderedSemiring.toPosMulReflectLT : PosMulReflectLT α :=
  ⟨fun a _ _ => (monotone_mul_left_of_nonneg a.2).reflect_lt⟩
#align linear_ordered_semiring.to_pos_mul_reflect_lt LinearOrderedSemiring.toPosMulReflectLT

-- see Note [lower instance priority]
instance (priority := 200) LinearOrderedSemiring.toMulPosReflectLT : MulPosReflectLT α :=
  ⟨fun a _ _ => (monotone_mul_right_of_nonneg a.2).reflect_lt⟩
#align linear_ordered_semiring.to_mul_pos_reflect_lt LinearOrderedSemiring.toMulPosReflectLT

attribute [local instance] LinearOrderedSemiring.decidableLE LinearOrderedSemiring.decidableLT

theorem nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nnonneg (hab : 0 ≤ a * b) :
    0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  refine' Decidable.or_iff_not_and_not.2 _
  -- ⊢ ¬(¬(0 ≤ a ∧ 0 ≤ b) ∧ ¬(a ≤ 0 ∧ b ≤ 0))
  simp only [not_and, not_le]; intro ab nab; apply not_lt_of_le hab _
  -- ⊢ (0 ≤ a → b < 0) → ¬(a ≤ 0 → 0 < b)
                               -- ⊢ False
                                             -- ⊢ a * b < 0
  -- Porting note: for the middle case, we used to have `rfl`, but it is now rejected.
  -- https://github.com/leanprover/std4/issues/62
  rcases lt_trichotomy 0 a with (ha | ha | ha)
  · exact mul_neg_of_pos_of_neg ha (ab ha.le)
    -- 🎉 no goals
  · subst ha
    -- ⊢ 0 * b < 0
    exact ((ab le_rfl).asymm (nab le_rfl)).elim
    -- 🎉 no goals
  · exact mul_neg_of_neg_of_pos ha (nab ha.le)
    -- 🎉 no goals
#align nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nnonneg nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nnonneg

theorem nonneg_of_mul_nonneg_left (h : 0 ≤ a * b) (hb : 0 < b) : 0 ≤ a :=
  le_of_not_gt fun ha => (mul_neg_of_neg_of_pos ha hb).not_le h
#align nonneg_of_mul_nonneg_left nonneg_of_mul_nonneg_left

theorem nonneg_of_mul_nonneg_right (h : 0 ≤ a * b) (ha : 0 < a) : 0 ≤ b :=
  le_of_not_gt fun hb => (mul_neg_of_pos_of_neg ha hb).not_le h
#align nonneg_of_mul_nonneg_right nonneg_of_mul_nonneg_right

theorem neg_of_mul_neg_left (h : a * b < 0) (hb : 0 ≤ b) : a < 0 :=
  lt_of_not_ge fun ha => (mul_nonneg ha hb).not_lt h
#align neg_of_mul_neg_left neg_of_mul_neg_left

theorem neg_of_mul_neg_right (h : a * b < 0) (ha : 0 ≤ a) : b < 0 :=
  lt_of_not_ge fun hb => (mul_nonneg ha hb).not_lt h
#align neg_of_mul_neg_right neg_of_mul_neg_right

theorem nonpos_of_mul_nonpos_left (h : a * b ≤ 0) (hb : 0 < b) : a ≤ 0 :=
  le_of_not_gt fun ha : a > 0 => (mul_pos ha hb).not_le h
#align nonpos_of_mul_nonpos_left nonpos_of_mul_nonpos_left

theorem nonpos_of_mul_nonpos_right (h : a * b ≤ 0) (ha : 0 < a) : b ≤ 0 :=
  le_of_not_gt fun hb : b > 0 => (mul_pos ha hb).not_le h
#align nonpos_of_mul_nonpos_right nonpos_of_mul_nonpos_right

@[simp]
theorem zero_le_mul_left (h : 0 < c) : 0 ≤ c * b ↔ 0 ≤ b := by
  -- Porting note: this used to be by:
  -- convert mul_le_mul_left h
  -- simp
  -- but the `convert` no longer works.
  simpa using (mul_le_mul_left h : c * 0 ≤ c * b ↔ 0 ≤ b)
  -- 🎉 no goals
#align zero_le_mul_left zero_le_mul_left

@[simp]
theorem zero_le_mul_right (h : 0 < c) : 0 ≤ b * c ↔ 0 ≤ b := by
  simpa using (mul_le_mul_right h : 0 * c ≤ b * c ↔ 0 ≤ b)
  -- 🎉 no goals
#align zero_le_mul_right zero_le_mul_right

-- Porting note: we used to not need the type annotation on `(0 : α)` at the start of the `calc`.
theorem add_le_mul_of_left_le_right (a2 : 2 ≤ a) (ab : a ≤ b) : a + b ≤ a * b :=
  have : 0 < b :=
    calc (0 : α)
      _ < 2 := zero_lt_two
      _ ≤ a := a2
      _ ≤ b := ab
  calc
    a + b ≤ b + b := add_le_add_right ab b
    _ = 2 * b := (two_mul b).symm
    _ ≤ a * b := (mul_le_mul_right this).mpr a2
#align add_le_mul_of_left_le_right add_le_mul_of_left_le_right

-- Porting note: we used to not need the type annotation on `(0 : α)` at the start of the `calc`.
theorem add_le_mul_of_right_le_left (b2 : 2 ≤ b) (ba : b ≤ a) : a + b ≤ a * b :=
  have : 0 < a :=
    calc (0 : α)
      _ < 2 := zero_lt_two
      _ ≤ b := b2
      _ ≤ a := ba
  calc
    a + b ≤ a + a := add_le_add_left ba a
    _ = a * 2 := (mul_two a).symm
    _ ≤ a * b := (mul_le_mul_left this).mpr b2
#align add_le_mul_of_right_le_left add_le_mul_of_right_le_left

theorem add_le_mul (a2 : 2 ≤ a) (b2 : 2 ≤ b) : a + b ≤ a * b :=
  if hab : a ≤ b then add_le_mul_of_left_le_right a2 hab
  else add_le_mul_of_right_le_left b2 (le_of_not_le hab)
#align add_le_mul add_le_mul

theorem add_le_mul' (a2 : 2 ≤ a) (b2 : 2 ≤ b) : a + b ≤ b * a :=
  (le_of_eq (add_comm _ _)).trans (add_le_mul b2 a2)
#align add_le_mul' add_le_mul'

set_option linter.deprecated false in
section

@[simp]
theorem bit0_le_bit0 : bit0 a ≤ bit0 b ↔ a ≤ b := by
  rw [bit0, bit0, ← two_mul, ← two_mul, mul_le_mul_left (zero_lt_two : 0 < (2 : α))]
  -- 🎉 no goals
#align bit0_le_bit0 bit0_le_bit0

@[simp]
theorem bit0_lt_bit0 : bit0 a < bit0 b ↔ a < b := by
  rw [bit0, bit0, ← two_mul, ← two_mul, mul_lt_mul_left (zero_lt_two : 0 < (2 : α))]
  -- 🎉 no goals
#align bit0_lt_bit0 bit0_lt_bit0

@[simp]
theorem bit1_le_bit1 : bit1 a ≤ bit1 b ↔ a ≤ b :=
  (add_le_add_iff_right 1).trans bit0_le_bit0
#align bit1_le_bit1 bit1_le_bit1

@[simp]
theorem bit1_lt_bit1 : bit1 a < bit1 b ↔ a < b :=
  (add_lt_add_iff_right 1).trans bit0_lt_bit0
#align bit1_lt_bit1 bit1_lt_bit1

@[simp]
theorem one_le_bit1 : (1 : α) ≤ bit1 a ↔ 0 ≤ a := by
  rw [bit1, le_add_iff_nonneg_left, bit0, ← two_mul, zero_le_mul_left (zero_lt_two : 0 < (2 : α))]
  -- 🎉 no goals
#align one_le_bit1 one_le_bit1

@[simp]
theorem one_lt_bit1 : (1 : α) < bit1 a ↔ 0 < a := by
  rw [bit1, lt_add_iff_pos_left, bit0, ← two_mul, zero_lt_mul_left (zero_lt_two : 0 < (2 : α))]
  -- 🎉 no goals
#align one_lt_bit1 one_lt_bit1

@[simp]
theorem zero_le_bit0 : (0 : α) ≤ bit0 a ↔ 0 ≤ a := by
  rw [bit0, ← two_mul, zero_le_mul_left (zero_lt_two : 0 < (2 : α))]
  -- 🎉 no goals
#align zero_le_bit0 zero_le_bit0

@[simp]
theorem zero_lt_bit0 : (0 : α) < bit0 a ↔ 0 < a := by
  rw [bit0, ← two_mul, zero_lt_mul_left (zero_lt_two : 0 < (2 : α))]
  -- 🎉 no goals
#align zero_lt_bit0 zero_lt_bit0

end

theorem mul_nonneg_iff_right_nonneg_of_pos (ha : 0 < a) : 0 ≤ a * b ↔ 0 ≤ b :=
  ⟨fun h => nonneg_of_mul_nonneg_right h ha, mul_nonneg ha.le⟩
#align mul_nonneg_iff_right_nonneg_of_pos mul_nonneg_iff_right_nonneg_of_pos

theorem mul_nonneg_iff_left_nonneg_of_pos (hb : 0 < b) : 0 ≤ a * b ↔ 0 ≤ a :=
  ⟨fun h => nonneg_of_mul_nonneg_left h hb, fun h => mul_nonneg h hb.le⟩
#align mul_nonneg_iff_left_nonneg_of_pos mul_nonneg_iff_left_nonneg_of_pos

theorem nonpos_of_mul_nonneg_left (h : 0 ≤ a * b) (hb : b < 0) : a ≤ 0 :=
  le_of_not_gt fun ha => absurd h (mul_neg_of_pos_of_neg ha hb).not_le
#align nonpos_of_mul_nonneg_left nonpos_of_mul_nonneg_left

theorem nonpos_of_mul_nonneg_right (h : 0 ≤ a * b) (ha : a < 0) : b ≤ 0 :=
  le_of_not_gt fun hb => absurd h (mul_neg_of_neg_of_pos ha hb).not_le
#align nonpos_of_mul_nonneg_right nonpos_of_mul_nonneg_right

@[simp]
theorem Units.inv_pos {u : αˣ} : (0 : α) < ↑u⁻¹ ↔ (0 : α) < u :=
  have : ∀ {u : αˣ}, (0 : α) < u → (0 : α) < ↑u⁻¹ := @fun u h =>
    (zero_lt_mul_left h).mp <| u.mul_inv.symm ▸ zero_lt_one
  ⟨this, this⟩
#align units.inv_pos Units.inv_pos

@[simp]
theorem Units.inv_neg {u : αˣ} : ↑u⁻¹ < (0 : α) ↔ ↑u < (0 : α) :=
  have : ∀ {u : αˣ}, ↑u < (0 : α) → ↑u⁻¹ < (0 : α) := @fun u h =>
    neg_of_mul_pos_right (u.mul_inv.symm ▸ zero_lt_one) h.le
  ⟨this, this⟩
#align units.inv_neg Units.inv_neg

theorem cmp_mul_pos_left (ha : 0 < a) (b c : α) : cmp (a * b) (a * c) = cmp b c :=
  (strictMono_mul_left_of_pos ha).cmp_map_eq b c
#align cmp_mul_pos_left cmp_mul_pos_left

theorem cmp_mul_pos_right (ha : 0 < a) (b c : α) : cmp (b * a) (c * a) = cmp b c :=
  (strictMono_mul_right_of_pos ha).cmp_map_eq b c
#align cmp_mul_pos_right cmp_mul_pos_right

theorem mul_max_of_nonneg (b c : α) (ha : 0 ≤ a) : a * max b c = max (a * b) (a * c) :=
  (monotone_mul_left_of_nonneg ha).map_max
#align mul_max_of_nonneg mul_max_of_nonneg

theorem mul_min_of_nonneg (b c : α) (ha : 0 ≤ a) : a * min b c = min (a * b) (a * c) :=
  (monotone_mul_left_of_nonneg ha).map_min
#align mul_min_of_nonneg mul_min_of_nonneg

theorem max_mul_of_nonneg (a b : α) (hc : 0 ≤ c) : max a b * c = max (a * c) (b * c) :=
  (monotone_mul_right_of_nonneg hc).map_max
#align max_mul_of_nonneg max_mul_of_nonneg

theorem min_mul_of_nonneg (a b : α) (hc : 0 ≤ c) : min a b * c = min (a * c) (b * c) :=
  (monotone_mul_right_of_nonneg hc).map_min
#align min_mul_of_nonneg min_mul_of_nonneg

theorem le_of_mul_le_of_one_le {a b c : α} (h : a * c ≤ b) (hb : 0 ≤ b) (hc : 1 ≤ c) : a ≤ b :=
  le_of_mul_le_mul_right (h.trans <| le_mul_of_one_le_right hb hc) <| zero_lt_one.trans_le hc
#align le_of_mul_le_of_one_le le_of_mul_le_of_one_le

theorem nonneg_le_nonneg_of_sq_le_sq {a b : α} (hb : 0 ≤ b) (h : a * a ≤ b * b) : a ≤ b :=
  le_of_not_gt fun hab => (mul_self_lt_mul_self hb hab).not_le h
#align nonneg_le_nonneg_of_sq_le_sq nonneg_le_nonneg_of_sq_le_sq

theorem mul_self_le_mul_self_iff {a b : α} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a ≤ b ↔ a * a ≤ b * b :=
  ⟨mul_self_le_mul_self h1, nonneg_le_nonneg_of_sq_le_sq h2⟩
#align mul_self_le_mul_self_iff mul_self_le_mul_self_iff

theorem mul_self_lt_mul_self_iff {a b : α} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a < b ↔ a * a < b * b :=
  ((@strictMonoOn_mul_self α _).lt_iff_lt h1 h2).symm
#align mul_self_lt_mul_self_iff mul_self_lt_mul_self_iff

theorem mul_self_inj {a b : α} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a * a = b * b ↔ a = b :=
  (@strictMonoOn_mul_self α _).eq_iff_eq h1 h2
#align mul_self_inj mul_self_inj

end LinearOrderedSemiring

-- See note [lower instance priority]
instance (priority := 100) LinearOrderedCommSemiring.toLinearOrderedCancelAddCommMonoid
    [LinearOrderedCommSemiring α] : LinearOrderedCancelAddCommMonoid α :=
  { ‹LinearOrderedCommSemiring α› with }
#align linear_ordered_comm_semiring.to_linear_ordered_cancel_add_comm_monoid LinearOrderedCommSemiring.toLinearOrderedCancelAddCommMonoid

section LinearOrderedRing

variable [LinearOrderedRing α] {a b c : α}

attribute [local instance] LinearOrderedRing.decidableLE LinearOrderedRing.decidableLT

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedRing.toLinearOrderedSemiring : LinearOrderedSemiring α :=
  { ‹LinearOrderedRing α›, StrictOrderedRing.toStrictOrderedSemiring with }
#align linear_ordered_ring.to_linear_ordered_semiring LinearOrderedRing.toLinearOrderedSemiring

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedRing.toLinearOrderedAddCommGroup :
    LinearOrderedAddCommGroup α :=
  { ‹LinearOrderedRing α› with }
#align linear_ordered_ring.to_linear_ordered_add_comm_group LinearOrderedRing.toLinearOrderedAddCommGroup

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedRing.noZeroDivisors : NoZeroDivisors α :=
  { ‹LinearOrderedRing α› with
    eq_zero_or_eq_zero_of_mul_eq_zero := by
      intro a b hab
      -- ⊢ a = 0 ∨ b = 0
      refine' Decidable.or_iff_not_and_not.2 fun h => _; revert hab
      -- ⊢ False
                                                         -- ⊢ a * b = 0 → False
      cases' lt_or_gt_of_ne h.1 with ha ha <;> cases' lt_or_gt_of_ne h.2 with hb hb
      -- ⊢ a * b = 0 → False
                                               -- ⊢ a * b = 0 → False
                                               -- ⊢ a * b = 0 → False
      exacts [(mul_pos_of_neg_of_neg ha hb).ne.symm, (mul_neg_of_neg_of_pos ha hb).ne,
        (mul_neg_of_pos_of_neg ha hb).ne, (mul_pos ha hb).ne.symm] }
#align linear_ordered_ring.no_zero_divisors LinearOrderedRing.noZeroDivisors

-- see Note [lower instance priority]
--We don't want to import `Algebra.Ring.Basic`, so we cannot use `NoZeroDivisors.to_isDomain`.
instance (priority := 100) LinearOrderedRing.isDomain : IsDomain α :=
  { (inferInstance : Nontrivial α) with
    mul_left_cancel_of_ne_zero := fun {a b c} ha h => by
      rw [← sub_eq_zero, ← mul_sub] at h
      -- ⊢ b = c
      exact sub_eq_zero.1 ((eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_left ha),
      -- 🎉 no goals
    mul_right_cancel_of_ne_zero := fun {a b c} hb h => by
      rw [← sub_eq_zero, ← sub_mul] at h
      -- ⊢ a = c
      exact sub_eq_zero.1 ((eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_right hb) }
      -- 🎉 no goals
#align linear_ordered_ring.is_domain LinearOrderedRing.isDomain

theorem mul_pos_iff : 0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 :=
  ⟨pos_and_pos_or_neg_and_neg_of_mul_pos, fun h =>
    h.elim (and_imp.2 mul_pos) (and_imp.2 mul_pos_of_neg_of_neg)⟩
#align mul_pos_iff mul_pos_iff

theorem mul_neg_iff : a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b := by
  rw [← neg_pos, neg_mul_eq_mul_neg, mul_pos_iff, neg_pos, neg_lt_zero]
  -- 🎉 no goals
#align mul_neg_iff mul_neg_iff

theorem mul_nonneg_iff : 0 ≤ a * b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 :=
  ⟨nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nnonneg, fun h =>
    h.elim (and_imp.2 mul_nonneg) (and_imp.2 mul_nonneg_of_nonpos_of_nonpos)⟩
#align mul_nonneg_iff mul_nonneg_iff

/-- Out of three elements of a `LinearOrderedRing`, two must have the same sign. -/
theorem mul_nonneg_of_three (a b c : α) : 0 ≤ a * b ∨ 0 ≤ b * c ∨ 0 ≤ c * a := by
  iterate 3 rw [mul_nonneg_iff]
  -- ⊢ (0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0) ∨ (0 ≤ b ∧ 0 ≤ c ∨ b ≤ 0 ∧ c ≤ 0) ∨ 0 ≤ c ∧  …
  have or_a := le_total 0 a
  -- ⊢ (0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0) ∨ (0 ≤ b ∧ 0 ≤ c ∨ b ≤ 0 ∧ c ≤ 0) ∨ 0 ≤ c ∧  …
  have or_b := le_total 0 b
  -- ⊢ (0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0) ∨ (0 ≤ b ∧ 0 ≤ c ∨ b ≤ 0 ∧ c ≤ 0) ∨ 0 ≤ c ∧  …
  have or_c := le_total 0 c
  -- ⊢ (0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0) ∨ (0 ≤ b ∧ 0 ≤ c ∨ b ≤ 0 ∧ c ≤ 0) ∨ 0 ≤ c ∧  …
  -- Porting note used to be by `itauto` from here
  exact Or.elim or_c
    (fun (h0 : 0 ≤ c) =>
      Or.elim or_b
        (fun (h1 : 0 ≤ b) =>
            Or.elim or_a (fun (h2 : 0 ≤ a) => Or.inl (Or.inl ⟨h2, h1⟩))
              (fun (_ : a ≤ 0) => Or.inr (Or.inl (Or.inl ⟨h1, h0⟩))))
        (fun (h1 : b ≤ 0) =>
            Or.elim or_a (fun (h3 : 0 ≤ a) => Or.inr (Or.inr (Or.inl ⟨h0, h3⟩)))
              (fun (h3 : a ≤ 0) => Or.inl (Or.inr ⟨h3, h1⟩))))
    (fun (h0 : c ≤ 0) =>
      Or.elim or_b
        (fun (h4 : 0 ≤ b) =>
            Or.elim or_a (fun (h5 : 0 ≤ a) => Or.inl (Or.inl ⟨h5, h4⟩))
              (fun (h5 : a ≤ 0) => Or.inr (Or.inr (Or.inr ⟨h0, h5⟩))))
        (fun (h4 : b ≤ 0) =>
            Or.elim or_a (fun (_ : 0 ≤ a) => Or.inr (Or.inl (Or.inr ⟨h4, h0⟩)))
              (fun (h6 : a ≤ 0) => Or.inl (Or.inr ⟨h6, h4⟩))))
#align mul_nonneg_of_three mul_nonneg_of_three

theorem mul_nonpos_iff : a * b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b := by
  rw [← neg_nonneg, neg_mul_eq_mul_neg, mul_nonneg_iff, neg_nonneg, neg_nonpos]
  -- 🎉 no goals
#align mul_nonpos_iff mul_nonpos_iff

theorem mul_self_nonneg (a : α) : 0 ≤ a * a :=
  (le_total 0 a).elim (fun h => mul_nonneg h h) fun h => mul_nonneg_of_nonpos_of_nonpos h h
#align mul_self_nonneg mul_self_nonneg

@[simp]
theorem neg_le_self_iff : -a ≤ a ↔ 0 ≤ a := by
  simp [neg_le_iff_add_nonneg, ← two_mul, mul_nonneg_iff, zero_le_one, (zero_lt_two' α).not_le]
  -- 🎉 no goals
#align neg_le_self_iff neg_le_self_iff

@[simp]
theorem neg_lt_self_iff : -a < a ↔ 0 < a := by
  simp [neg_lt_iff_pos_add, ← two_mul, mul_pos_iff, zero_lt_one, (zero_lt_two' α).not_lt]
  -- 🎉 no goals
#align neg_lt_self_iff neg_lt_self_iff

@[simp]
theorem le_neg_self_iff : a ≤ -a ↔ a ≤ 0 :=
  calc
    a ≤ -a ↔ - -a ≤ -a := by rw [neg_neg]
                             -- 🎉 no goals
    _ ↔ 0 ≤ -a := neg_le_self_iff
    _ ↔ a ≤ 0 := neg_nonneg
#align le_neg_self_iff le_neg_self_iff

@[simp]
theorem lt_neg_self_iff : a < -a ↔ a < 0 :=
  calc
    a < -a ↔ - -a < -a := by rw [neg_neg]
                             -- 🎉 no goals
    _ ↔ 0 < -a := neg_lt_self_iff
    _ ↔ a < 0 := neg_pos
#align lt_neg_self_iff lt_neg_self_iff

theorem neg_one_lt_zero : -1 < (0 : α) :=
  neg_lt_zero.2 zero_lt_one
#align neg_one_lt_zero neg_one_lt_zero

@[simp]
theorem mul_le_mul_left_of_neg {a b c : α} (h : c < 0) : c * a ≤ c * b ↔ b ≤ a :=
  (strictAnti_mul_left h).le_iff_le
#align mul_le_mul_left_of_neg mul_le_mul_left_of_neg

@[simp]
theorem mul_le_mul_right_of_neg {a b c : α} (h : c < 0) : a * c ≤ b * c ↔ b ≤ a :=
  (strictAnti_mul_right h).le_iff_le
#align mul_le_mul_right_of_neg mul_le_mul_right_of_neg

@[simp]
theorem mul_lt_mul_left_of_neg {a b c : α} (h : c < 0) : c * a < c * b ↔ b < a :=
  (strictAnti_mul_left h).lt_iff_lt
#align mul_lt_mul_left_of_neg mul_lt_mul_left_of_neg

@[simp]
theorem mul_lt_mul_right_of_neg {a b c : α} (h : c < 0) : a * c < b * c ↔ b < a :=
  (strictAnti_mul_right h).lt_iff_lt
#align mul_lt_mul_right_of_neg mul_lt_mul_right_of_neg

theorem lt_of_mul_lt_mul_of_nonpos_left (h : c * a < c * b) (hc : c ≤ 0) : b < a :=
  lt_of_mul_lt_mul_left (by rwa [neg_mul, neg_mul, neg_lt_neg_iff]) <| neg_nonneg.2 hc
                            -- 🎉 no goals
#align lt_of_mul_lt_mul_of_nonpos_left lt_of_mul_lt_mul_of_nonpos_left

theorem lt_of_mul_lt_mul_of_nonpos_right (h : a * c < b * c) (hc : c ≤ 0) : b < a :=
  lt_of_mul_lt_mul_right (by rwa [mul_neg, mul_neg, neg_lt_neg_iff]) <| neg_nonneg.2 hc
                             -- 🎉 no goals
#align lt_of_mul_lt_mul_of_nonpos_right lt_of_mul_lt_mul_of_nonpos_right

theorem cmp_mul_neg_left {a : α} (ha : a < 0) (b c : α) : cmp (a * b) (a * c) = cmp c b :=
  (strictAnti_mul_left ha).cmp_map_eq b c
#align cmp_mul_neg_left cmp_mul_neg_left

theorem cmp_mul_neg_right {a : α} (ha : a < 0) (b c : α) : cmp (b * a) (c * a) = cmp c b :=
  (strictAnti_mul_right ha).cmp_map_eq b c
#align cmp_mul_neg_right cmp_mul_neg_right

theorem sub_one_lt (a : α) : a - 1 < a :=
  sub_lt_iff_lt_add.2 (lt_add_one a)
#align sub_one_lt sub_one_lt

@[simp]
theorem mul_self_pos {a : α} : 0 < a * a ↔ a ≠ 0 := by
  constructor
  -- ⊢ 0 < a * a → a ≠ 0
  · rintro h rfl
    -- ⊢ False
    rw [mul_zero] at h
    -- ⊢ False
    exact h.false
    -- 🎉 no goals
  · intro h
    -- ⊢ 0 < a * a
    cases' h.lt_or_lt with h h
    -- ⊢ 0 < a * a
    exacts [mul_pos_of_neg_of_neg h h, mul_pos h h]
    -- 🎉 no goals
#align mul_self_pos mul_self_pos

theorem mul_self_le_mul_self_of_le_of_neg_le {x y : α} (h₁ : x ≤ y) (h₂ : -x ≤ y) : x * x ≤ y * y :=
  (le_total 0 x).elim (fun h => mul_le_mul h₁ h₁ h (h.trans h₁)) fun h =>
    le_of_eq_of_le (neg_mul_neg x x).symm
      (mul_le_mul h₂ h₂ (neg_nonneg.mpr h) ((neg_nonneg.mpr h).trans h₂))
#align mul_self_le_mul_self_of_le_of_neg_le mul_self_le_mul_self_of_le_of_neg_le

theorem nonneg_of_mul_nonpos_left {a b : α} (h : a * b ≤ 0) (hb : b < 0) : 0 ≤ a :=
  le_of_not_gt fun ha => absurd h (mul_pos_of_neg_of_neg ha hb).not_le
#align nonneg_of_mul_nonpos_left nonneg_of_mul_nonpos_left

theorem nonneg_of_mul_nonpos_right {a b : α} (h : a * b ≤ 0) (ha : a < 0) : 0 ≤ b :=
  le_of_not_gt fun hb => absurd h (mul_pos_of_neg_of_neg ha hb).not_le
#align nonneg_of_mul_nonpos_right nonneg_of_mul_nonpos_right

theorem pos_of_mul_neg_left {a b : α} (h : a * b < 0) (hb : b ≤ 0) : 0 < a :=
  lt_of_not_ge fun ha => absurd h (mul_nonneg_of_nonpos_of_nonpos ha hb).not_lt
#align pos_of_mul_neg_left pos_of_mul_neg_left

theorem pos_of_mul_neg_right {a b : α} (h : a * b < 0) (ha : a ≤ 0) : 0 < b :=
  lt_of_not_ge fun hb => absurd h (mul_nonneg_of_nonpos_of_nonpos ha hb).not_lt
#align pos_of_mul_neg_right pos_of_mul_neg_right

theorem neg_iff_pos_of_mul_neg (hab : a * b < 0) : a < 0 ↔ 0 < b :=
  ⟨pos_of_mul_neg_right hab ∘ le_of_lt, neg_of_mul_neg_left hab ∘ le_of_lt⟩
#align neg_iff_pos_of_mul_neg neg_iff_pos_of_mul_neg

theorem pos_iff_neg_of_mul_neg (hab : a * b < 0) : 0 < a ↔ b < 0 :=
  ⟨neg_of_mul_neg_right hab ∘ le_of_lt, pos_of_mul_neg_left hab ∘ le_of_lt⟩
#align pos_iff_neg_of_mul_neg pos_iff_neg_of_mul_neg

/-- The sum of two squares is zero iff both elements are zero. -/
theorem mul_self_add_mul_self_eq_zero {x y : α} : x * x + y * y = 0 ↔ x = 0 ∧ y = 0 := by
  rw [add_eq_zero_iff', mul_self_eq_zero, mul_self_eq_zero] <;> apply mul_self_nonneg
  -- ⊢ 0 ≤ x * x
                                                                -- 🎉 no goals
                                                                -- 🎉 no goals
#align mul_self_add_mul_self_eq_zero mul_self_add_mul_self_eq_zero

theorem eq_zero_of_mul_self_add_mul_self_eq_zero (h : a * a + b * b = 0) : a = 0 :=
  (mul_self_add_mul_self_eq_zero.mp h).left
#align eq_zero_of_mul_self_add_mul_self_eq_zero eq_zero_of_mul_self_add_mul_self_eq_zero

end LinearOrderedRing

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedCommRing.toStrictOrderedCommRing
    [d : LinearOrderedCommRing α] : StrictOrderedCommRing α :=
  { d with }
#align linear_ordered_comm_ring.to_strict_ordered_comm_ring LinearOrderedCommRing.toStrictOrderedCommRing

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedCommRing.toLinearOrderedCommSemiring
    [d : LinearOrderedCommRing α] : LinearOrderedCommSemiring α :=
  { d, LinearOrderedRing.toLinearOrderedSemiring with }
#align linear_ordered_comm_ring.to_linear_ordered_comm_semiring LinearOrderedCommRing.toLinearOrderedCommSemiring

section LinearOrderedCommRing

variable [LinearOrderedCommRing α] {a b c d : α}

theorem max_mul_mul_le_max_mul_max (b c : α) (ha : 0 ≤ a) (hd : 0 ≤ d) :
    max (a * b) (d * c) ≤ max a c * max d b :=
  have ba : b * a ≤ max d b * max c a :=
    mul_le_mul (le_max_right d b) (le_max_right c a) ha (le_trans hd (le_max_left d b))
  have cd : c * d ≤ max a c * max b d :=
    mul_le_mul (le_max_right a c) (le_max_right b d) hd (le_trans ha (le_max_left a c))
  max_le (by simpa [mul_comm, max_comm] using ba) (by simpa [mul_comm, max_comm] using cd)
             -- 🎉 no goals
                                                      -- 🎉 no goals
#align max_mul_mul_le_max_mul_max max_mul_mul_le_max_mul_max

end LinearOrderedCommRing
