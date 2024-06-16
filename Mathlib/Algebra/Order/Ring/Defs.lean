/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Yaël Dillies
-/
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Units
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Unbundled
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Monoid.NatCast
import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Tauto

#align_import algebra.order.ring.char_zero from "leanprover-community/mathlib"@"655994e298904d7e5bbd1e18c95defd7b543eb94"
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
  - `Ring` & `IsDomain` & linear order structure
* `LinearOrderedCommRing`
  - `StrictOrderedCommRing` & totality of the order
  - `LinearOrderedRing` & commutativity of multiplication
  - `LinearOrderedCommSemiring` & additive inverses
  - `CommRing` & `IsDomain` & linear order structure
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
class OrderedCommSemiring (α : Type u) extends OrderedSemiring α, CommSemiring α where
  mul_le_mul_of_nonneg_right a b c ha hc :=
    -- parentheses ensure this generates an `optParam` rather than an `autoParam`
    (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left a b c ha hc)
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
    exact zero_le_one
  | n + 1 => by
    rw [pow_succ]
    exact mul_nonneg (pow_nonneg H _) H
#align pow_nonneg pow_nonneg

lemma pow_le_pow_of_le_one (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) : ∀ {m n : ℕ}, m ≤ n → a ^ n ≤ a ^ m
  | _, _, Nat.le.refl => le_rfl
  | _, _, Nat.le.step h => by
    rw [pow_succ']
    exact (mul_le_of_le_one_left (pow_nonneg ha₀ _) ha₁).trans $ pow_le_pow_of_le_one ha₀ ha₁ h
#align pow_le_pow_of_le_one pow_le_pow_of_le_one

lemma pow_le_of_le_one (h₀ : 0 ≤ a) (h₁ : a ≤ 1) {n : ℕ} (hn : n ≠ 0) : a ^ n ≤ a :=
  (pow_one a).subst (pow_le_pow_of_le_one h₀ h₁ (Nat.pos_of_ne_zero hn))
#align pow_le_of_le_one pow_le_of_le_one

lemma sq_le (h₀ : 0 ≤ a) (h₁ : a ≤ 1) : a ^ 2 ≤ a := pow_le_of_le_one h₀ h₁ two_ne_zero
#align sq_le sq_le

-- Porting note: it's unfortunate we need to write `(@one_le_two α)` here.
theorem add_le_mul_two_add (a2 : 2 ≤ a) (b0 : 0 ≤ b) : a + (2 + b) ≤ a * (2 + b) :=
  calc
    a + (2 + b) ≤ a + (a + a * b) :=
      add_le_add_left (add_le_add a2 <| le_mul_of_one_le_left b0 <| (@one_le_two α).trans a2) a
    _ ≤ a * (2 + b) := by rw [mul_add, mul_two, add_assoc]
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
  exact bit1_pos h.le
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

variable [ExistsAddOfLE α] [ContravariantClass α α (swap (· + ·)) (· ≤ ·)]

theorem mul_le_mul_of_nonpos_left (h : b ≤ a) (hc : c ≤ 0) : c * a ≤ c * b := by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc
  refine le_of_add_le_add_right (a := d * b + d * a) ?_
  calc
    _ = d * b := by rw [add_left_comm, ← add_mul, ← hcd, zero_mul, add_zero]
    _ ≤ d * a := mul_le_mul_of_nonneg_left h <| hcd.trans_le <| add_le_of_nonpos_left hc
    _ = _ := by rw [← add_assoc, ← add_mul, ← hcd, zero_mul, zero_add]
#align mul_le_mul_of_nonpos_left mul_le_mul_of_nonpos_left

theorem mul_le_mul_of_nonpos_right (h : b ≤ a) (hc : c ≤ 0) : a * c ≤ b * c := by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc
  refine le_of_add_le_add_right (a := b * d + a * d) ?_
  calc
    _ = b * d := by rw [add_left_comm, ← mul_add, ← hcd, mul_zero, add_zero]
    _ ≤ a * d := mul_le_mul_of_nonneg_right h <| hcd.trans_le <| add_le_of_nonpos_left hc
    _ = _ := by rw [← add_assoc, ← mul_add, ← hcd, mul_zero, zero_add]
#align mul_le_mul_of_nonpos_right mul_le_mul_of_nonpos_right

theorem mul_nonneg_of_nonpos_of_nonpos (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b := by
  simpa only [zero_mul] using mul_le_mul_of_nonpos_right ha hb
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
#align le_mul_of_le_one_left le_mul_of_le_one_left

/-- Variant of `le_mul_of_one_le_left` for `b` non-positive instead of non-negative. -/
theorem mul_le_of_one_le_left (hb : b ≤ 0) (h : 1 ≤ a) : a * b ≤ b := by
  simpa only [one_mul] using mul_le_mul_of_nonpos_right h hb
#align mul_le_of_one_le_left mul_le_of_one_le_left

/-- Variant of `mul_le_of_le_one_right` for `a` non-positive instead of non-negative. -/
theorem le_mul_of_le_one_right (ha : a ≤ 0) (h : b ≤ 1) : a ≤ a * b := by
  simpa only [mul_one] using mul_le_mul_of_nonpos_left h ha
#align le_mul_of_le_one_right le_mul_of_le_one_right

/-- Variant of `le_mul_of_one_le_right` for `a` non-positive instead of non-negative. -/
theorem mul_le_of_one_le_right (ha : a ≤ 0) (h : 1 ≤ b) : a * b ≤ a := by
  simpa only [mul_one] using mul_le_mul_of_nonpos_left h ha
#align mul_le_of_one_le_right mul_le_of_one_le_right

section Monotone

variable [Preorder β] {f g : β → α}

theorem antitone_mul_left {a : α} (ha : a ≤ 0) : Antitone (a * ·) := fun _ _ b_le_c =>
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

variable [ContravariantClass α α (· + ·) (· ≤ ·)]

lemma le_iff_exists_nonneg_add (a b : α) : a ≤ b ↔ ∃ c ≥ 0, b = a + c := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨c, rfl⟩ := exists_add_of_le h
    exact ⟨c, nonneg_of_le_add_right h, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact le_add_of_nonneg_right hc
#align le_iff_exists_nonneg_add le_iff_exists_nonneg_add

end OrderedSemiring

section OrderedRing

variable [OrderedRing α] {a b c d : α}

-- see Note [lower instance priority]
instance (priority := 100) OrderedRing.toOrderedSemiring : OrderedSemiring α :=
  { ‹OrderedRing α›, (Ring.toSemiring : Semiring α) with
    mul_le_mul_of_nonneg_left := fun a b c h hc => by
      simpa only [mul_sub, sub_nonneg] using OrderedRing.mul_nonneg _ _ hc (sub_nonneg.2 h),
    mul_le_mul_of_nonneg_right := fun a b c h hc => by
      simpa only [sub_mul, sub_nonneg] using OrderedRing.mul_nonneg _ _ (sub_nonneg.2 h) hc }
#align ordered_ring.to_ordered_semiring OrderedRing.toOrderedSemiring

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
abbrev StrictOrderedSemiring.toOrderedSemiring' [@DecidableRel α (· ≤ ·)] : OrderedSemiring α :=
  { ‹StrictOrderedSemiring α› with
    mul_le_mul_of_nonneg_left := fun a b c hab hc => by
      obtain rfl | hab := Decidable.eq_or_lt_of_le hab
      · rfl
      obtain rfl | hc := Decidable.eq_or_lt_of_le hc
      · simp
      · exact (mul_lt_mul_of_pos_left hab hc).le,
    mul_le_mul_of_nonneg_right := fun a b c hab hc => by
      obtain rfl | hab := Decidable.eq_or_lt_of_le hab
      · rfl
      obtain rfl | hc := Decidable.eq_or_lt_of_le hc
      · simp
      · exact (mul_lt_mul_of_pos_right hab hc).le }
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

-- see Note [lower instance priority]
instance (priority := 100) StrictOrderedSemiring.toCharZero [StrictOrderedSemiring α] :
    CharZero α where
  cast_injective :=
    (strictMono_nat_of_lt_succ fun n ↦ by rw [Nat.cast_succ]; apply lt_add_one).injective
#align strict_ordered_semiring.to_char_zero StrictOrderedSemiring.toCharZero

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
    rw [pow_zero]
    exact zero_lt_one
  | n + 1 => by
    rw [pow_succ]
    exact mul_pos (pow_pos H _) H
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
#align decidable.mul_lt_mul'' Decidable.mul_lt_mul''

@[gcongr]
theorem mul_lt_mul'' : a < c → b < d → 0 ≤ a → 0 ≤ b → a * b < c * d := by classical
  exact Decidable.mul_lt_mul''
#align mul_lt_mul'' mul_lt_mul''

theorem lt_mul_left (hn : 0 < a) (hm : 1 < b) : a < b * a := by
  convert mul_lt_mul_of_pos_right hm hn
  rw [one_mul]
#align lt_mul_left lt_mul_left

theorem lt_mul_right (hn : 0 < a) (hm : 1 < b) : a < a * b := by
  convert mul_lt_mul_of_pos_left hm hn
  rw [mul_one]
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

variable [ExistsAddOfLE α]

theorem mul_lt_mul_of_neg_left (h : b < a) (hc : c < 0) : c * a < c * b := by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc.le
  refine (add_lt_add_iff_right (d * b + d * a)).1 ?_
  calc
    _ = d * b := by rw [add_left_comm, ← add_mul, ← hcd, zero_mul, add_zero]
    _ < d * a := mul_lt_mul_of_pos_left h <| hcd.trans_lt <| add_lt_of_neg_left _ hc
    _ = _ := by rw [← add_assoc, ← add_mul, ← hcd, zero_mul, zero_add]
#align mul_lt_mul_of_neg_left mul_lt_mul_of_neg_left

theorem mul_lt_mul_of_neg_right (h : b < a) (hc : c < 0) : a * c < b * c := by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc.le
  refine (add_lt_add_iff_right (b * d + a * d)).1 ?_
  calc
    _ = b * d := by rw [add_left_comm, ← mul_add, ← hcd, mul_zero, add_zero]
    _ < a * d := mul_lt_mul_of_pos_right h <| hcd.trans_lt <| add_lt_of_neg_left _ hc
    _ = _ := by rw [← add_assoc, ← mul_add, ← hcd, mul_zero, zero_add]
#align mul_lt_mul_of_neg_right mul_lt_mul_of_neg_right

theorem mul_pos_of_neg_of_neg {a b : α} (ha : a < 0) (hb : b < 0) : 0 < a * b := by
  simpa only [zero_mul] using mul_lt_mul_of_neg_right ha hb
#align mul_pos_of_neg_of_neg mul_pos_of_neg_of_neg

/-- Variant of `mul_lt_of_lt_one_left` for `b` negative instead of positive. -/
theorem lt_mul_of_lt_one_left (hb : b < 0) (h : a < 1) : b < a * b := by
  simpa only [one_mul] using mul_lt_mul_of_neg_right h hb
#align lt_mul_of_lt_one_left lt_mul_of_lt_one_left

/-- Variant of `lt_mul_of_one_lt_left` for `b` negative instead of positive. -/
theorem mul_lt_of_one_lt_left (hb : b < 0) (h : 1 < a) : a * b < b := by
  simpa only [one_mul] using mul_lt_mul_of_neg_right h hb
#align mul_lt_of_one_lt_left mul_lt_of_one_lt_left

/-- Variant of `mul_lt_of_lt_one_right` for `a` negative instead of positive. -/
theorem lt_mul_of_lt_one_right (ha : a < 0) (h : b < 1) : a < a * b := by
  simpa only [mul_one] using mul_lt_mul_of_neg_left h ha
#align lt_mul_of_lt_one_right lt_mul_of_lt_one_right

/-- Variant of `lt_mul_of_lt_one_right` for `a` negative instead of positive. -/
theorem mul_lt_of_one_lt_right (ha : a < 0) (h : 1 < b) : a * b < a := by
  simpa only [mul_one] using mul_lt_mul_of_neg_left h ha
#align mul_lt_of_one_lt_right mul_lt_of_one_lt_right

section Monotone

variable [Preorder β] {f g : β → α}

theorem strictAnti_mul_left {a : α} (ha : a < 0) : StrictAnti (a * ·) := fun _ _ b_lt_c =>
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

/-- Binary **rearrangement inequality**. -/
lemma mul_add_mul_le_mul_add_mul (hab : a ≤ b) (hcd : c ≤ d) : a * d + b * c ≤ a * c + b * d := by
  obtain ⟨b, rfl⟩ := exists_add_of_le hab
  obtain ⟨d, rfl⟩ := exists_add_of_le hcd
  rw [mul_add, add_right_comm, mul_add, ← add_assoc]
  exact add_le_add_left (mul_le_mul_of_nonneg_right hab <| (le_add_iff_nonneg_right _).1 hcd) _
#align mul_add_mul_le_mul_add_mul mul_add_mul_le_mul_add_mul

/-- Binary **rearrangement inequality**. -/
lemma mul_add_mul_le_mul_add_mul' (hba : b ≤ a) (hdc : d ≤ c) : a * d + b * c ≤ a * c + b * d := by
  rw [add_comm (a * d), add_comm (a * c)]; exact mul_add_mul_le_mul_add_mul hba hdc
#align mul_add_mul_le_mul_add_mul' mul_add_mul_le_mul_add_mul'

/-- Binary strict **rearrangement inequality**. -/
lemma mul_add_mul_lt_mul_add_mul (hab : a < b) (hcd : c < d) : a * d + b * c < a * c + b * d := by
  obtain ⟨b, rfl⟩ := exists_add_of_le hab.le
  obtain ⟨d, rfl⟩ := exists_add_of_le hcd.le
  rw [mul_add, add_right_comm, mul_add, ← add_assoc]
  exact add_lt_add_left (mul_lt_mul_of_pos_right hab <| (lt_add_iff_pos_right _).1 hcd) _
#align mul_add_mul_lt_mul_add_mul mul_add_mul_lt_mul_add_mul

/-- Binary **rearrangement inequality**. -/
lemma mul_add_mul_lt_mul_add_mul' (hba : b < a) (hdc : d < c) : a * d + b * c < a * c + b * d := by
  rw [add_comm (a * d), add_comm (a * c)]
  exact mul_add_mul_lt_mul_add_mul hba hdc
#align mul_add_mul_lt_mul_add_mul' mul_add_mul_lt_mul_add_mul'

end StrictOrderedSemiring

section StrictOrderedCommSemiring
variable [StrictOrderedCommSemiring α]

-- See note [reducible non-instances]
/-- A choice-free version of `StrictOrderedCommSemiring.toOrderedCommSemiring'` to avoid using
choice in basic `Nat` lemmas. -/
abbrev StrictOrderedCommSemiring.toOrderedCommSemiring' [@DecidableRel α (· ≤ ·)] :
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
    mul_lt_mul_of_pos_right := fun a b c h hc => by
      simpa only [sub_mul, sub_pos] using StrictOrderedRing.mul_pos _ _ (sub_pos.2 h) hc }
#align strict_ordered_ring.to_strict_ordered_semiring StrictOrderedRing.toStrictOrderedSemiring

-- See note [reducible non-instances]
/-- A choice-free version of `StrictOrderedRing.toOrderedRing` to avoid using choice in basic
`Int` lemmas. -/
abbrev StrictOrderedRing.toOrderedRing' [@DecidableRel α (· ≤ ·)] : OrderedRing α :=
  { ‹StrictOrderedRing α›, (Ring.toSemiring : Semiring α) with
    mul_nonneg := fun a b ha hb => by
      obtain ha | ha := Decidable.eq_or_lt_of_le ha
      · rw [← ha, zero_mul]
      obtain hb | hb := Decidable.eq_or_lt_of_le hb
      · rw [← hb, mul_zero]
      · exact (StrictOrderedRing.mul_pos _ _ ha hb).le }
#align strict_ordered_ring.to_ordered_ring' StrictOrderedRing.toOrderedRing'

-- see Note [lower instance priority]
instance (priority := 100) StrictOrderedRing.toOrderedRing : OrderedRing α where
  __ := ‹StrictOrderedRing α›
  mul_nonneg := fun _ _ => mul_nonneg
#align strict_ordered_ring.to_ordered_ring StrictOrderedRing.toOrderedRing

end StrictOrderedRing

section StrictOrderedCommRing

variable [StrictOrderedCommRing α]

-- See note [reducible non-instances]
/-- A choice-free version of `StrictOrderedCommRing.toOrderedCommRing` to avoid using
choice in basic `Int` lemmas. -/
abbrev StrictOrderedCommRing.toOrderedCommRing' [@DecidableRel α (· ≤ ·)] : OrderedCommRing α :=
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

theorem nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg (hab : 0 ≤ a * b) :
    0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  refine Decidable.or_iff_not_and_not.2 ?_
  simp only [not_and, not_le]; intro ab nab; apply not_lt_of_le hab _
  rcases lt_trichotomy 0 a with (ha | rfl | ha)
  · exact mul_neg_of_pos_of_neg ha (ab ha.le)
  · exact ((ab le_rfl).asymm (nab le_rfl)).elim
  · exact mul_neg_of_neg_of_pos ha (nab ha.le)
#align nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nnonneg nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg

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
theorem mul_nonneg_iff_of_pos_left (h : 0 < c) : 0 ≤ c * b ↔ 0 ≤ b := by
  convert mul_le_mul_left h
  simp
#align zero_le_mul_left mul_nonneg_iff_of_pos_left

@[simp]
theorem mul_nonneg_iff_of_pos_right (h : 0 < c) : 0 ≤ b * c ↔ 0 ≤ b := by
  simpa using (mul_le_mul_right h : 0 * c ≤ b * c ↔ 0 ≤ b)
#align zero_le_mul_right mul_nonneg_iff_of_pos_right

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
#align bit0_le_bit0 bit0_le_bit0

@[simp]
theorem bit0_lt_bit0 : bit0 a < bit0 b ↔ a < b := by
  rw [bit0, bit0, ← two_mul, ← two_mul, mul_lt_mul_left (zero_lt_two : 0 < (2 : α))]
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
  rw [bit1, le_add_iff_nonneg_left, bit0, ← two_mul, mul_nonneg_iff_of_pos_left (zero_lt_two' α)]
#align one_le_bit1 one_le_bit1

@[simp]
theorem one_lt_bit1 : (1 : α) < bit1 a ↔ 0 < a := by
  rw [bit1, lt_add_iff_pos_left, bit0, ← two_mul, mul_pos_iff_of_pos_left (zero_lt_two' α)]
#align one_lt_bit1 one_lt_bit1

@[simp]
theorem zero_le_bit0 : (0 : α) ≤ bit0 a ↔ 0 ≤ a := by
  rw [bit0, ← two_mul, mul_nonneg_iff_of_pos_left (zero_lt_two : 0 < (2 : α))]
#align zero_le_bit0 zero_le_bit0

@[simp]
theorem zero_lt_bit0 : (0 : α) < bit0 a ↔ 0 < a := by
  rw [bit0, ← two_mul, mul_pos_iff_of_pos_left (zero_lt_two : 0 < (2 : α))]
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
    (mul_pos_iff_of_pos_left h).mp <| u.mul_inv.symm ▸ zero_lt_one
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

lemma sign_cases_of_C_mul_pow_nonneg  (h : ∀ n, 0 ≤ a * b ^ n) : a = 0 ∨ 0 < a ∧ 0 ≤ b := by
  have : 0 ≤ a := by simpa only [pow_zero, mul_one] using h 0
  refine this.eq_or_gt.imp_right fun ha ↦ ⟨ha, nonneg_of_mul_nonneg_right ?_ ha⟩
  simpa only [pow_one] using h 1
set_option linter.uppercaseLean3 false in
#align sign_cases_of_C_mul_pow_nonneg sign_cases_of_C_mul_pow_nonneg

variable [ExistsAddOfLE α]

-- See note [lower instance priority]
instance (priority := 100) LinearOrderedSemiring.noZeroDivisors : NoZeroDivisors α where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} hab := by
    contrapose! hab
    obtain ha | ha := hab.1.lt_or_lt <;> obtain hb | hb := hab.2.lt_or_lt
    exacts [(mul_pos_of_neg_of_neg ha hb).ne', (mul_neg_of_neg_of_pos ha hb).ne,
      (mul_neg_of_pos_of_neg ha hb).ne, (mul_pos ha hb).ne']
#align linear_ordered_ring.no_zero_divisors LinearOrderedSemiring.noZeroDivisors

-- Note that we can't use `NoZeroDivisors.to_isDomain` since we are merely in a semiring.
-- See note [lower instance priority]
instance (priority := 100) LinearOrderedRing.isDomain : IsDomain α where
  mul_left_cancel_of_ne_zero {a b c} ha h := by
    obtain ha | ha := ha.lt_or_lt
    exacts [(strictAnti_mul_left ha).injective h, (strictMono_mul_left_of_pos ha).injective h]
  mul_right_cancel_of_ne_zero {b a c} ha h := by
    obtain ha | ha := ha.lt_or_lt
    exacts [(strictAnti_mul_right ha).injective h, (strictMono_mul_right_of_pos ha).injective h]
#align linear_ordered_ring.is_domain LinearOrderedRing.isDomain

theorem mul_pos_iff : 0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 :=
  ⟨pos_and_pos_or_neg_and_neg_of_mul_pos, fun h =>
    h.elim (and_imp.2 mul_pos) (and_imp.2 mul_pos_of_neg_of_neg)⟩
#align mul_pos_iff mul_pos_iff

theorem mul_nonneg_iff : 0 ≤ a * b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 :=
  ⟨nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg, fun h =>
    h.elim (and_imp.2 mul_nonneg) (and_imp.2 mul_nonneg_of_nonpos_of_nonpos)⟩
#align mul_nonneg_iff mul_nonneg_iff

/-- Out of three elements of a `LinearOrderedRing`, two must have the same sign. -/
theorem mul_nonneg_of_three (a b c : α) : 0 ≤ a * b ∨ 0 ≤ b * c ∨ 0 ≤ c * a := by
  iterate 3 rw [mul_nonneg_iff]
  have or_a := le_total 0 a
  have or_b := le_total 0 b
  have or_c := le_total 0 c
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

lemma mul_nonneg_iff_pos_imp_nonneg : 0 ≤ a * b ↔ (0 < a → 0 ≤ b) ∧ (0 < b → 0 ≤ a) := by
  refine mul_nonneg_iff.trans ?_
  simp_rw [← not_le, ← or_iff_not_imp_left]
  have := le_total a 0
  have := le_total b 0
  tauto

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
  (antitone_mul_left hc).reflect_lt h
#align lt_of_mul_lt_mul_of_nonpos_left lt_of_mul_lt_mul_of_nonpos_left

theorem lt_of_mul_lt_mul_of_nonpos_right (h : a * c < b * c) (hc : c ≤ 0) : b < a :=
  (antitone_mul_right hc).reflect_lt h
#align lt_of_mul_lt_mul_of_nonpos_right lt_of_mul_lt_mul_of_nonpos_right

theorem cmp_mul_neg_left {a : α} (ha : a < 0) (b c : α) : cmp (a * b) (a * c) = cmp c b :=
  (strictAnti_mul_left ha).cmp_map_eq b c
#align cmp_mul_neg_left cmp_mul_neg_left

theorem cmp_mul_neg_right {a : α} (ha : a < 0) (b c : α) : cmp (b * a) (c * a) = cmp c b :=
  (strictAnti_mul_right ha).cmp_map_eq b c
#align cmp_mul_neg_right cmp_mul_neg_right

@[simp]
theorem mul_self_pos {a : α} : 0 < a * a ↔ a ≠ 0 := by
  constructor
  · rintro h rfl
    rw [mul_zero] at h
    exact h.false
  · intro h
    cases' h.lt_or_lt with h h
    exacts [mul_pos_of_neg_of_neg h h, mul_pos h h]
#align mul_self_pos mul_self_pos

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

lemma sq_nonneg (a : α) : 0 ≤ a ^ 2 := by
  obtain ha | ha := le_total 0 a
  · exact pow_nonneg ha _
  obtain ⟨b, hab⟩ := exists_add_of_le ha
  calc
    0 ≤ b ^ 2 := pow_nonneg (not_lt.1 fun hb ↦ hab.not_gt <| add_neg_of_nonpos_of_neg ha hb) _
    _ = a ^ 2 := add_left_injective (a * b) ?_
  calc
    b ^ 2 + a * b = (a + b) * b := by rw [add_comm, sq, add_mul]
    _ = a * (a + b) := by simp [← hab]
    _ = a ^ 2 + a * b := by rw [sq, mul_add]
#align sq_nonneg sq_nonneg

alias pow_two_nonneg := sq_nonneg
#align pow_two_nonneg pow_two_nonneg

lemma mul_self_nonneg (a : α) : 0 ≤ a * a := by simpa only [sq] using sq_nonneg a

/-- The sum of two squares is zero iff both elements are zero. -/
lemma mul_self_add_mul_self_eq_zero : a * a + b * b = 0 ↔ a = 0 ∧ b = 0 := by
  rw [add_eq_zero_iff', mul_self_eq_zero (M₀ := α), mul_self_eq_zero (M₀ := α)] <;>
    apply mul_self_nonneg
#align mul_self_add_mul_self_eq_zero mul_self_add_mul_self_eq_zero

lemma eq_zero_of_mul_self_add_mul_self_eq_zero (h : a * a + b * b = 0) : a = 0 :=
  (mul_self_add_mul_self_eq_zero.mp h).left
#align eq_zero_of_mul_self_add_mul_self_eq_zero eq_zero_of_mul_self_add_mul_self_eq_zero

end LinearOrderedSemiring

section LinearOrderedCommSemiring
variable [LinearOrderedCommSemiring α] {a b c d : α}

-- See note [lower instance priority]
instance (priority := 100) LinearOrderedCommSemiring.toLinearOrderedCancelAddCommMonoid :
    LinearOrderedCancelAddCommMonoid α where __ := ‹LinearOrderedCommSemiring α›
#align linear_ordered_comm_semiring.to_linear_ordered_cancel_add_comm_monoid LinearOrderedCommSemiring.toLinearOrderedCancelAddCommMonoid

lemma max_mul_mul_le_max_mul_max (b c : α) (ha : 0 ≤ a) (hd : 0 ≤ d) :
    max (a * b) (d * c) ≤ max a c * max d b :=
  have ba : b * a ≤ max d b * max c a :=
    mul_le_mul (le_max_right d b) (le_max_right c a) ha (le_trans hd (le_max_left d b))
  have cd : c * d ≤ max a c * max b d :=
    mul_le_mul (le_max_right a c) (le_max_right b d) hd (le_trans ha (le_max_left a c))
  max_le (by simpa [mul_comm, max_comm] using ba) (by simpa [mul_comm, max_comm] using cd)
#align max_mul_mul_le_max_mul_max max_mul_mul_le_max_mul_max

variable [ExistsAddOfLE α]

/-- Binary **arithmetic mean-geometric mean inequality** (aka AM-GM inequality) for linearly ordered
commutative semirings. -/
lemma two_mul_le_add_sq (a b : α) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  simpa [fn_min_add_fn_max (fun x ↦ x * x), sq, two_mul, add_mul]
    using mul_add_mul_le_mul_add_mul (@min_le_max _ _ a b) (@min_le_max _ _ a b)
#align two_mul_le_add_sq two_mul_le_add_sq

alias two_mul_le_add_pow_two := two_mul_le_add_sq
#align two_mul_le_add_pow_two two_mul_le_add_pow_two

end LinearOrderedCommSemiring

section LinearOrderedRing
variable [LinearOrderedRing α] {a b c : α}

attribute [local instance] LinearOrderedRing.decidableLE LinearOrderedRing.decidableLT

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedRing.toLinearOrderedSemiring : LinearOrderedSemiring α :=
  { ‹LinearOrderedRing α›, StrictOrderedRing.toStrictOrderedSemiring with }
#align linear_ordered_ring.to_linear_ordered_semiring LinearOrderedRing.toLinearOrderedSemiring

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedRing.toLinearOrderedAddCommGroup :
    LinearOrderedAddCommGroup α where __ := ‹LinearOrderedRing α›
#align linear_ordered_ring.to_linear_ordered_add_comm_group LinearOrderedRing.toLinearOrderedAddCommGroup

-- TODO: Can the following five lemmas be generalised to
-- `[LinearOrderedSemiring α] [ExistsAddOfLE α]`?

lemma mul_neg_iff : a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b := by
  rw [← neg_pos, neg_mul_eq_mul_neg, mul_pos_iff (α := α), neg_pos, neg_lt_zero]
#align mul_neg_iff mul_neg_iff

lemma mul_nonpos_iff : a * b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b := by
  rw [← neg_nonneg, neg_mul_eq_mul_neg, mul_nonneg_iff (α := α), neg_nonneg, neg_nonpos]
#align mul_nonpos_iff mul_nonpos_iff

lemma mul_nonneg_iff_neg_imp_nonpos : 0 ≤ a * b ↔ (a < 0 → b ≤ 0) ∧ (b < 0 → a ≤ 0) := by
  rw [← neg_mul_neg, mul_nonneg_iff_pos_imp_nonneg (α := α)]; simp only [neg_pos, neg_nonneg]

lemma mul_nonpos_iff_pos_imp_nonpos : a * b ≤ 0 ↔ (0 < a → b ≤ 0) ∧ (b < 0 → 0 ≤ a) := by
  rw [← neg_nonneg, ← mul_neg, mul_nonneg_iff_pos_imp_nonneg (α := α)]
  simp only [neg_pos, neg_nonneg]

lemma mul_nonpos_iff_neg_imp_nonneg : a * b ≤ 0 ↔ (a < 0 → 0 ≤ b) ∧ (0 < b → a ≤ 0) := by
  rw [← neg_nonneg, ← neg_mul, mul_nonneg_iff_pos_imp_nonneg (α := α)]
  simp only [neg_pos, neg_nonneg]

lemma neg_one_lt_zero : -1 < (0 : α) := neg_lt_zero.2 zero_lt_one
#align neg_one_lt_zero neg_one_lt_zero

lemma sub_one_lt (a : α) : a - 1 < a := sub_lt_iff_lt_add.2 <| lt_add_one a
#align sub_one_lt sub_one_lt

lemma mul_self_le_mul_self_of_le_of_neg_le (h₁ : a ≤ b) (h₂ : -a ≤ b) : a * a ≤ b * b :=
  (le_total 0 a).elim (mul_self_le_mul_self · h₁) fun h ↦
    (neg_mul_neg a a).symm.trans_le <|
      mul_le_mul h₂ h₂ (neg_nonneg.2 h) <| (neg_nonneg.2 h).trans h₂
#align mul_self_le_mul_self_of_le_of_neg_le mul_self_le_mul_self_of_le_of_neg_le

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

@[deprecated (since := "2023-12-23")] alias zero_le_mul_left := mul_nonneg_iff_of_pos_left
@[deprecated (since := "2023-12-23")] alias zero_le_mul_right := mul_nonneg_iff_of_pos_right
@[deprecated (since := "2023-12-23")] alias zero_lt_mul_left := mul_pos_iff_of_pos_left
@[deprecated (since := "2023-12-23")] alias zero_lt_mul_right := mul_pos_iff_of_pos_right

assert_not_exists MonoidHom
