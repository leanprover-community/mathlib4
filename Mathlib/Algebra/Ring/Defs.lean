/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Logic.Nontrivial

#align_import algebra.ring.defs from "leanprover-community/mathlib"@"76de8ae01554c3b37d66544866659ff174e66e1f"

/-!
# Semirings and rings

This file defines semirings, rings and domains. This is analogous to `Algebra.Group.Defs` and
`Algebra.Group.Basic`, the difference being that the former is about `+` and `*` separately, while
the present file is about their interaction.

## Main definitions

* `Distrib`: Typeclass for distributivity of multiplication over addition.
* `HasDistribNeg`: Typeclass for commutativity of negation and multiplication. This is useful when
  dealing with multiplicative submonoids which are closed under negation without being closed under
  addition, for example `Units`.
* `(NonUnital)(NonAssoc)(Semi)Ring`: Typeclasses for possibly non-unital or non-associative
  rings and semirings. Some combinations are not defined yet because they haven't found use.

## Tags

`Semiring`, `CommSemiring`, `Ring`, `CommRing`, domain, `IsDomain`, nonzero, units
-/


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

open Function

/-!
### `Distrib` class
-/


/-- A typeclass stating that multiplication is left and right distributive
over addition. -/
class Distrib (R : Type*) extends Mul R, Add R where
  /-- Multiplication is left distributive over addition -/
  protected left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- Multiplication is right distributive over addition -/
  protected right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c
#align distrib Distrib

/-- A typeclass stating that multiplication is left distributive over addition. -/
class LeftDistribClass (R : Type*) [Mul R] [Add R] : Prop where
  /-- Multiplication is left distributive over addition -/
  protected left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
#align left_distrib_class LeftDistribClass

/-- A typeclass stating that multiplication is right distributive over addition. -/
class RightDistribClass (R : Type*) [Mul R] [Add R] : Prop where
  /-- Multiplication is right distributive over addition -/
  protected right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c
#align right_distrib_class RightDistribClass

-- see Note [lower instance priority]
instance (priority := 100) Distrib.leftDistribClass (R : Type*) [Distrib R] : LeftDistribClass R :=
  ⟨Distrib.left_distrib⟩
#align distrib.left_distrib_class Distrib.leftDistribClass

-- see Note [lower instance priority]
instance (priority := 100) Distrib.rightDistribClass (R : Type*) [Distrib R] :
    RightDistribClass R :=
  ⟨Distrib.right_distrib⟩
#align distrib.right_distrib_class Distrib.rightDistribClass

theorem left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c : R) :
    a * (b + c) = a * b + a * c :=
  LeftDistribClass.left_distrib a b c
#align left_distrib left_distrib

alias mul_add := left_distrib
#align mul_add mul_add

theorem right_distrib [Mul R] [Add R] [RightDistribClass R] (a b c : R) :
    (a + b) * c = a * c + b * c :=
  RightDistribClass.right_distrib a b c
#align right_distrib right_distrib

alias add_mul := right_distrib
#align add_mul add_mul

theorem distrib_three_right [Mul R] [Add R] [RightDistribClass R] (a b c d : R) :
    (a + b + c) * d = a * d + b * d + c * d := by simp [right_distrib]
                                                  -- 🎉 no goals
#align distrib_three_right distrib_three_right

/-!
### Classes of semirings and rings

We make sure that the canonical path from `NonAssocSemiring` to `Ring` passes through `Semiring`,
as this is a path which is followed all the time in linear algebra where the defining semilinear map
`σ : R →+* S` depends on the `NonAssocSemiring` structure of `R` and `S` while the module
definition depends on the `Semiring` structure.

It is not currently possible to adjust priorities by hand (see lean4#2115). Instead, the last
declared instance is used, so we make sure that `Semiring` is declared after `NonAssocRing`, so
that `Semiring -> NonAssocSemiring` is tried before `NonAssocRing -> NonAssocSemiring`.
TODO: clean this once lean4#2115 is fixed
-/

/-- A not-necessarily-unital, not-necessarily-associative semiring. -/
class NonUnitalNonAssocSemiring (α : Type u) extends AddCommMonoid α, Distrib α, MulZeroClass α
#align non_unital_non_assoc_semiring NonUnitalNonAssocSemiring

/-- An associative but not-necessarily unital semiring. -/
class NonUnitalSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, SemigroupWithZero α
#align non_unital_semiring NonUnitalSemiring

/-- A unital but not-necessarily-associative semiring. -/
class NonAssocSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, MulZeroOneClass α,
    AddCommMonoidWithOne α
#align non_assoc_semiring NonAssocSemiring

/-- A not-necessarily-unital, not-necessarily-associative ring. -/
class NonUnitalNonAssocRing (α : Type u) extends AddCommGroup α, NonUnitalNonAssocSemiring α
#align non_unital_non_assoc_ring NonUnitalNonAssocRing

-- We defer the instance `NonUnitalNonAssocRing.toHasDistribNeg` to `Algebra.Ring.Basic`
-- as it relies on the lemma `eq_neg_of_add_eq_zero_left`.
/-- An associative but not-necessarily unital ring. -/
class NonUnitalRing (α : Type*) extends NonUnitalNonAssocRing α, NonUnitalSemiring α
#align non_unital_ring NonUnitalRing

/-- A unital but not-necessarily-associative ring. -/
class NonAssocRing (α : Type*) extends NonUnitalNonAssocRing α, NonAssocSemiring α,
    AddCommGroupWithOne α
#align non_assoc_ring NonAssocRing

class Semiring (α : Type u) extends NonUnitalSemiring α, NonAssocSemiring α, MonoidWithZero α
#align semiring Semiring

class Ring (R : Type u) extends Semiring R, AddCommGroup R, AddGroupWithOne R
#align ring Ring

/-!
### Semirings
-/

section DistribMulOneClass

variable [Add α] [MulOneClass α]

theorem add_one_mul [RightDistribClass α] (a b : α) : (a + 1) * b = a * b + b := by
  rw [add_mul, one_mul]
  -- 🎉 no goals
#align add_one_mul add_one_mul

theorem mul_add_one [LeftDistribClass α] (a b : α) : a * (b + 1) = a * b + a := by
  rw [mul_add, mul_one]
  -- 🎉 no goals
#align mul_add_one mul_add_one

theorem one_add_mul [RightDistribClass α] (a b : α) : (1 + a) * b = b + a * b := by
  rw [add_mul, one_mul]
  -- 🎉 no goals
#align one_add_mul one_add_mul

theorem mul_one_add [LeftDistribClass α] (a b : α) : a * (1 + b) = a + a * b := by
  rw [mul_add, mul_one]
  -- 🎉 no goals
#align mul_one_add mul_one_add

end DistribMulOneClass

section NonAssocSemiring

variable [NonAssocSemiring α]

-- Porting note: was [has_add α] [mul_one_class α] [right_distrib_class α]
theorem two_mul (n : α) : 2 * n = n + n :=
  (congrArg₂ _ one_add_one_eq_two.symm rfl).trans <| (right_distrib 1 1 n).trans (by rw [one_mul])
                                                                                     -- 🎉 no goals
#align two_mul two_mul

-- Porting note: was [has_add α] [mul_one_class α] [right_distrib_class α]
set_option linter.deprecated false in
theorem bit0_eq_two_mul (n : α) : bit0 n = 2 * n :=
  (two_mul _).symm
#align bit0_eq_two_mul bit0_eq_two_mul

-- Porting note: was [has_add α] [mul_one_class α] [left_distrib_class α]
theorem mul_two (n : α) : n * 2 = n + n :=
  (congrArg₂ _ rfl one_add_one_eq_two.symm).trans <| (left_distrib n 1 1).trans (by rw [mul_one])
                                                                                    -- 🎉 no goals
#align mul_two mul_two

end NonAssocSemiring

@[to_additive]
theorem mul_ite {α} [Mul α] (P : Prop) [Decidable P] (a b c : α) :
    (a * if P then b else c) = if P then a * b else a * c := by split_ifs <;> rfl
                                                                -- ⊢ a * b = a * b
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
#align mul_ite mul_ite
#align add_ite add_ite

@[to_additive]
theorem ite_mul {α} [Mul α] (P : Prop) [Decidable P] (a b c : α) :
    (if P then a else b) * c = if P then a * c else b * c := by split_ifs <;> rfl
                                                                -- ⊢ a * c = a * c
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
#align ite_mul ite_mul
#align ite_add ite_add

-- We make `mul_ite` and `ite_mul` simp lemmas,
-- but not `add_ite` or `ite_add`.
-- The problem we're trying to avoid is dealing with
-- summations of the form `∑ x in s, (f x + ite P 1 0)`,
-- in which `add_ite` followed by `sum_ite` would needlessly slice up
-- the `f x` terms according to whether `P` holds at `x`.
-- There doesn't appear to be a corresponding difficulty so far with
-- `mul_ite` and `ite_mul`.
attribute [simp] mul_ite ite_mul

-- Porting note: no @[simp] because simp proves it
theorem mul_boole {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a : α) :
    (a * if P then 1 else 0) = if P then a else 0 := by simp
                                                        -- 🎉 no goals
#align mul_boole mul_boole

-- Porting note: no @[simp] because simp proves it
theorem boole_mul {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a : α) :
    (if P then 1 else 0) * a = if P then a else 0 := by simp
                                                        -- 🎉 no goals
#align boole_mul boole_mul

theorem ite_mul_zero_left {α : Type*} [MulZeroClass α] (P : Prop) [Decidable P] (a b : α) :
    ite P (a * b) 0 = ite P a 0 * b := by by_cases h : P <;> simp [h]
                                          -- ⊢ (if P then a * b else 0) = (if P then a else 0) * b
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
#align ite_mul_zero_left ite_mul_zero_left

theorem ite_mul_zero_right {α : Type*} [MulZeroClass α] (P : Prop) [Decidable P] (a b : α) :
    ite P (a * b) 0 = a * ite P b 0 := by by_cases h : P <;> simp [h]
                                          -- ⊢ (if P then a * b else 0) = a * if P then b else 0
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
#align ite_mul_zero_right ite_mul_zero_right

theorem ite_and_mul_zero {α : Type*} [MulZeroClass α] (P Q : Prop) [Decidable P] [Decidable Q]
    (a b : α) : ite (P ∧ Q) (a * b) 0 = ite P a 0 * ite Q b 0 := by
  simp only [← ite_and, ite_mul, mul_ite, mul_zero, zero_mul, and_comm]
  -- 🎉 no goals
#align ite_and_mul_zero ite_and_mul_zero

/-- A non-unital commutative semiring is a `NonUnitalSemiring` with commutative multiplication.
In other words, it is a type with the following structures: additive commutative monoid
(`AddCommMonoid`), commutative semigroup (`CommSemigroup`), distributive laws (`Distrib`), and
multiplication by zero law (`MulZeroClass`). -/
class NonUnitalCommSemiring (α : Type u) extends NonUnitalSemiring α, CommSemigroup α
#align non_unital_comm_semiring NonUnitalCommSemiring

class CommSemiring (R : Type u) extends Semiring R, CommMonoid R
#align comm_semiring CommSemiring

-- see Note [lower instance priority]
instance (priority := 100) CommSemiring.toNonUnitalCommSemiring [CommSemiring α] :
    NonUnitalCommSemiring α :=
  { inferInstanceAs (CommMonoid α), inferInstanceAs (CommSemiring α) with }
#align comm_semiring.to_non_unital_comm_semiring CommSemiring.toNonUnitalCommSemiring

-- see Note [lower instance priority]
instance (priority := 100) CommSemiring.toCommMonoidWithZero [CommSemiring α] :
    CommMonoidWithZero α :=
  { inferInstanceAs (CommMonoid α), inferInstanceAs (CommSemiring α) with }
#align comm_semiring.to_comm_monoid_with_zero CommSemiring.toCommMonoidWithZero

section CommSemiring

variable [CommSemiring α] {a b c : α}

theorem add_mul_self_eq (a b : α) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
  simp only [two_mul, add_mul, mul_add, add_assoc, mul_comm b]
  -- 🎉 no goals
#align add_mul_self_eq add_mul_self_eq

end CommSemiring

section HasDistribNeg

/-- Typeclass for a negation operator that distributes across multiplication.

This is useful for dealing with submonoids of a ring that contain `-1` without having to duplicate
lemmas. -/
class HasDistribNeg (α : Type*) [Mul α] extends InvolutiveNeg α where
  /-- Negation is left distributive over multiplication -/
  neg_mul : ∀ x y : α, -x * y = -(x * y)
  /-- Negation is right distributive over multiplication -/
  mul_neg : ∀ x y : α, x * -y = -(x * y)
#align has_distrib_neg HasDistribNeg

section Mul

variable [Mul α] [HasDistribNeg α]

@[simp]
theorem neg_mul (a b : α) : -a * b = -(a * b) :=
  HasDistribNeg.neg_mul _ _
#align neg_mul neg_mul

@[simp]
theorem mul_neg (a b : α) : a * -b = -(a * b) :=
  HasDistribNeg.mul_neg _ _
#align mul_neg mul_neg

theorem neg_mul_neg (a b : α) : -a * -b = a * b := by simp
                                                      -- 🎉 no goals
#align neg_mul_neg neg_mul_neg

theorem neg_mul_eq_neg_mul (a b : α) : -(a * b) = -a * b :=
  (neg_mul _ _).symm
#align neg_mul_eq_neg_mul neg_mul_eq_neg_mul

theorem neg_mul_eq_mul_neg (a b : α) : -(a * b) = a * -b :=
  (mul_neg _ _).symm
#align neg_mul_eq_mul_neg neg_mul_eq_mul_neg

theorem neg_mul_comm (a b : α) : -a * b = a * -b := by simp
                                                       -- 🎉 no goals
#align neg_mul_comm neg_mul_comm

end Mul

section MulOneClass

variable [MulOneClass α] [HasDistribNeg α]

theorem neg_eq_neg_one_mul (a : α) : -a = -1 * a := by simp
                                                       -- 🎉 no goals
#align neg_eq_neg_one_mul neg_eq_neg_one_mul

/-- An element of a ring multiplied by the additive inverse of one is the element's additive
  inverse. -/
theorem mul_neg_one (a : α) : a * -1 = -a := by simp
                                                -- 🎉 no goals
#align mul_neg_one mul_neg_one

/-- The additive inverse of one multiplied by an element of a ring is the element's additive
  inverse. -/
theorem neg_one_mul (a : α) : -1 * a = -a := by simp
                                                -- 🎉 no goals
#align neg_one_mul neg_one_mul

end MulOneClass

section MulZeroClass

variable [MulZeroClass α] [HasDistribNeg α]

instance (priority := 100) MulZeroClass.negZeroClass : NegZeroClass α where
  __ := inferInstanceAs (Zero α); __ := inferInstanceAs (InvolutiveNeg α)
  neg_zero := by rw [← zero_mul (0 : α), ← neg_mul, mul_zero, mul_zero]
                 -- 🎉 no goals
#align mul_zero_class.neg_zero_class MulZeroClass.negZeroClass

end MulZeroClass

end HasDistribNeg

/-!
### Rings
-/

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α]

instance (priority := 100) NonUnitalNonAssocRing.toHasDistribNeg : HasDistribNeg α where
  neg := Neg.neg
  neg_neg := neg_neg
  neg_mul a b := eq_neg_of_add_eq_zero_left <| by rw [← right_distrib, add_left_neg, zero_mul]
                                                  -- 🎉 no goals
  mul_neg a b := eq_neg_of_add_eq_zero_left <| by rw [← left_distrib, add_left_neg, mul_zero]
                                                  -- 🎉 no goals
#align non_unital_non_assoc_ring.to_has_distrib_neg NonUnitalNonAssocRing.toHasDistribNeg

theorem mul_sub_left_distrib (a b c : α) : a * (b - c) = a * b - a * c := by
  simpa only [sub_eq_add_neg, neg_mul_eq_mul_neg] using mul_add a b (-c)
  -- 🎉 no goals
#align mul_sub_left_distrib mul_sub_left_distrib

alias mul_sub := mul_sub_left_distrib
#align mul_sub mul_sub

theorem mul_sub_right_distrib (a b c : α) : (a - b) * c = a * c - b * c := by
  simpa only [sub_eq_add_neg, neg_mul_eq_neg_mul] using add_mul a (-b) c
  -- 🎉 no goals
#align mul_sub_right_distrib mul_sub_right_distrib

alias sub_mul := mul_sub_right_distrib
#align sub_mul sub_mul

variable {a b c d e : α}

/-- An iff statement following from right distributivity in rings and the definition
  of subtraction. -/
theorem mul_add_eq_mul_add_iff_sub_mul_add_eq : a * e + c = b * e + d ↔ (a - b) * e + c = d :=
  calc
    a * e + c = b * e + d ↔ a * e + c = d + b * e := by simp [add_comm]
                                                        -- 🎉 no goals
    _ ↔ a * e + c - b * e = d :=
      Iff.intro
        (fun h => by
          rw [h]
          -- ⊢ d + b * e - b * e = d
          simp)
          -- 🎉 no goals
        fun h => by
        rw [← h]
        -- ⊢ a * e + c = a * e + c - b * e + b * e
        simp
        -- 🎉 no goals
    _ ↔ (a - b) * e + c = d := by simp [sub_mul, sub_add_eq_add_sub]
                                  -- 🎉 no goals
#align mul_add_eq_mul_add_iff_sub_mul_add_eq mul_add_eq_mul_add_iff_sub_mul_add_eq

/-- A simplification of one side of an equation exploiting right distributivity in rings
  and the definition of subtraction. -/
theorem sub_mul_add_eq_of_mul_add_eq_mul_add (h : a * e + c = b * e + d) : (a - b) * e + c = d :=
  calc
    (a - b) * e + c = a * e + c - b * e := by simp [sub_mul, sub_add_eq_add_sub]
                                              -- 🎉 no goals
    _ = d := by rw [h]; simp [@add_sub_cancel α]
                -- ⊢ b * e + d - b * e = d
                        -- 🎉 no goals
#align sub_mul_add_eq_of_mul_add_eq_mul_add sub_mul_add_eq_of_mul_add_eq_mul_add

end NonUnitalNonAssocRing

section NonAssocRing

variable [NonAssocRing α]

theorem sub_one_mul (a b : α) : (a - 1) * b = a * b - b := by rw [sub_mul, one_mul]
                                                              -- 🎉 no goals
#align sub_one_mul sub_one_mul

theorem mul_sub_one (a b : α) : a * (b - 1) = a * b - a := by rw [mul_sub, mul_one]
                                                              -- 🎉 no goals
#align mul_sub_one mul_sub_one

theorem one_sub_mul (a b : α) : (1 - a) * b = b - a * b := by rw [sub_mul, one_mul]
                                                              -- 🎉 no goals
#align one_sub_mul one_sub_mul

theorem mul_one_sub (a b : α) : a * (1 - b) = a - a * b := by rw [mul_sub, mul_one]
                                                              -- 🎉 no goals
#align mul_one_sub mul_one_sub

end NonAssocRing

section Ring

variable [Ring α] {a b c d e : α}

-- A (unital, associative) ring is a not-necessarily-unital ring
-- see Note [lower instance priority]
instance (priority := 100) Ring.toNonUnitalRing : NonUnitalRing α where
  __ := ‹Ring α›
  zero_mul := fun a => add_left_cancel (a := 0 * a) <| by rw [← add_mul, zero_add, add_zero]
                                                          -- 🎉 no goals
  mul_zero := fun a => add_left_cancel (a := a * 0) <| by rw [← mul_add, add_zero, add_zero]
                                                          -- 🎉 no goals
#align ring.to_non_unital_ring Ring.toNonUnitalRing

-- A (unital, associative) ring is a not-necessarily-associative ring
-- see Note [lower instance priority]
instance (priority := 100) Ring.toNonAssocRing : NonAssocRing α where
  __ := ‹Ring α›
  zero_mul := fun a => add_left_cancel (a := 0 * a) <| by rw [← add_mul, zero_add, add_zero]
                                                          -- 🎉 no goals
  mul_zero := fun a => add_left_cancel (a := a * 0) <| by rw [← mul_add, add_zero, add_zero]
                                                          -- 🎉 no goals
#align ring.to_non_assoc_ring Ring.toNonAssocRing

/- The instance from `Ring` to `Semiring` happens often in linear algebra, for which all the basic
definitions are given in terms of semirings, but many applications use rings or fields. We increase
a little bit its priority above 100 to try it quickly, but remaining below the default 1000 so that
more specific instances are tried first. -/
instance (priority := 200) : Semiring α :=
  { ‹Ring α› with }
#align ring.to_semiring Ring.toSemiring

end Ring

/-- A non-unital commutative ring is a `NonUnitalRing` with commutative multiplication. -/
class NonUnitalCommRing (α : Type u) extends NonUnitalRing α, CommSemigroup α
#align non_unital_comm_ring NonUnitalCommRing

-- see Note [lower instance priority]
instance (priority := 100) NonUnitalCommRing.toNonUnitalCommSemiring [s : NonUnitalCommRing α] :
    NonUnitalCommSemiring α :=
  { s with }
#align non_unital_comm_ring.to_non_unital_comm_semiring NonUnitalCommRing.toNonUnitalCommSemiring

class CommRing (α : Type u) extends Ring α, CommMonoid α
#align comm_ring CommRing

instance (priority := 100) CommRing.toCommSemiring [s : CommRing α] : CommSemiring α :=
  { s with }
#align comm_ring.to_comm_semiring CommRing.toCommSemiring

-- see Note [lower instance priority]
instance (priority := 100) CommRing.toNonUnitalCommRing [s : CommRing α] : NonUnitalCommRing α :=
  { s with }
#align comm_ring.to_non_unital_comm_ring CommRing.toNonUnitalCommRing

-- see Note [lower instance priority]
instance (priority := 100) CommRing.toAddCommGroupWithOne [s : CommRing α] :
    AddCommGroupWithOne α :=
  { s with }

/-- A domain is a nontrivial semiring such multiplication by a non zero element is cancellative,
  on both sides. In other words, a nontrivial semiring `R` satisfying
  `∀ {a b c : R}, a ≠ 0 → a * b = a * c → b = c` and
  `∀ {a b c : R}, b ≠ 0 → a * b = c * b → a = c`.

  This is implemented as a mixin for `Semiring α`.
  To obtain an integral domain use `[CommRing α] [IsDomain α]`. -/
class IsDomain (α : Type u) [Semiring α] extends IsCancelMulZero α, Nontrivial α : Prop
#align is_domain IsDomain
