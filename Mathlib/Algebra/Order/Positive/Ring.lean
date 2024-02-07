/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.InjSurj

#align_import algebra.order.positive.ring from "leanprover-community/mathlib"@"655994e298904d7e5bbd1e18c95defd7b543eb94"

/-!
# Algebraic structures on the set of positive numbers

In this file we define various instances (`AddSemigroup`, `OrderedCommMonoid` etc) on the
type `{x : R // 0 < x}`. In each case we try to require the weakest possible typeclass
assumptions on `R` but possibly, there is a room for improvements.
-/


open Function

namespace Positive

variable {M R K : Type*}

section AddBasic

variable [AddMonoid M] [Preorder M] [CovariantClass M M (· + ·) (· < ·)]

instance (priority := 10000) : Add { x : M // 0 < x } :=
  ⟨fun x y => ⟨x + y, add_pos x.2 y.2⟩⟩

@[simp, norm_cast]
theorem coe_add (x y : { x : M // 0 < x }) : ↑(x + y) = (x + y : M) :=
  rfl
#align positive.coe_add Positive.coe_add

instance (priority := 10000) addSemigroup : AddSemigroup { x : M // 0 < x } :=
  Subtype.coe_injective.addSemigroup _ coe_add
#align positive.subtype.add_semigroup Positive.addSemigroup

instance (priority := 10000) addCommSemigroup {M : Type*} [AddCommMonoid M] [Preorder M]
    [CovariantClass M M (· + ·) (· < ·)] : AddCommSemigroup { x : M // 0 < x } :=
  Subtype.coe_injective.addCommSemigroup _ coe_add
#align positive.subtype.add_comm_semigroup Positive.addCommSemigroup

instance (priority := 10000) addLeftCancelSemigroup {M : Type*} [AddLeftCancelMonoid M] [Preorder M]
    [CovariantClass M M (· + ·) (· < ·)] : AddLeftCancelSemigroup { x : M // 0 < x } :=
  Subtype.coe_injective.addLeftCancelSemigroup _ coe_add
#align positive.subtype.add_left_cancel_semigroup Positive.addLeftCancelSemigroup

instance (priority := 10000) addRightCancelSemigroup {M : Type*} [AddRightCancelMonoid M] [Preorder M]
    [CovariantClass M M (· + ·) (· < ·)] : AddRightCancelSemigroup { x : M // 0 < x } :=
  Subtype.coe_injective.addRightCancelSemigroup _ coe_add
#align positive.subtype.add_right_cancel_semigroup Positive.addRightCancelSemigroup

instance (priority := 10000) covariantClass_add_lt :
    CovariantClass { x : M // 0 < x } { x : M // 0 < x } (· + ·) (· < ·) :=
  ⟨fun _ y z hyz => Subtype.coe_lt_coe.1 <| add_lt_add_left (show (y : M) < z from hyz) _⟩
#align positive.covariant_class_add_lt Positive.covariantClass_add_lt

instance (priority := 10000) covariantClass_swap_add_lt [CovariantClass M M (swap (· + ·)) (· < ·)] :
    CovariantClass { x : M // 0 < x } { x : M // 0 < x } (swap (· + ·)) (· < ·) :=
  ⟨fun _ y z hyz => Subtype.coe_lt_coe.1 <| add_lt_add_right (show (y : M) < z from hyz) _⟩
#align positive.covariant_class_swap_add_lt Positive.covariantClass_swap_add_lt

instance (priority := 10000) contravariantClass_add_lt [ContravariantClass M M (· + ·) (· < ·)] :
    ContravariantClass { x : M // 0 < x } { x : M // 0 < x } (· + ·) (· < ·) :=
  ⟨fun _ _ _ h => Subtype.coe_lt_coe.1 <| lt_of_add_lt_add_left h⟩
#align positive.contravariant_class_add_lt Positive.contravariantClass_add_lt

instance (priority := 10000) contravariantClass_swap_add_lt [ContravariantClass M M (swap (· + ·)) (· < ·)] :
    ContravariantClass { x : M // 0 < x } { x : M // 0 < x } (swap (· + ·)) (· < ·) :=
  ⟨fun _ _ _ h => Subtype.coe_lt_coe.1 <| lt_of_add_lt_add_right h⟩
#align positive.contravariant_class_swap_add_lt Positive.contravariantClass_swap_add_lt

instance (priority := 10000) contravariantClass_add_le [ContravariantClass M M (· + ·) (· ≤ ·)] :
    ContravariantClass { x : M // 0 < x } { x : M // 0 < x } (· + ·) (· ≤ ·) :=
  ⟨fun _ _ _ h => Subtype.coe_le_coe.1 <| le_of_add_le_add_left h⟩
#align positive.contravariant_class_add_le Positive.contravariantClass_add_le

instance (priority := 10000) contravariantClass_swap_add_le [ContravariantClass M M (swap (· + ·)) (· ≤ ·)] :
    ContravariantClass { x : M // 0 < x } { x : M // 0 < x } (swap (· + ·)) (· ≤ ·) :=
  ⟨fun _ _ _ h => Subtype.coe_le_coe.1 <| le_of_add_le_add_right h⟩
#align positive.contravariant_class_swap_add_le Positive.contravariantClass_swap_add_le

end AddBasic

instance (priority := 10000) covariantClass_add_le [AddMonoid M] [PartialOrder M]
    [CovariantClass M M (· + ·) (· < ·)] :
    CovariantClass { x : M // 0 < x } { x : M // 0 < x } (· + ·) (· ≤ ·) :=
  ⟨@fun _ _ _ h₁ => StrictMono.monotone (fun _ _ h => add_lt_add_left h _) h₁⟩
#align positive.covariant_class_add_le Positive.covariantClass_add_le

section Mul

variable [StrictOrderedSemiring R]

instance (priority := 10000) : Mul { x : R // 0 < x } :=
  ⟨fun x y => ⟨x * y, mul_pos x.2 y.2⟩⟩

@[simp]
theorem val_mul (x y : { x : R // 0 < x }) : ↑(x * y) = (x * y : R) :=
  rfl
#align positive.coe_mul Positive.val_mul

instance (priority := 10000) : Pow { x : R // 0 < x } ℕ :=
  ⟨fun x n => ⟨(x : R) ^ n , pow_pos x.2 n⟩⟩

@[simp]
theorem val_pow (x : { x : R // 0 < x }) (n : ℕ) :
    ↑(x ^ n) = (x : R) ^ n :=
  rfl
#align positive.coe_pow Positive.val_pow

instance (priority := 10000) : Semigroup { x : R // 0 < x } :=
  Subtype.coe_injective.semigroup Subtype.val val_mul

instance (priority := 10000) : Distrib { x : R // 0 < x } :=
  Subtype.coe_injective.distrib _ coe_add val_mul

instance (priority := 10000) [Nontrivial R] : One { x : R // 0 < x } :=
  ⟨⟨1, one_pos⟩⟩

@[simp]
theorem val_one [Nontrivial R] : ((1 : { x : R // 0 < x }) : R) = 1 :=
  rfl
#align positive.coe_one Positive.val_one

instance (priority := 10000) [Nontrivial R] : Monoid { x : R // 0 < x } :=
  Subtype.coe_injective.monoid _ val_one val_mul val_pow

end Mul

section mul_comm

instance (priority := 10000) orderedCommMonoid [StrictOrderedCommSemiring R] [Nontrivial R] :
    OrderedCommMonoid { x : R // 0 < x } :=
  { Subtype.partialOrder _,
    Subtype.coe_injective.commMonoid (M₂ := R) (Subtype.val) val_one val_mul val_pow with
    mul_le_mul_left := fun _ _ hxy c =>
      Subtype.coe_le_coe.1 <| mul_le_mul_of_nonneg_left hxy c.2.le }
#align positive.subtype.ordered_comm_monoid Positive.orderedCommMonoid

/-- If `R` is a nontrivial linear ordered commutative semiring, then `{x : R // 0 < x}` is a linear
ordered cancellative commutative monoid. -/
instance (priority := 10000) linearOrderedCancelCommMonoid [LinearOrderedCommSemiring R] :
    LinearOrderedCancelCommMonoid { x : R // 0 < x } :=
  { Subtype.linearOrder _, Positive.orderedCommMonoid with
    le_of_mul_le_mul_left := fun a _ _ h => Subtype.coe_le_coe.1 <| (mul_le_mul_left a.2).1 h }
#align positive.subtype.linear_ordered_cancel_comm_monoid Positive.linearOrderedCancelCommMonoid

end mul_comm

end Positive
