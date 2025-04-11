/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.Tactic.FastInstance

/-!
# Algebraic structures on the set of positive numbers

In this file we define various instances (`AddSemigroup`, `OrderedCommMonoid` etc) on the
type `{x : R // 0 < x}`. In each case we try to require the weakest possible typeclass
assumptions on `R` but possibly, there is a room for improvements.
-/


open Function

namespace Positive

variable {M R : Type*}

section AddBasic

variable [AddMonoid M] [Preorder M] [AddLeftStrictMono M]

instance : Add { x : M // 0 < x } :=
  ⟨fun x y => ⟨x + y, add_pos x.2 y.2⟩⟩

@[simp, norm_cast]
theorem coe_add (x y : { x : M // 0 < x }) : ↑(x + y) = (x + y : M) :=
  rfl

instance addSemigroup : AddSemigroup { x : M // 0 < x } := fast_instance%
  Subtype.coe_injective.addSemigroup _ coe_add

instance addCommSemigroup {M : Type*} [AddCommMonoid M] [Preorder M]
    [AddLeftStrictMono M] : AddCommSemigroup { x : M // 0 < x } := fast_instance%
  Subtype.coe_injective.addCommSemigroup _ coe_add

instance addLeftCancelSemigroup {M : Type*} [AddLeftCancelMonoid M] [Preorder M]
    [AddLeftStrictMono M] : AddLeftCancelSemigroup { x : M // 0 < x } := fast_instance%
  Subtype.coe_injective.addLeftCancelSemigroup _ coe_add

instance addRightCancelSemigroup {M : Type*} [AddRightCancelMonoid M] [Preorder M]
    [AddLeftStrictMono M] : AddRightCancelSemigroup { x : M // 0 < x } := fast_instance%
  Subtype.coe_injective.addRightCancelSemigroup _ coe_add

instance addLeftStrictMono : AddLeftStrictMono { x : M // 0 < x } :=
  ⟨fun _ y z hyz => Subtype.coe_lt_coe.1 <| add_lt_add_left (show (y : M) < z from hyz) _⟩

instance addRightStrictMono [AddRightStrictMono M] : AddRightStrictMono { x : M // 0 < x } :=
  ⟨fun _ y z hyz => Subtype.coe_lt_coe.1 <| add_lt_add_right (show (y : M) < z from hyz) _⟩

instance addLeftReflectLT [AddLeftReflectLT M] : AddLeftReflectLT { x : M // 0 < x } :=
  ⟨fun _ _ _ h => Subtype.coe_lt_coe.1 <| lt_of_add_lt_add_left h⟩

instance addRightReflectLT [AddRightReflectLT M] : AddRightReflectLT { x : M // 0 < x } :=
  ⟨fun _ _ _ h => Subtype.coe_lt_coe.1 <| lt_of_add_lt_add_right h⟩

instance addLeftReflectLE [AddLeftReflectLE M] : AddLeftReflectLE { x : M // 0 < x } :=
  ⟨fun _ _ _ h => Subtype.coe_le_coe.1 <| le_of_add_le_add_left h⟩

instance addRightReflectLE [AddRightReflectLE M] : AddRightReflectLE { x : M // 0 < x } :=
  ⟨fun _ _ _ h => Subtype.coe_le_coe.1 <| le_of_add_le_add_right h⟩

end AddBasic

instance addLeftMono [AddMonoid M] [PartialOrder M] [AddLeftStrictMono M] :
    AddLeftMono { x : M // 0 < x } :=
  ⟨@fun _ _ _ h₁ => StrictMono.monotone (fun _ _ h => add_lt_add_left h _) h₁⟩

section Mul

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

instance : Mul { x : R // 0 < x } :=
  ⟨fun x y => ⟨x * y, mul_pos x.2 y.2⟩⟩

@[simp]
theorem val_mul (x y : { x : R // 0 < x }) : ↑(x * y) = (x * y : R) :=
  rfl

instance : Pow { x : R // 0 < x } ℕ :=
  ⟨fun x n => ⟨(x : R) ^ n , pow_pos x.2 n⟩⟩

@[simp]
theorem val_pow (x : { x : R // 0 < x }) (n : ℕ) :
    ↑(x ^ n) = (x : R) ^ n :=
  rfl

instance : Semigroup { x : R // 0 < x } := fast_instance%
  Subtype.coe_injective.semigroup Subtype.val val_mul

instance : Distrib { x : R // 0 < x } := fast_instance%
  Subtype.coe_injective.distrib _ coe_add val_mul

instance : One { x : R // 0 < x } :=
  ⟨⟨1, one_pos⟩⟩

@[simp]
theorem val_one : ((1 : { x : R // 0 < x }) : R) = 1 :=
  rfl

instance : Monoid { x : R // 0 < x } := fast_instance%
  Subtype.coe_injective.monoid _ val_one val_mul val_pow

end Mul

section mul_comm

instance commMonoid [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] :
    CommMonoid { x : R // 0 < x } := fast_instance%
  Subtype.coe_injective.commMonoid (M₂ := R) (Subtype.val) val_one val_mul val_pow

instance isOrderedMonoid [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] :
    IsOrderedMonoid { x : R // 0 < x } :=
  { mul_le_mul_left := fun _ _ hxy c =>
      Subtype.coe_le_coe.1 <| mul_le_mul_of_nonneg_left hxy c.2.le }

/-- If `R` is a nontrivial linear ordered commutative semiring, then `{x : R // 0 < x}` is a linear
ordered cancellative commutative monoid. -/
instance isOrderedCancelMonoid [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] :
    IsOrderedCancelMonoid { x : R // 0 < x } :=
  { le_of_mul_le_mul_left := fun a _ _ h => Subtype.coe_le_coe.1 <| (mul_le_mul_left a.2).1 h }

end mul_comm

end Positive
