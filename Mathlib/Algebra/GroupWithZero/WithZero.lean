/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin
-/
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.WithOne.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Option.Basic
import Mathlib.Data.Option.NAry

/-!
# Adjoining a zero to a group

This file proves that one can adjoin a new zero element to a group and get a group with zero.
-/

namespace WithZero
variable {α : Type*}

section One
variable [One α]

instance one : One (WithZero α) where
  __ := ‹One α›

@[simp, norm_cast] lemma coe_one : ((1 : α) : WithZero α) = 1 := rfl
#align with_zero.coe_one WithZero.coe_one

end One

section Mul
variable [Mul α]

instance mulZeroClass : MulZeroClass (WithZero α) where
  mul := Option.map₂ (· * ·)
  zero_mul := Option.map₂_none_left (· * ·)
  mul_zero := Option.map₂_none_right (· * ·)

@[simp, norm_cast] lemma coe_mul (a b : α) : (↑(a * b) : WithZero α) = a * b := rfl
#align with_zero.coe_mul WithZero.coe_mul

instance noZeroDivisors : NoZeroDivisors (WithZero α) := ⟨Option.map₂_eq_none_iff.1⟩

end Mul

instance semigroupWithZero [Semigroup α] : SemigroupWithZero (WithZero α) where
  __ := mulZeroClass
  mul_assoc _ _ _ := Option.map₂_assoc mul_assoc

instance commSemigroup [CommSemigroup α] : CommSemigroup (WithZero α) where
  __ := semigroupWithZero
  mul_comm _ _ := Option.map₂_comm mul_comm

instance mulZeroOneClass [MulOneClass α] : MulZeroOneClass (WithZero α) where
  __ := mulZeroClass
  one_mul := Option.map₂_left_identity one_mul
  mul_one := Option.map₂_right_identity mul_one

section Pow
variable [One α] [Pow α ℕ]

instance pow : Pow (WithZero α) ℕ where
  pow x n := match x, n with
    | none, 0 => 1
    | none, _ + 1 => 0
    | some x, n => ↑(x ^ n)

@[simp, norm_cast] lemma coe_pow (a : α) (n : ℕ) : (↑(a ^ n) : WithZero α) = a ^ n := rfl
#align with_zero.coe_pow WithZero.coe_pow

end Pow

instance monoidWithZero [Monoid α] : MonoidWithZero (WithZero α) where
  __ := mulZeroOneClass
  __ := semigroupWithZero
  npow n a := a ^ n
  npow_zero a := match a with
    | none => rfl
    | some a => congr_arg some (pow_zero _)
  npow_succ n a := match a with
    | none => by change 0 ^ (n + 1) = 0 ^ n * 0; simp only [mul_zero]; rfl
    | some a => congr_arg some <| pow_succ _ _

instance commMonoidWithZero [CommMonoid α] : CommMonoidWithZero (WithZero α) :=
  { WithZero.monoidWithZero, WithZero.commSemigroup with }

section Inv
variable [Inv α]

/-- Extend the inverse operation on `α` to `WithZero α` by sending `0` to `0`. -/
instance inv : Inv (WithZero α) where inv a := Option.map (·⁻¹) a

@[simp, norm_cast] lemma coe_inv (a : α) : ((a⁻¹ : α) : WithZero α) = (↑a)⁻¹ := rfl
#align with_zero.coe_inv WithZero.coe_inv

@[simp] protected lemma inv_zero : (0 : WithZero α)⁻¹ = 0 := rfl
#align with_zero.inv_zero WithZero.inv_zero

end Inv

instance invOneClass [InvOneClass α] : InvOneClass (WithZero α) where
  inv_one := show ((1⁻¹ : α) : WithZero α) = 1 by simp

section Div
variable [Div α]

instance div : Div (WithZero α) where div := Option.map₂ (· / ·)

@[norm_cast] lemma coe_div (a b : α) : ↑(a / b : α) = (a / b : WithZero α) := rfl
#align with_zero.coe_div WithZero.coe_div

end Div

section ZPow
variable [One α] [Pow α ℤ]

instance : Pow (WithZero α) ℤ where
  pow a n := match a, n with
    | none, Int.ofNat 0 => 1
    | none, Int.ofNat (Nat.succ _) => 0
    | none, Int.negSucc _ => 0
    | some x, n => ↑(x ^ n)

@[simp, norm_cast] lemma coe_zpow (a : α) (n : ℤ) : ↑(a ^ n) = (↑a : WithZero α) ^ n := rfl
#align with_zero.coe_zpow WithZero.coe_zpow

end ZPow

instance divInvMonoid [DivInvMonoid α] : DivInvMonoid (WithZero α) where
  __ := monoidWithZero
  div_eq_mul_inv a b := match a, b with
    | none, _ => rfl
    | some _, none => rfl
    | some a, some b => congr_arg some (div_eq_mul_inv a b)
  zpow n a := a ^ n
  zpow_zero' a := match a with
    | none => rfl
    | some a => congr_arg some (zpow_zero _)
  zpow_succ' n a := match a with
    | none => by change 0 ^ _ = 0 ^ _ * 0; simp only [mul_zero]; rfl
    | some a => congr_arg some (DivInvMonoid.zpow_succ' _ _)
  zpow_neg' n a := match a with
    | none => rfl
    | some a => congr_arg some (DivInvMonoid.zpow_neg' _ _)

instance divInvOneMonoid [DivInvOneMonoid α] : DivInvOneMonoid (WithZero α) where
  __ := divInvMonoid
  __ := invOneClass

instance involutiveInv [InvolutiveInv α] : InvolutiveInv (WithZero α) where
  inv_inv a := (Option.map_map _ _ _).trans <| by simp [Function.comp]

instance divisionMonoid [DivisionMonoid α] : DivisionMonoid (WithZero α) where
  __ := divInvMonoid
  __ := involutiveInv
  mul_inv_rev a b := match a, b with
    | none, none => rfl
    | none, some b => rfl
    | some a, none => rfl
    | some a, some b => congr_arg some (mul_inv_rev _ _)
  inv_eq_of_mul a b := match a, b with
    | none, none => fun _ ↦ rfl
    | none, some b => fun _ ↦ by contradiction
    | some a, none => fun _ ↦ by contradiction
    | some a, some b => fun h ↦
      congr_arg some <| inv_eq_of_mul_eq_one_right <| Option.some_injective _ h

instance divisionCommMonoid [DivisionCommMonoid α] : DivisionCommMonoid (WithZero α) where
  __ := divisionMonoid
  __ := commSemigroup

section Group
variable [Group α]

/-- If `G` is a group then `WithZero G` is a group with zero. -/
instance groupWithZero : GroupWithZero (WithZero α) where
  __ := monoidWithZero
  __ := divInvMonoid
  __ := nontrivial
  inv_zero := WithZero.inv_zero
  mul_inv_cancel a ha := by lift a to α using ha; norm_cast; apply mul_right_inv


/-- Any group is isomorphic to the units of itself adjoined with `0`. -/
def unitsWithZeroEquiv : (WithZero α)ˣ ≃* α where
  toFun a := unzero a.ne_zero
  invFun a := Units.mk0 a coe_ne_zero
  left_inv _ := Units.ext <| by simp only [coe_unzero, Units.mk0_val]
  right_inv _ := rfl
  map_mul' _ _ := coe_inj.mp <| by simp only [Units.val_mul, coe_unzero, coe_mul]
#align with_zero.units_with_zero_equiv WithZero.unitsWithZeroEquiv

end Group

instance commGroupWithZero [CommGroup α] : CommGroupWithZero (WithZero α) :=
  { WithZero.groupWithZero, WithZero.commMonoidWithZero with }

instance addMonoidWithOne [AddMonoidWithOne α] : AddMonoidWithOne (WithZero α) where
  natCast n := if n = 0 then 0 else (n : α)
  natCast_zero := rfl
  natCast_succ n := by
    cases n with
    | zero => show (((1 : ℕ) : α) : WithZero α) = 0 + 1; · rw [Nat.cast_one, coe_one, zero_add]
    | succ n =>
        show (((n + 2 : ℕ) : α) : WithZero α) = ((n + 1 : ℕ) : α) + 1
        rw [Nat.cast_succ, coe_add, coe_one]

end WithZero
