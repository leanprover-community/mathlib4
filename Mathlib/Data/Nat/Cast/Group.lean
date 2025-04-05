/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Cast.Defs

/-!
# Cast of natural numbers (additional theorems)

This file proves additional properties about the *canonical* homomorphism from
the natural numbers into an additive monoid with a one (`Nat.cast`).

## Main declarations

* `castAddMonoidHom`: `cast` bundled as an `AddMonoidHom`.
-/

assert_not_exists OrderedCommGroup Commute.zero_right Commute.add_right abs_eq_max_neg
  NeZero.natCast_ne MulOpposite.op_natCast MonoidWithZero

variable {α β : Type*}

namespace Nat

/-- `Nat.cast : ℕ → α` as an `AddMonoidHom`. -/
def castAddMonoidHom (α : Type*) [AddMonoidWithOne α] :
    ℕ →+ α where
  toFun := Nat.cast
  map_add' := cast_add
  map_zero' := cast_zero

@[simp]
theorem coe_castAddMonoidHom [AddMonoidWithOne α] : (castAddMonoidHom α : ℕ → α) = Nat.cast :=
  rfl


end Nat

section AddMonoidHomClass

variable {A B F : Type*} [AddMonoidWithOne B] [FunLike F ℕ A] [AddMonoidWithOne A]

-- these versions are primed so that the `RingHomClass` versions aren't
theorem eq_natCast' [AddMonoidHomClass F ℕ A] (f : F) (h1 : f 1 = 1) : ∀ n : ℕ, f n = n
  | 0 => by simp
  | n + 1 => by rw [map_add, h1, eq_natCast' f h1 n, Nat.cast_add_one]

theorem map_natCast' {A} [AddMonoidWithOne A] [FunLike F A B] [AddMonoidHomClass F A B]
    (f : F) (h : f 1 = 1) :
    ∀ n : ℕ, f n = n :=
  eq_natCast' ((f : A →+ B).comp <| Nat.castAddMonoidHom _) (by simpa)

theorem map_ofNat' {A} [AddMonoidWithOne A] [FunLike F A B] [AddMonoidHomClass F A B]
    (f : F) (h : f 1 = 1) (n : ℕ) [n.AtLeastTwo] : f (OfNat.ofNat n) = OfNat.ofNat n :=
  map_natCast' f h n

end AddMonoidHomClass

@[simp, norm_cast]
theorem Nat.cast_id (n : ℕ) : n.cast = n :=
  rfl

namespace Pi

variable {π : α → Type*}

section NatCast
variable [∀ a, NatCast (π a)]

instance instNatCast : NatCast (∀ a, π a) where natCast n _ := n

@[simp]
theorem natCast_apply (n : ℕ) (a : α) : (n : ∀ a, π a) a = n :=
  rfl

theorem natCast_def (n : ℕ) : (n : ∀ a, π a) = fun _ ↦ ↑n :=
  rfl

end NatCast

section OfNat

-- This instance is low priority, as `to_additive` only works with the one that comes from `One`
-- and `Zero`.
instance (priority := low) instOfNat (n : ℕ) [∀ i, OfNat (π i) n] : OfNat ((i : α) → π i) n where
  ofNat _ := OfNat.ofNat n

@[simp]
theorem ofNat_apply (n : ℕ) [∀ i, OfNat (π i) n] (a : α) : (ofNat(n) : ∀ a, π a) a = ofNat(n) := rfl

lemma ofNat_def (n : ℕ) [∀ i, OfNat (π i) n] : (ofNat(n) : ∀ a, π a) = fun _ ↦ ofNat(n) := rfl

end OfNat

end Pi

theorem Sum.elim_natCast_natCast {α β γ : Type*} [NatCast γ] (n : ℕ) :
    Sum.elim (n : α → γ) (n : β → γ) = n :=
  Sum.elim_lam_const_lam_const (γ := γ) n
