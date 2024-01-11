/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Data.Nat.Basic

#align_import data.nat.cast.basic from "leanprover-community/mathlib"@"acebd8d49928f6ed8920e502a6c90674e75bd441"

/-!
# Cast of natural numbers (additional theorems)

This file proves additional properties about the *canonical* homomorphism from
the natural numbers into an additive monoid with a one (`Nat.cast`).

## Main declarations

* `castAddMonoidHom`: `cast` bundled as an `AddMonoidHom`.
* `castRingHom`: `cast` bundled as a `RingHom`.
-/

-- Porting note: There are many occasions below where we need `simp [map_zero f]`
-- where `simp [map_zero]` should suffice. (Similarly for `map_one`.)
-- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/simp.20regression.20with.20MonoidHomClass

variable {α β : Type*}

namespace Nat

/-- `Nat.cast : ℕ → α` as an `AddMonoidHom`. -/
def castAddMonoidHom (α : Type*) [AddMonoidWithOne α] :
    ℕ →+ α where
  toFun := Nat.cast
  map_add' := cast_add
  map_zero' := cast_zero
#align nat.cast_add_monoid_hom Nat.castAddMonoidHom

@[simp]
theorem coe_castAddMonoidHom [AddMonoidWithOne α] : (castAddMonoidHom α : ℕ → α) = Nat.cast :=
  rfl
#align nat.coe_cast_add_monoid_hom Nat.coe_castAddMonoidHom

@[simp, norm_cast]
theorem cast_mul [NonAssocSemiring α] (m n : ℕ) : ((m * n : ℕ) : α) = m * n := by
  induction n <;> simp [mul_succ, mul_add, *]
#align nat.cast_mul Nat.cast_mul

/-- `Nat.cast : ℕ → α` as a `RingHom` -/
def castRingHom (α : Type*) [NonAssocSemiring α] : ℕ →+* α :=
  { castAddMonoidHom α with toFun := Nat.cast, map_one' := cast_one, map_mul' := cast_mul }
#align nat.cast_ring_hom Nat.castRingHom

@[simp]
theorem coe_castRingHom [NonAssocSemiring α] : (castRingHom α : ℕ → α) = Nat.cast :=
  rfl
#align nat.coe_cast_ring_hom Nat.coe_castRingHom



theorem coe_nat_dvd [Semiring α] {m n : ℕ} (h : m ∣ n) : (m : α) ∣ (n : α) :=
  map_dvd (Nat.castRingHom α) h
#align nat.coe_nat_dvd Nat.coe_nat_dvd

alias _root_.Dvd.dvd.natCast := coe_nat_dvd

end Nat

section AddMonoidHomClass

variable {A B F : Type*} [AddMonoidWithOne B]

theorem ext_nat' [AddMonoid A] [AddMonoidHomClass F ℕ A] (f g : F) (h : f 1 = g 1) : f = g :=
  FunLike.ext f g <| by
    intro n
    induction n with
    | zero => simp_rw [Nat.zero_eq, map_zero f, map_zero g]
    | succ n ihn =>
      simp [Nat.succ_eq_add_one, h, ihn]
#align ext_nat' ext_nat'

@[ext]
theorem AddMonoidHom.ext_nat [AddMonoid A] {f g : ℕ →+ A} : f 1 = g 1 → f = g :=
  ext_nat' f g
#align add_monoid_hom.ext_nat AddMonoidHom.ext_nat

variable [AddMonoidWithOne A]

-- these versions are primed so that the `RingHomClass` versions aren't
theorem eq_natCast' [AddMonoidHomClass F ℕ A] (f : F) (h1 : f 1 = 1) : ∀ n : ℕ, f n = n
  | 0 => by simp [map_zero f]
  | n + 1 => by rw [map_add, h1, eq_natCast' f h1 n, Nat.cast_add_one]
#align eq_nat_cast' eq_natCast'

theorem map_natCast' {A} [AddMonoidWithOne A] [AddMonoidHomClass F A B] (f : F) (h : f 1 = 1) :
    ∀ n : ℕ, f n = n
  | 0 => by simp [map_zero f]
  | n + 1 => by
    rw [Nat.cast_add, map_add, Nat.cast_add, map_natCast' f h n, Nat.cast_one, h, Nat.cast_one]
#align map_nat_cast' map_natCast'

end AddMonoidHomClass

section MonoidWithZeroHomClass

variable {A F : Type*} [MulZeroOneClass A]

/-- If two `MonoidWithZeroHom`s agree on the positive naturals they are equal. -/
theorem ext_nat'' [MonoidWithZeroHomClass F ℕ A] (f g : F) (h_pos : ∀ {n : ℕ}, 0 < n → f n = g n) :
    f = g := by
  apply FunLike.ext
  rintro (_ | n)
  · simp [map_zero f, map_zero g]
  · exact h_pos n.succ_pos
#align ext_nat'' ext_nat''

@[ext]
theorem MonoidWithZeroHom.ext_nat {f g : ℕ →*₀ A} : (∀ {n : ℕ}, 0 < n → f n = g n) → f = g :=
  ext_nat'' f g
#align monoid_with_zero_hom.ext_nat MonoidWithZeroHom.ext_nat

end MonoidWithZeroHomClass

section RingHomClass

variable {R S F : Type*} [NonAssocSemiring R] [NonAssocSemiring S]

@[simp]
theorem eq_natCast [RingHomClass F ℕ R] (f : F) : ∀ n, f n = n :=
  eq_natCast' f <| map_one f
#align eq_nat_cast eq_natCast

@[simp]
theorem map_natCast [RingHomClass F R S] (f : F) : ∀ n : ℕ, f (n : R) = n :=
  map_natCast' f <| map_one f
#align map_nat_cast map_natCast

--Porting note: new theorem
@[simp]
theorem map_ofNat [RingHomClass F R S] (f : F) (n : ℕ) [Nat.AtLeastTwo n] :
    (f (no_index (OfNat.ofNat n)) : S) = OfNat.ofNat n :=
  map_natCast f n

theorem ext_nat [RingHomClass F ℕ R] (f g : F) : f = g :=
  ext_nat' f g <| by simp only [map_one f, map_one g]
#align ext_nat ext_nat

theorem NeZero.nat_of_neZero {R S} [Semiring R] [Semiring S] {F} [RingHomClass F R S] (f : F)
    {n : ℕ} [hn : NeZero (n : S)] : NeZero (n : R) :=
  .of_map (f := f) (neZero := by simp only [map_natCast, hn])
#align ne_zero.nat_of_ne_zero NeZero.nat_of_neZero

end RingHomClass

namespace RingHom

/-- This is primed to match `eq_intCast'`. -/
theorem eq_natCast' {R} [NonAssocSemiring R] (f : ℕ →+* R) : f = Nat.castRingHom R :=
  RingHom.ext <| eq_natCast f
#align ring_hom.eq_nat_cast' RingHom.eq_natCast'

end RingHom

@[simp, norm_cast]
theorem Nat.cast_id (n : ℕ) : n.cast = n :=
  rfl
#align nat.cast_id Nat.cast_id

@[simp]
theorem Nat.castRingHom_nat : Nat.castRingHom ℕ = RingHom.id ℕ :=
  rfl
#align nat.cast_ring_hom_nat Nat.castRingHom_nat

/-- We don't use `RingHomClass` here, since that might cause type-class slowdown for
`Subsingleton`-/
instance Nat.uniqueRingHom {R : Type*} [NonAssocSemiring R] : Unique (ℕ →+* R) where
  default := Nat.castRingHom R
  uniq := RingHom.eq_natCast'

namespace Pi

variable {π : α → Type*} [∀ a, NatCast (π a)]

/- Porting note: manually wrote this instance.
Was `by refine_struct { .. } <;> pi_instance_derive_field` -/
instance natCast : NatCast (∀ a, π a) := { natCast := fun n _ ↦ n }

theorem nat_apply (n : ℕ) (a : α) : (n : ∀ a, π a) a = n :=
  rfl
#align pi.nat_apply Pi.nat_apply

@[simp]
theorem coe_nat (n : ℕ) : (n : ∀ a, π a) = fun _ ↦ ↑n :=
  rfl
#align pi.coe_nat Pi.coe_nat

@[simp]
theorem ofNat_apply (n : ℕ) [n.AtLeastTwo] (a : α) : (OfNat.ofNat n : ∀ a, π a) a = n := rfl

end Pi

theorem Sum.elim_natCast_natCast {α β γ : Type*} [NatCast γ] (n : ℕ) :
    Sum.elim (n : α → γ) (n : β → γ) = n :=
  Sum.elim_lam_const_lam_const (γ := γ) n
#align sum.elim_nat_cast_nat_cast Sum.elim_natCast_natCast

-- Guard against import creep regression.
assert_not_exists OrderedCommGroup
assert_not_exists CharZero
assert_not_exists Commute.zero_right
assert_not_exists Commute.add_right
assert_not_exists abs_eq_max_neg
assert_not_exists natCast_ne
assert_not_exists MulOpposite.natCast
