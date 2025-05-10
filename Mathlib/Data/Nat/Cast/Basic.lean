/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Divisibility.Hom
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Group.Nat.Hom
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat

/-!
# Cast of natural numbers (additional theorems)

This file proves additional properties about the *canonical* homomorphism from
the natural numbers into an additive monoid with a one (`Nat.cast`).

## Main declarations

* `castAddMonoidHom`: `cast` bundled as an `AddMonoidHom`.
* `castRingHom`: `cast` bundled as a `RingHom`.
-/

assert_not_exists OrderedCommGroup Commute.zero_right Commute.add_right abs_eq_max_neg
  NeZero.natCast_ne
-- TODO: `MulOpposite.op_natCast` was not intended to be imported
-- assert_not_exists MulOpposite.op_natCast

open Additive Multiplicative

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

lemma _root_.Even.natCast [AddMonoidWithOne α] {n : ℕ} (hn : Even n) : Even (n : α) :=
  hn.map <| Nat.castAddMonoidHom α

section NonAssocSemiring
variable [NonAssocSemiring α]

@[simp, norm_cast] lemma cast_mul (m n : ℕ) : ((m * n : ℕ) : α) = m * n := by
  induction n <;> simp [mul_succ, mul_add, *]

variable (α) in
/-- `Nat.cast : ℕ → α` as a `RingHom` -/
def castRingHom : ℕ →+* α :=
  { castAddMonoidHom α with toFun := Nat.cast, map_one' := cast_one, map_mul' := cast_mul }

@[simp, norm_cast] lemma coe_castRingHom : (castRingHom α : ℕ → α) = Nat.cast := rfl

lemma _root_.nsmul_eq_mul' (a : α) (n : ℕ) : n • a = a * n := by
  induction n with
  | zero => rw [zero_nsmul, Nat.cast_zero, mul_zero]
  | succ n ih => rw [succ_nsmul, ih, Nat.cast_succ, mul_add, mul_one]

@[simp] lemma _root_.nsmul_eq_mul (n : ℕ) (a : α) : n • a = n * a := by
  induction n with
  | zero => rw [zero_nsmul, Nat.cast_zero, zero_mul]
  | succ n ih => rw [succ_nsmul, ih, Nat.cast_succ, add_mul, one_mul]

end NonAssocSemiring

section Semiring
variable [Semiring α] {m n : ℕ}

@[simp, norm_cast]
lemma cast_pow (m : ℕ) : ∀ n : ℕ, ↑(m ^ n) = (m ^ n : α)
  | 0 => by simp
  | n + 1 => by rw [_root_.pow_succ', _root_.pow_succ', cast_mul, cast_pow m n]

@[gcongr]
lemma cast_dvd_cast (h : m ∣ n) : (m : α) ∣ (n : α) := map_dvd (Nat.castRingHom α) h

alias _root_.Dvd.dvd.natCast := cast_dvd_cast

end Semiring
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

section MonoidWithZeroHomClass

variable {A F : Type*} [MulZeroOneClass A] [FunLike F ℕ A]

/-- If two `MonoidWithZeroHom`s agree on the positive naturals they are equal. -/
theorem ext_nat'' [ZeroHomClass F ℕ A] (f g : F) (h_pos : ∀ {n : ℕ}, 0 < n → f n = g n) :
    f = g := by
  apply DFunLike.ext
  rintro (_ | n)
  · simp
  · exact h_pos n.succ_pos

@[ext]
theorem MonoidWithZeroHom.ext_nat {f g : ℕ →*₀ A} : (∀ {n : ℕ}, 0 < n → f n = g n) → f = g :=
  ext_nat'' f g

end MonoidWithZeroHomClass

section RingHomClass

variable {R S F : Type*} [NonAssocSemiring R] [NonAssocSemiring S]

@[simp]
theorem eq_natCast [FunLike F ℕ R] [RingHomClass F ℕ R] (f : F) : ∀ n, f n = n :=
  eq_natCast' f <| map_one f

@[simp]
theorem map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : ∀ n : ℕ, f (n : R) = n :=
  map_natCast' f <| map_one f

/-- This lemma is not marked `@[simp]` lemma because its `#discr_tree_key` (for the LHS) would just
be `DFunLike.coe _ _`, due to the `ofNat` that https://github.com/leanprover/lean4/issues/2867
forces us to include, and therefore it would negatively impact performance.

If that issue is resolved, this can be marked `@[simp]`. -/
theorem map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : ℕ) [Nat.AtLeastTwo n] :
    (f ofNat(n) : S) = OfNat.ofNat n :=
  map_natCast f n

theorem ext_nat [FunLike F ℕ R] [RingHomClass F ℕ R] (f g : F) : f = g :=
  ext_nat' f g <| by simp

theorem NeZero.nat_of_neZero {R S} [NonAssocSemiring R] [NonAssocSemiring S]
    {F} [FunLike F R S] [RingHomClass F R S] (f : F)
    {n : ℕ} [hn : NeZero (n : S)] : NeZero (n : R) :=
  .of_map (f := f) (neZero := by simp only [map_natCast, hn])

end RingHomClass

namespace RingHom

/-- This is primed to match `eq_intCast'`. -/
theorem eq_natCast' {R} [NonAssocSemiring R] (f : ℕ →+* R) : f = Nat.castRingHom R :=
  RingHom.ext <| eq_natCast f

end RingHom

@[simp, norm_cast]
theorem Nat.cast_id (n : ℕ) : n.cast = n :=
  rfl

@[simp]
theorem Nat.castRingHom_nat : Nat.castRingHom ℕ = RingHom.id ℕ :=
  rfl

/-- We don't use `RingHomClass` here, since that might cause type-class slowdown for
`Subsingleton`. -/
instance Nat.uniqueRingHom {R : Type*} [NonAssocSemiring R] : Unique (ℕ →+* R) where
  default := Nat.castRingHom R
  uniq := RingHom.eq_natCast'

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
