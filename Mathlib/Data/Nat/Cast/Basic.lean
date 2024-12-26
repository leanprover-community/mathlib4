/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Divisibility.Hom
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Group.TypeTags.Hom
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

assert_not_exists OrderedCommGroup
assert_not_exists Commute.zero_right
assert_not_exists Commute.add_right
assert_not_exists abs_eq_max_neg
assert_not_exists NeZero.natCast_ne
-- TODO: `MulOpposite.op_natCast` was not intended to be imported
-- assert_not_exists MulOpposite.op_natCast

-- Porting note: There are many occasions below where we need `simp [map_zero f]`
-- where `simp [map_zero]` should suffice. (Similarly for `map_one`.)
-- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/simp.20regression.20with.20MonoidHomClass

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

lemma cast_dvd_cast (h : m ∣ n) : (m : α) ∣ (n : α) := map_dvd (Nat.castRingHom α) h

alias _root_.Dvd.dvd.natCast := cast_dvd_cast

end Semiring
end Nat

section AddMonoidHomClass

variable {A B F : Type*} [AddMonoidWithOne B] [FunLike F ℕ A]

theorem ext_nat' [AddMonoid A] [AddMonoidHomClass F ℕ A] (f g : F) (h : f 1 = g 1) : f = g :=
  DFunLike.ext f g <| by
    intro n
    induction n with
    | zero => simp_rw [map_zero f, map_zero g]
    | succ n ihn =>
      simp [h, ihn]

@[ext]
theorem AddMonoidHom.ext_nat [AddMonoid A] {f g : ℕ →+ A} : f 1 = g 1 → f = g :=
  ext_nat' f g

variable [AddMonoidWithOne A]

-- these versions are primed so that the `RingHomClass` versions aren't
theorem eq_natCast' [AddMonoidHomClass F ℕ A] (f : F) (h1 : f 1 = 1) : ∀ n : ℕ, f n = n
  | 0 => by simp [map_zero f]
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
theorem ext_nat'' [MonoidWithZeroHomClass F ℕ A] (f g : F) (h_pos : ∀ {n : ℕ}, 0 < n → f n = g n) :
    f = g := by
  apply DFunLike.ext
  rintro (_ | n)
  · simp [map_zero f, map_zero g]
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
be `DFunLike.coe _ _`, due to the `no_index` that https://github.com/leanprover/lean4/issues/2867
forces us to include, and therefore it would negatively impact performance.

If that issue is resolved, this can be marked `@[simp]`. -/
theorem map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : ℕ) [Nat.AtLeastTwo n] :
    (f (no_index (OfNat.ofNat n)) : S) = OfNat.ofNat n :=
  map_natCast f n

theorem ext_nat [FunLike F ℕ R] [RingHomClass F ℕ R] (f g : F) : f = g :=
  ext_nat' f g <| by simp only [map_one f, map_one g]

theorem NeZero.nat_of_neZero {R S} [Semiring R] [Semiring S]
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
`Subsingleton`-/
instance Nat.uniqueRingHom {R : Type*} [NonAssocSemiring R] : Unique (ℕ →+* R) where
  default := Nat.castRingHom R
  uniq := RingHom.eq_natCast'

section Monoid
variable (α) [Monoid α] (β) [AddMonoid β]

/-- Additive homomorphisms from `ℕ` are defined by the image of `1`. -/
def multiplesHom : β ≃ (ℕ →+ β) where
  toFun x :=
  { toFun := fun n ↦ n • x
    map_zero' := zero_nsmul x
    map_add' := fun _ _ ↦ add_nsmul _ _ _ }
  invFun f := f 1
  left_inv := one_nsmul
  right_inv f := AddMonoidHom.ext_nat <| one_nsmul (f 1)

/-- Monoid homomorphisms from `Multiplicative ℕ` are defined by the image
of `Multiplicative.ofAdd 1`. -/
@[to_additive existing]
def powersHom : α ≃ (Multiplicative ℕ →* α) :=
  Additive.ofMul.trans <| (multiplesHom _).trans <| AddMonoidHom.toMultiplicative''

variable {α}

-- TODO: can `to_additive` generate the following lemmas automatically?

lemma multiplesHom_apply (x : β) (n : ℕ) : multiplesHom β x n = n • x := rfl

@[to_additive existing (attr := simp)]
lemma powersHom_apply (x : α) (n : Multiplicative ℕ) :
    powersHom α x n = x ^ n.toAdd := rfl

lemma multiplesHom_symm_apply (f : ℕ →+ β) : (multiplesHom β).symm f = f 1 := rfl

@[to_additive existing (attr := simp)]
lemma powersHom_symm_apply (f : Multiplicative ℕ →* α) :
    (powersHom α).symm f = f (Multiplicative.ofAdd 1) := rfl

lemma MonoidHom.apply_mnat (f : Multiplicative ℕ →* α) (n : Multiplicative ℕ) :
    f n = f (Multiplicative.ofAdd 1) ^ n.toAdd := by
  rw [← powersHom_symm_apply, ← powersHom_apply, Equiv.apply_symm_apply]

@[ext]
lemma MonoidHom.ext_mnat ⦃f g : Multiplicative ℕ →* α⦄
    (h : f (Multiplicative.ofAdd 1) = g (Multiplicative.ofAdd 1)) : f = g :=
  MonoidHom.ext fun n ↦ by rw [f.apply_mnat, g.apply_mnat, h]

lemma AddMonoidHom.apply_nat (f : ℕ →+ β) (n : ℕ) : f n = n • f 1 := by
  rw [← multiplesHom_symm_apply, ← multiplesHom_apply, Equiv.apply_symm_apply]

end Monoid

section CommMonoid
variable (α) [CommMonoid α] (β) [AddCommMonoid β]

/-- If `α` is commutative, `multiplesHom` is an additive equivalence. -/
def multiplesAddHom : β ≃+ (ℕ →+ β) :=
  { multiplesHom β with map_add' := fun a b ↦ AddMonoidHom.ext fun n ↦ by simp [nsmul_add] }

/-- If `α` is commutative, `powersHom` is a multiplicative equivalence. -/
def powersMulHom : α ≃* (Multiplicative ℕ →* α) :=
  { powersHom α with map_mul' := fun a b ↦ MonoidHom.ext fun n ↦ by simp [mul_pow] }

@[simp] lemma multiplesAddHom_apply (x : β) (n : ℕ) : multiplesAddHom β x n = n • x := rfl

@[simp]
lemma powersMulHom_apply (x : α) (n : Multiplicative ℕ) : powersMulHom α x n = x ^ n.toAdd := rfl

@[simp] lemma multiplesAddHom_symm_apply (f : ℕ →+ β) : (multiplesAddHom β).symm f = f 1 := rfl

@[simp] lemma powersMulHom_symm_apply (f : Multiplicative ℕ →* α) :
    (powersMulHom α).symm f = f (ofAdd 1) := rfl

end CommMonoid

namespace Pi

variable {π : α → Type*} [∀ a, NatCast (π a)]

instance instNatCast : NatCast (∀ a, π a) where natCast n _ := n

theorem natCast_apply (n : ℕ) (a : α) : (n : ∀ a, π a) a = n :=
  rfl

@[simp]
theorem natCast_def (n : ℕ) : (n : ∀ a, π a) = fun _ ↦ ↑n :=
  rfl

@[deprecated (since := "2024-04-05")] alias nat_apply := natCast_apply
@[deprecated (since := "2024-04-05")] alias coe_nat := natCast_def

@[simp]
theorem ofNat_apply (n : ℕ) [n.AtLeastTwo] (a : α) : (OfNat.ofNat n : ∀ a, π a) a = n := rfl

end Pi

theorem Sum.elim_natCast_natCast {α β γ : Type*} [NatCast γ] (n : ℕ) :
    Sum.elim (n : α → γ) (n : β → γ) = n :=
  Sum.elim_lam_const_lam_const (γ := γ) n
