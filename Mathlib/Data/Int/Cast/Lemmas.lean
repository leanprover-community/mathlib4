/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Parity

/-!
# Cast of integers (additional theorems)

This file proves additional properties about the *canonical* homomorphism from
the integers into an additive group with a one (`Int.cast`),
particularly results involving algebraic homomorphisms or the order structure on `ℤ`
which were not available in the import dependencies of `Data.Int.Cast.Basic`.

## Main declarations

* `castAddHom`: `cast` bundled as an `AddMonoidHom`.
* `castRingHom`: `cast` bundled as a `RingHom`.
-/

assert_not_exists RelIso Field

open Additive Function Multiplicative Nat

variable {F ι α β : Type*}

namespace Int

/-- Coercion `ℕ → ℤ` as a `RingHom`. -/
def ofNatHom : ℕ →+* ℤ :=
  Nat.castRingHom ℤ

section cast

@[simp, norm_cast]
theorem cast_ite [IntCast α] (P : Prop) [Decidable P] (m n : ℤ) :
    ((ite P m n : ℤ) : α) = ite P (m : α) (n : α) :=
  apply_ite _ _ _ _

/-- `coe : ℤ → α` as an `AddMonoidHom`. -/
def castAddHom (α : Type*) [AddGroupWithOne α] : ℤ →+ α where
  toFun := Int.cast
  map_zero' := cast_zero
  map_add' := cast_add

section AddGroupWithOne
variable [AddGroupWithOne α]

@[simp] lemma coe_castAddHom : ⇑(castAddHom α) = fun x : ℤ => (x : α) := rfl

lemma _root_.Even.intCast {n : ℤ} (h : Even n) : Even (n : α) := h.map (castAddHom α)

variable [CharZero α] {m n : ℤ}

@[simp] lemma cast_eq_zero : (n : α) = 0 ↔ n = 0 where
  mp h := by
    cases n
    · rw [ofNat_eq_coe, Int.cast_natCast] at h
      exact congr_arg _ (Nat.cast_eq_zero.1 h)
    · rw [cast_negSucc, neg_eq_zero, Nat.cast_eq_zero] at h
      contradiction
  mpr h := by rw [h, cast_zero]

@[simp, norm_cast]
lemma cast_inj : (m : α) = n ↔ m = n := by rw [← sub_eq_zero, ← cast_sub, cast_eq_zero, sub_eq_zero]

lemma cast_injective : Injective (Int.cast : ℤ → α) := fun _ _ ↦ cast_inj.1

lemma cast_ne_zero : (n : α) ≠ 0 ↔ n ≠ 0 := not_congr cast_eq_zero

@[simp] lemma cast_eq_one : (n : α) = 1 ↔ n = 1 := by rw [← cast_one, cast_inj]

lemma cast_ne_one : (n : α) ≠ 1 ↔ n ≠ 1 := cast_eq_one.not

end AddGroupWithOne

section NonAssocRing
variable [NonAssocRing α]

variable (α) in
/-- `coe : ℤ → α` as a `RingHom`. -/
def castRingHom : ℤ →+* α where
  toFun := Int.cast
  map_zero' := cast_zero
  map_add' := cast_add
  map_one' := cast_one
  map_mul' := cast_mul

@[simp] lemma coe_castRingHom : ⇑(castRingHom α) = fun x : ℤ ↦ (x : α) := rfl

lemma cast_commute : ∀ (n : ℤ) (a : α), Commute ↑n a
  | (n : ℕ), x => by simpa using n.cast_commute x
  | -[n+1], x => by
    simpa only [cast_negSucc, Commute.neg_left_iff, Commute.neg_right_iff] using
      (n + 1).cast_commute (-x)

lemma cast_comm (n : ℤ) (x : α) : n * x = x * n := (cast_commute ..).eq

lemma commute_cast (a : α) (n : ℤ) : Commute a n := (cast_commute ..).symm

@[simp] lemma _root_.zsmul_eq_mul (a : α) : ∀ n : ℤ, n • a = n * a
  | (n : ℕ) => by rw [natCast_zsmul, nsmul_eq_mul, Int.cast_natCast]
  | -[n+1] => by simp [Nat.cast_succ, neg_add_rev, Int.cast_negSucc, add_mul]

lemma _root_.zsmul_eq_mul' (a : α) (n : ℤ) : n • a = a * n := by
  rw [zsmul_eq_mul, (n.cast_commute a).eq]

end NonAssocRing

section Ring
variable [Ring α] {n : ℤ}

lemma _root_.Odd.intCast (hn : Odd n) : Odd (n : α) := hn.map (castRingHom α)

end Ring

theorem cast_dvd_cast [Ring α] (m n : ℤ) (h : m ∣ n) : (m : α) ∣ (n : α) :=
  map_dvd (Int.castRingHom α) h

end cast

end Int

open Int

namespace SemiconjBy
variable [Ring α] {a x y : α}

@[simp] lemma intCast_mul_right (h : SemiconjBy a x y) (n : ℤ) : SemiconjBy a (n * x) (n * y) :=
  SemiconjBy.mul_right (Int.commute_cast _ _) h

@[simp] lemma intCast_mul_left (h : SemiconjBy a x y) (n : ℤ) : SemiconjBy (n * a) x y :=
  SemiconjBy.mul_left (Int.cast_commute _ _) h

lemma intCast_mul_intCast_mul (h : SemiconjBy a x y) (m n : ℤ) :
    SemiconjBy (m * a) (n * x) (n * y) := by simp [h]

end SemiconjBy

namespace Commute
section NonAssocRing
variable [NonAssocRing α] {a : α} {n : ℤ}

@[simp] lemma intCast_left : Commute (n : α) a := Int.cast_commute _ _

@[simp] lemma intCast_right : Commute a n := Int.commute_cast _ _

end NonAssocRing

section Ring
variable [Ring α] {a b : α}

lemma intCast_mul_right (h : Commute a b) (m : ℤ) : Commute a (m * b) := by
  simp [h]

lemma intCast_mul_left (h : Commute a b) (m : ℤ) : Commute (m * a) b := by
  simp [h]

lemma intCast_mul_intCast_mul (h : Commute a b) (m n : ℤ) : Commute (m * a) (n * b) :=
  SemiconjBy.intCast_mul_intCast_mul h m n

variable (a) (m n : ℤ)

lemma self_intCast_mul : Commute a (n * a : α) := (Commute.refl a).intCast_mul_right n

lemma intCast_mul_self : Commute ((n : α) * a) a := (Commute.refl a).intCast_mul_left n

lemma self_intCast_mul_intCast_mul : Commute (m * a : α) (n * a : α) :=
  (Commute.refl a).intCast_mul_intCast_mul m n

end Ring
end Commute

namespace AddMonoidHom

variable {A : Type*}

/-- Two additive monoid homomorphisms `f`, `g` from `ℤ` to an additive monoid are equal
if `f 1 = g 1`. -/
@[ext high]
theorem ext_int [AddMonoid A] {f g : ℤ →+ A} (h1 : f 1 = g 1) : f = g :=
  have : f.comp (Int.ofNatHom : ℕ →+ ℤ) = g.comp (Int.ofNatHom : ℕ →+ ℤ) := ext_nat' _ _ h1
  have this' : ∀ n : ℕ, f n = g n := DFunLike.ext_iff.1 this
  ext fun n => match n with
  | (n : ℕ) => this' n
  | .negSucc n => eq_on_neg _ _ (this' <| n + 1)

variable [AddGroupWithOne A]

theorem eq_intCastAddHom (f : ℤ →+ A) (h1 : f 1 = 1) : f = Int.castAddHom A :=
  ext_int <| by simp [h1]

end AddMonoidHom

namespace AddEquiv
variable {A : Type*}

/-- Two additive monoid isomorphisms `f`, `g` from `ℤ` to an additive monoid are equal
if `f 1 = g 1`. -/
@[ext high]
theorem ext_int [AddMonoid A] {f g : ℤ ≃+ A} (h1 : f 1 = g 1) : f = g :=
  toAddMonoidHom_injective <| AddMonoidHom.ext_int h1

end AddEquiv

theorem eq_intCast' [AddGroupWithOne α] [FunLike F ℤ α] [AddMonoidHomClass F ℤ α]
    (f : F) (h₁ : f 1 = 1) :
    ∀ n : ℤ, f n = n :=
  DFunLike.ext_iff.1 <| (f : ℤ →+ α).eq_intCastAddHom h₁

/-- This version is primed so that the `RingHomClass` versions aren't. -/
theorem map_intCast' [AddGroupWithOne α] [AddGroupWithOne β] [FunLike F α β]
    [AddMonoidHomClass F α β] (f : F) (h₁ : f 1 = 1) : ∀ n : ℤ, f n = n :=
  eq_intCast' ((f : α →+ β).comp <| Int.castAddHom _) (by simpa)

@[simp]
theorem Int.castAddHom_int : Int.castAddHom ℤ = AddMonoidHom.id ℤ :=
  ((AddMonoidHom.id ℤ).eq_intCastAddHom rfl).symm

namespace MonoidHom

variable {M : Type*} [Monoid M]

@[ext]
theorem ext_mint {f g : Multiplicative ℤ →* M} (h1 : f (ofAdd 1) = g (ofAdd 1)) : f = g :=
  MonoidHom.toAdditiveRight.injective <| AddMonoidHom.ext_int <| Additive.toMul.injective h1

/-- If two `MonoidHom`s agree on `-1` and the naturals then they are equal. -/
@[ext]
theorem ext_int {f g : ℤ →* M} (h_neg_one : f (-1) = g (-1))
    (h_nat : f.comp Int.ofNatHom.toMonoidHom = g.comp Int.ofNatHom.toMonoidHom) : f = g := by
  ext (x | x)
  · exact (DFunLike.congr_fun h_nat x :)
  · rw [Int.negSucc_eq, ← neg_one_mul, f.map_mul, g.map_mul]
    congr 1
    exact mod_cast (DFunLike.congr_fun h_nat (x + 1) :)

end MonoidHom

namespace MonoidWithZeroHom

variable {M : Type*} [MonoidWithZero M]

/-- If two `MonoidWithZeroHom`s agree on `-1` and the naturals then they are equal. -/
@[ext]
theorem ext_int {f g : ℤ →*₀ M} (h_neg_one : f (-1) = g (-1))
    (h_nat : f.comp Int.ofNatHom.toMonoidWithZeroHom = g.comp Int.ofNatHom.toMonoidWithZeroHom) :
    f = g :=
  toMonoidHom_injective <| MonoidHom.ext_int h_neg_one <|
    MonoidHom.ext (DFunLike.congr_fun h_nat :)

end MonoidWithZeroHom

/-- If two `MonoidWithZeroHom`s agree on `-1` and the _positive_ naturals then they are equal. -/
theorem ext_int' [MonoidWithZero α] [FunLike F ℤ α] [MonoidWithZeroHomClass F ℤ α] {f g : F}
    (h_neg_one : f (-1) = g (-1)) (h_pos : ∀ n : ℕ, 0 < n → f n = g n) : f = g :=
  (DFunLike.ext _ _) fun n =>
    haveI :=
      DFunLike.congr_fun
        (@MonoidWithZeroHom.ext_int _ _ (f : ℤ →*₀ α) (g : ℤ →*₀ α) h_neg_one <|
          MonoidWithZeroHom.ext_nat (h_pos _))
        n
    this

section Group
variable (α) [Group α] (β) [AddGroup β]

/-- Additive homomorphisms from `ℤ` are defined by the image of `1`. -/
def zmultiplesHom : β ≃ (ℤ →+ β) where
  toFun x :=
  { toFun := fun n => n • x
    map_zero' := zero_zsmul x
    map_add' := fun _ _ => add_zsmul _ _ _ }
  invFun f := f 1
  left_inv := one_zsmul
  right_inv f := AddMonoidHom.ext_int <| one_zsmul (f 1)

/-- Monoid homomorphisms from `Multiplicative ℤ` are defined by the image
of `Multiplicative.ofAdd 1`. -/
def zpowersHom : α ≃ (Multiplicative ℤ →* α) :=
  ofMul.trans <| (zmultiplesHom _).trans <| AddMonoidHom.toMultiplicativeLeft

@[simp] lemma zmultiplesHom_apply (x : β) (n : ℤ) : zmultiplesHom β x n = n • x := rfl

@[simp] lemma zmultiplesHom_symm_apply (f : ℤ →+ β) : (zmultiplesHom β).symm f = f 1 := rfl

@[simp] lemma zpowersHom_apply (x : α) (n : Multiplicative ℤ) :
    zpowersHom α x n = x ^ n.toAdd := rfl

@[simp] lemma zpowersHom_symm_apply (f : Multiplicative ℤ →* α) :
    (zpowersHom α).symm f = f (ofAdd 1) := rfl

lemma MonoidHom.apply_mint (f : Multiplicative ℤ →* α) (n : Multiplicative ℤ) :
    f n = f (ofAdd 1) ^ n.toAdd := by
  rw [← zpowersHom_symm_apply, ← zpowersHom_apply, Equiv.apply_symm_apply]

lemma AddMonoidHom.apply_int (f : ℤ →+ β) (n : ℤ) : f n = n • f 1 := by
  rw [← zmultiplesHom_symm_apply, ← zmultiplesHom_apply, Equiv.apply_symm_apply]

end Group

section CommGroup
variable (α) [CommGroup α] (β) [AddCommGroup β]

/-- If `α` is commutative, `zmultiplesHom` is an additive equivalence. -/
def zmultiplesAddHom : β ≃+ (ℤ →+ β) :=
  { zmultiplesHom β with map_add' := fun a b => AddMonoidHom.ext fun n => by simp [zsmul_add] }

/-- If `α` is commutative, `zpowersHom` is a multiplicative equivalence. -/
def zpowersMulHom : α ≃* (Multiplicative ℤ →* α) :=
  { zpowersHom α with map_mul' := fun a b => MonoidHom.ext fun n => by simp [mul_zpow] }

variable {α}

@[simp]
lemma zpowersMulHom_apply (x : α) (n : Multiplicative ℤ) : zpowersMulHom α x n = x ^ n.toAdd := rfl

@[simp]
lemma zpowersMulHom_symm_apply (f : Multiplicative ℤ →* α) :
    (zpowersMulHom α).symm f = f (ofAdd 1) := rfl

@[simp] lemma zmultiplesAddHom_apply (x : β) (n : ℤ) : zmultiplesAddHom β x n = n • x := rfl

@[simp] lemma zmultiplesAddHom_symm_apply (f : ℤ →+ β) : (zmultiplesAddHom β).symm f = f 1 := rfl

end CommGroup

section NonAssocRing

variable [NonAssocRing α] [NonAssocRing β]

@[simp]
theorem eq_intCast [FunLike F ℤ α] [RingHomClass F ℤ α] (f : F) (n : ℤ) : f n = n :=
  eq_intCast' f (map_one _) n

@[simp]
theorem map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n : ℤ) : f n = n :=
  eq_intCast ((f : α →+* β).comp (Int.castRingHom α)) n

namespace RingHom

theorem eq_intCast' (f : ℤ →+* α) : f = Int.castRingHom α :=
  RingHom.ext <| eq_intCast f

theorem ext_int {R : Type*} [NonAssocSemiring R] (f g : ℤ →+* R) : f = g :=
  coe_addMonoidHom_injective <| AddMonoidHom.ext_int <| f.map_one.trans g.map_one.symm

instance Int.subsingleton_ringHom {R : Type*} [NonAssocSemiring R] : Subsingleton (ℤ →+* R) :=
  ⟨RingHom.ext_int⟩

end RingHom

end NonAssocRing

@[simp]
theorem Int.castRingHom_int : Int.castRingHom ℤ = RingHom.id ℤ :=
  (RingHom.id ℤ).eq_intCast'.symm
