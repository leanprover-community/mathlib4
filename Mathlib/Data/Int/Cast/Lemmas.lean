/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Ring.Hom.Basic
import Mathlib.Algebra.Ring.Int
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Commute

#align_import data.int.cast.lemmas from "leanprover-community/mathlib"@"acebd8d49928f6ed8920e502a6c90674e75bd441"

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

assert_not_exists OrderedCommMonoid

open Additive Function Multiplicative Nat

variable {F ι α β : Type*}

namespace Int

/-- Coercion `ℕ → ℤ` as a `RingHom`. -/
def ofNatHom : ℕ →+* ℤ :=
  Nat.castRingHom ℤ
#align int.of_nat_hom Int.ofNatHom

section cast

@[simp, norm_cast]
theorem cast_ite [AddGroupWithOne α] (P : Prop) [Decidable P] (m n : ℤ) :
    ((ite P m n : ℤ) : α) = ite P (m : α) (n : α) :=
  apply_ite _ _ _ _
#align int.cast_ite Int.cast_ite

/-- `coe : ℤ → α` as an `AddMonoidHom`. -/
def castAddHom (α : Type*) [AddGroupWithOne α] : ℤ →+ α where
  toFun := Int.cast
  map_zero' := cast_zero
  map_add' := cast_add
#align int.cast_add_hom Int.castAddHom

section AddGroupWithOne
variable [AddGroupWithOne α]

@[simp] lemma coe_castAddHom : ⇑(castAddHom α) = fun x : ℤ => (x : α) := rfl
#align int.coe_cast_add_hom Int.coe_castAddHom

lemma Even.intCast {n : ℤ} (h : Even n) : Even (n : α) := h.map (castAddHom α)

variable [CharZero α] {m n : ℤ}

@[simp] lemma cast_eq_zero : (n : α) = 0 ↔ n = 0 where
  mp h := by
    cases n
    · erw [Int.cast_natCast] at h
      exact congr_arg _ (Nat.cast_eq_zero.1 h)
    · rw [cast_negSucc, neg_eq_zero, Nat.cast_eq_zero] at h
      contradiction
  mpr h := by rw [h, cast_zero]
#align int.cast_eq_zero Int.cast_eq_zero

@[simp, norm_cast]
lemma cast_inj : (m : α) = n ↔ m = n := by rw [← sub_eq_zero, ← cast_sub, cast_eq_zero, sub_eq_zero]
#align int.cast_inj Int.cast_inj

lemma cast_injective : Injective (Int.cast : ℤ → α) := fun _ _ ↦ cast_inj.1
#align int.cast_injective Int.cast_injective

lemma cast_ne_zero : (n : α) ≠ 0 ↔ n ≠ 0 := not_congr cast_eq_zero
#align int.cast_ne_zero Int.cast_ne_zero

@[simp] lemma cast_eq_one : (n : α) = 1 ↔ n = 1 := by rw [← cast_one, cast_inj]
#align int.cast_eq_one Int.cast_eq_one

lemma cast_ne_one : (n : α) ≠ 1 ↔ n ≠ 1 := cast_eq_one.not
#align int.cast_ne_one Int.cast_ne_one

end AddGroupWithOne

section NonAssocRing
variable [NonAssocRing α] {a b : α} {n : ℤ}

variable (α) in
/-- `coe : ℤ → α` as a `RingHom`. -/
def castRingHom : ℤ →+* α where
  toFun := Int.cast
  map_zero' := cast_zero
  map_add' := cast_add
  map_one' := cast_one
  map_mul' := cast_mul
#align int.cast_ring_hom Int.castRingHom

@[simp] lemma coe_castRingHom : ⇑(castRingHom α) = fun x : ℤ ↦ (x : α) := rfl
#align int.coe_cast_ring_hom Int.coe_castRingHom

lemma cast_commute : ∀ (n : ℤ) (a : α), Commute ↑n a
  | (n : ℕ), x => by simpa using n.cast_commute x
  | -[n+1], x => by
    simpa only [cast_negSucc, Commute.neg_left_iff, Commute.neg_right_iff] using
      (n + 1).cast_commute (-x)
#align int.cast_commute Int.cast_commute

lemma cast_comm (n : ℤ) (x : α) : n * x = x * n := (cast_commute ..).eq
#align int.cast_comm Int.cast_comm

lemma commute_cast (a : α) (n : ℤ) : Commute a n := (cast_commute ..).symm
#align int.commute_cast Int.commute_cast

end NonAssocRing

section Ring
variable [Ring α]

@[simp] lemma _root_.zsmul_eq_mul (a : α) : ∀ n : ℤ, n • a = n * a
  | (n : ℕ) => by rw [natCast_zsmul, nsmul_eq_mul, Int.cast_natCast]
  | -[n+1] => by simp [Nat.cast_succ, neg_add_rev, Int.cast_negSucc, add_mul]
#align zsmul_eq_mul zsmul_eq_mul

lemma _root_.zsmul_eq_mul' (a : α) (n : ℤ) : n • a = a * n := by
  rw [zsmul_eq_mul, (n.cast_commute a).eq]
#align zsmul_eq_mul' zsmul_eq_mul'

lemma _root_.Odd.intCast {n : ℤ} (hn : Odd n) : Odd (n : α) :=
  hn.map (castRingHom α)

end Ring

theorem cast_dvd_cast [CommRing α] (m n : ℤ) (h : m ∣ n) : (m : α) ∣ (n : α) :=
  RingHom.map_dvd (Int.castRingHom α) h
#align int.cast_dvd Int.cast_dvd_cast

@[deprecated (since := "2024-05-25")] alias coe_int_dvd := cast_dvd_cast

end cast

end Int

open Int

namespace SemiconjBy
variable [Ring α] {a x y : α}

@[simp] lemma intCast_mul_right (h : SemiconjBy a x y) (n : ℤ) : SemiconjBy a (n * x) (n * y) :=
  SemiconjBy.mul_right (Int.commute_cast _ _) h
#align semiconj_by.cast_int_mul_right SemiconjBy.intCast_mul_right

@[simp] lemma intCast_mul_left (h : SemiconjBy a x y) (n : ℤ) : SemiconjBy (n * a) x y :=
  SemiconjBy.mul_left (Int.cast_commute _ _) h
#align semiconj_by.cast_int_mul_left SemiconjBy.intCast_mul_left

@[simp] lemma intCast_mul_intCast_mul (h : SemiconjBy a x y) (m n : ℤ) :
    SemiconjBy (m * a) (n * x) (n * y) := (h.intCast_mul_left m).intCast_mul_right n
#align semiconj_by.cast_int_mul_cast_int_mul SemiconjBy.intCast_mul_intCast_mul

@[deprecated (since := "2024-05-27")] alias cast_int_mul_right := intCast_mul_right
@[deprecated (since := "2024-05-27")] alias cast_int_mul_left := intCast_mul_left
@[deprecated (since := "2024-05-27")] alias cast_int_mul_cast_int_mul := intCast_mul_intCast_mul

end SemiconjBy

namespace Commute
section NonAssocRing
variable [NonAssocRing α] {a b : α} {n : ℤ}

@[simp] lemma intCast_left : Commute (n : α) a := Int.cast_commute _ _
#align commute.cast_int_left Commute.intCast_left

@[simp] lemma intCast_right : Commute a n := Int.commute_cast _ _
#align commute.cast_int_right Commute.intCast_right

@[deprecated (since := "2024-05-27")] alias cast_int_right := intCast_right
@[deprecated (since := "2024-05-27")] alias cast_int_left := intCast_left

end NonAssocRing

section Ring
variable [Ring α] {a b : α} {n : ℤ}

@[simp] lemma intCast_mul_right (h : Commute a b) (m : ℤ) : Commute a (m * b) :=
  SemiconjBy.intCast_mul_right h m
#align commute.cast_int_mul_right Commute.intCast_mul_right

@[simp] lemma intCast_mul_left (h : Commute a b) (m : ℤ) : Commute (m  * a) b :=
  SemiconjBy.intCast_mul_left h m
#align commute.cast_int_mul_left Commute.intCast_mul_left

lemma intCast_mul_intCast_mul (h : Commute a b) (m n : ℤ) : Commute (m * a) (n * b) :=
  SemiconjBy.intCast_mul_intCast_mul h m n
#align commute.cast_int_mul_cast_int_mul Commute.intCast_mul_intCast_mul

variable (a) (m n : ℤ)

/- Porting note (#10618): `simp` attribute removed as linter reports:
simp can prove this:
  by simp only [Commute.cast_int_right, Commute.refl, Commute.mul_right]
-/
-- @[simp]
lemma self_intCast_mul : Commute a (n * a : α) := (Commute.refl a).intCast_mul_right n
#align commute.self_cast_int_mul Commute.self_intCast_mul

/- Porting note (#10618): `simp` attribute removed as linter reports:
simp can prove this:
  by simp only [Commute.cast_int_left, Commute.refl, Commute.mul_left]
-/
-- @[simp]
lemma intCast_mul_self : Commute ((n : α) * a) a := (Commute.refl a).intCast_mul_left n
#align commute.cast_int_mul_self Commute.intCast_mul_self

lemma self_intCast_mul_intCast_mul : Commute (m * a : α) (n * a : α) :=
  (Commute.refl a).intCast_mul_intCast_mul m n
#align commute.self_cast_int_mul_cast_int_mul Commute.self_intCast_mul_intCast_mul

@[deprecated (since := "2024-05-27")] alias cast_int_mul_right := intCast_mul_right
@[deprecated (since := "2024-05-27")] alias cast_int_mul_left := intCast_mul_left
@[deprecated (since := "2024-05-27")] alias cast_int_mul_cast_int_mul := intCast_mul_intCast_mul
@[deprecated (since := "2024-05-27")] alias self_cast_int_mul := self_intCast_mul
@[deprecated (since := "2024-05-27")] alias cast_int_mul_self := intCast_mul_self
@[deprecated (since := "2024-05-27")]
alias self_cast_int_mul_cast_int_mul := self_intCast_mul_intCast_mul

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
#align add_monoid_hom.ext_int AddMonoidHom.ext_int

variable [AddGroupWithOne A]

theorem eq_intCastAddHom (f : ℤ →+ A) (h1 : f 1 = 1) : f = Int.castAddHom A :=
  ext_int <| by simp [h1]
#align add_monoid_hom.eq_int_cast_hom AddMonoidHom.eq_intCastAddHom

@[deprecated (since := "2024-04-17")]
alias eq_int_castAddHom := eq_intCastAddHom

end AddMonoidHom

theorem eq_intCast' [AddGroupWithOne α] [FunLike F ℤ α] [AddMonoidHomClass F ℤ α]
    (f : F) (h₁ : f 1 = 1) :
    ∀ n : ℤ, f n = n :=
  DFunLike.ext_iff.1 <| (f : ℤ →+ α).eq_intCastAddHom h₁
#align eq_int_cast' eq_intCast'

@[simp] lemma zsmul_one [AddGroupWithOne α] (n : ℤ) : n • (1 : α) = n := by cases n <;> simp
#align zsmul_one zsmul_one

@[simp]
theorem Int.castAddHom_int : Int.castAddHom ℤ = AddMonoidHom.id ℤ :=
  ((AddMonoidHom.id ℤ).eq_intCastAddHom rfl).symm
#align int.cast_add_hom_int Int.castAddHom_int

namespace MonoidHom

variable {M : Type*} [Monoid M]

open Multiplicative

@[ext]
theorem ext_mint {f g : Multiplicative ℤ →* M} (h1 : f (ofAdd 1) = g (ofAdd 1)) : f = g :=
  MonoidHom.toAdditive''.injective <| AddMonoidHom.ext_int <| Additive.toMul.injective h1
#align monoid_hom.ext_mint MonoidHom.ext_mint

/-- If two `MonoidHom`s agree on `-1` and the naturals then they are equal. -/
@[ext]
theorem ext_int {f g : ℤ →* M} (h_neg_one : f (-1) = g (-1))
    (h_nat : f.comp Int.ofNatHom.toMonoidHom = g.comp Int.ofNatHom.toMonoidHom) : f = g := by
  ext (x | x)
  · exact (DFunLike.congr_fun h_nat x : _)
  · rw [Int.negSucc_eq, ← neg_one_mul, f.map_mul, g.map_mul]
    congr 1
    exact mod_cast (DFunLike.congr_fun h_nat (x + 1) : _)
#align monoid_hom.ext_int MonoidHom.ext_int

end MonoidHom

namespace MonoidWithZeroHom

variable {M : Type*} [MonoidWithZero M]

/-- If two `MonoidWithZeroHom`s agree on `-1` and the naturals then they are equal. -/
@[ext]
theorem ext_int {f g : ℤ →*₀ M} (h_neg_one : f (-1) = g (-1))
    (h_nat : f.comp Int.ofNatHom.toMonoidWithZeroHom = g.comp Int.ofNatHom.toMonoidWithZeroHom) :
    f = g :=
  toMonoidHom_injective <| MonoidHom.ext_int h_neg_one <|
    MonoidHom.ext (DFunLike.congr_fun h_nat : _)
#align monoid_with_zero_hom.ext_int MonoidWithZeroHom.ext_int

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
#align ext_int' ext_int'

section Group
variable (α) [Group α] [AddGroup α]

/-- Additive homomorphisms from `ℤ` are defined by the image of `1`. -/
def zmultiplesHom : α ≃ (ℤ →+ α) where
  toFun x :=
  { toFun := fun n => n • x
    map_zero' := zero_zsmul x
    map_add' := fun _ _ => add_zsmul _ _ _ }
  invFun f := f 1
  left_inv := one_zsmul
  right_inv f := AddMonoidHom.ext_int <| one_zsmul (f 1)
#align zmultiples_hom zmultiplesHom
#align powers_hom powersHom

/-- Monoid homomorphisms from `Multiplicative ℤ` are defined by the image
of `Multiplicative.ofAdd 1`. -/
@[to_additive existing]
def zpowersHom : α ≃ (Multiplicative ℤ →* α) :=
  ofMul.trans <| (zmultiplesHom _).trans <| AddMonoidHom.toMultiplicative''
#align zpowers_hom zpowersHom

lemma zmultiplesHom_apply (x : α) (n : ℤ) : zmultiplesHom α x n = n • x := rfl
#align zmultiples_hom_apply zmultiplesHom_apply

lemma zmultiplesHom_symm_apply (f : ℤ →+ α) : (zmultiplesHom α).symm f = f 1 := rfl
#align zmultiples_hom_symm_apply zmultiplesHom_symm_apply

@[to_additive existing (attr := simp)]
lemma zpowersHom_apply (x : α) (n : Multiplicative ℤ) : zpowersHom α x n = x ^ toAdd n := rfl
#align zpowers_hom_apply zpowersHom_apply

@[to_additive existing (attr := simp)]
lemma zpowersHom_symm_apply (f : Multiplicative ℤ →* α) :
    (zpowersHom α).symm f = f (ofAdd 1) := rfl
#align zpowers_hom_symm_apply zpowersHom_symm_apply

lemma MonoidHom.apply_mint (f : Multiplicative ℤ →* α) (n : Multiplicative ℤ) :
    f n = f (ofAdd 1) ^ (toAdd n) := by
  rw [← zpowersHom_symm_apply, ← zpowersHom_apply, Equiv.apply_symm_apply]
#align monoid_hom.apply_mint MonoidHom.apply_mint

lemma AddMonoidHom.apply_int (f : ℤ →+ α) (n : ℤ) : f n = n • f 1 := by
  rw [← zmultiplesHom_symm_apply, ← zmultiplesHom_apply, Equiv.apply_symm_apply]
#align add_monoid_hom.apply_int AddMonoidHom.apply_int

end Group

section CommGroup
variable (α) [CommGroup α] [AddCommGroup α]

/-- If `α` is commutative, `zmultiplesHom` is an additive equivalence. -/
def zmultiplesAddHom : α ≃+ (ℤ →+ α) :=
  { zmultiplesHom α with map_add' := fun a b => AddMonoidHom.ext fun n => by simp [zsmul_add] }
#align zmultiples_add_hom zmultiplesAddHom

/-- If `α` is commutative, `zpowersHom` is a multiplicative equivalence. -/
def zpowersMulHom : α ≃* (Multiplicative ℤ →* α) :=
  { zpowersHom α with map_mul' := fun a b => MonoidHom.ext fun n => by simp [mul_zpow] }
#align zpowers_mul_hom zpowersMulHom

variable {α}

@[simp]
lemma zpowersMulHom_apply (x : α) (n : Multiplicative ℤ) : zpowersMulHom α x n = x ^ toAdd n := rfl
#align zpowers_mul_hom_apply zpowersMulHom_apply

@[simp]
lemma zpowersMulHom_symm_apply (f : Multiplicative ℤ →* α) :
    (zpowersMulHom α).symm f = f (ofAdd 1) := rfl
#align zpowers_mul_hom_symm_apply zpowersMulHom_symm_apply

@[simp] lemma zmultiplesAddHom_apply (x : α) (n : ℤ) : zmultiplesAddHom α x n = n • x := rfl
#align zmultiples_add_hom_apply zmultiplesAddHom_apply

@[simp] lemma zmultiplesAddHom_symm_apply (f : ℤ →+ α) : (zmultiplesAddHom α).symm f = f 1 := rfl
#align zmultiples_add_hom_symm_apply zmultiplesAddHom_symm_apply

end CommGroup

section NonAssocRing

variable [NonAssocRing α] [NonAssocRing β]

@[simp]
theorem eq_intCast [FunLike F ℤ α] [RingHomClass F ℤ α] (f : F) (n : ℤ) : f n = n :=
  eq_intCast' f (map_one _) n
#align eq_int_cast eq_intCast

@[simp]
theorem map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n : ℤ) : f n = n :=
  eq_intCast ((f : α →+* β).comp (Int.castRingHom α)) n
#align map_int_cast map_intCast

namespace RingHom

theorem eq_intCast' (f : ℤ →+* α) : f = Int.castRingHom α :=
  RingHom.ext <| eq_intCast f
#align ring_hom.eq_int_cast' RingHom.eq_intCast'

theorem ext_int {R : Type*} [NonAssocSemiring R] (f g : ℤ →+* R) : f = g :=
  coe_addMonoidHom_injective <| AddMonoidHom.ext_int <| f.map_one.trans g.map_one.symm
#align ring_hom.ext_int RingHom.ext_int

instance Int.subsingleton_ringHom {R : Type*} [NonAssocSemiring R] : Subsingleton (ℤ →+* R) :=
  ⟨RingHom.ext_int⟩
#align ring_hom.int.subsingleton_ring_hom RingHom.Int.subsingleton_ringHom

end RingHom

end NonAssocRing

#align int.cast_id Int.cast_idₓ -- dubious translation, type involves HasLiftT?

@[simp]
theorem Int.castRingHom_int : Int.castRingHom ℤ = RingHom.id ℤ :=
  (RingHom.id ℤ).eq_intCast'.symm
#align int.cast_ring_hom_int Int.castRingHom_int

namespace Pi

variable {π : ι → Type*} [∀ i, IntCast (π i)]

instance instIntCast : IntCast (∀ i, π i) where intCast n _ := n

theorem intCast_apply (n : ℤ) (i : ι) : (n : ∀ i, π i) i = n :=
  rfl
#align pi.int_apply Pi.intCast_apply

@[simp]
theorem intCast_def (n : ℤ) : (n : ∀ i, π i) = fun _ => ↑n :=
  rfl
#align pi.coe_int Pi.intCast_def

-- 2024-04-05
@[deprecated] alias int_apply := intCast_apply
@[deprecated] alias coe_int := intCast_def

end Pi

theorem Sum.elim_intCast_intCast {α β γ : Type*} [IntCast γ] (n : ℤ) :
    Sum.elim (n : α → γ) (n : β → γ) = n :=
  Sum.elim_lam_const_lam_const (γ := γ) n
#align sum.elim_int_cast_int_cast Sum.elim_intCast_intCast
