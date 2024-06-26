/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Rat.Lemmas

#align_import data.rat.cast from "leanprover-community/mathlib"@"acebd8d49928f6ed8920e502a6c90674e75bd441"


/-!
# Casts for Rational Numbers

## Summary

We define the canonical injection from ℚ into an arbitrary division ring and prove various
casting lemmas showing the well-behavedness of this injection.

## Notations

- `/.` is infix notation for `Rat.divInt`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, cast, coercion, casting
-/

variable {F ι α β : Type*}

namespace NNRat
variable [DivisionSemiring α] {q r : ℚ≥0}

@[simp, norm_cast] lemma cast_natCast (n : ℕ) : ((n : ℚ≥0) : α) = n := by simp [cast_def]

-- See note [no_index around OfNat.ofNat]
@[simp, norm_cast] lemma cast_ofNat (n : ℕ) [n.AtLeastTwo] :
    no_index (OfNat.ofNat n : ℚ≥0) = (OfNat.ofNat n : α) := cast_natCast _

@[simp, norm_cast] lemma cast_zero : ((0 : ℚ≥0) : α) = 0 := (cast_natCast _).trans Nat.cast_zero
@[simp, norm_cast] lemma cast_one : ((1 : ℚ≥0) : α) = 1 := (cast_natCast _).trans Nat.cast_one

lemma cast_commute (q : ℚ≥0) (a : α) : Commute (↑q) a := by
  simpa only [cast_def] using (q.num.cast_commute a).div_left (q.den.cast_commute a)

lemma commute_cast (a : α) (q : ℚ≥0) : Commute a q := (cast_commute ..).symm

lemma cast_comm (q : ℚ≥0) (a : α) : q * a = a * q := cast_commute _ _

@[norm_cast] lemma cast_divNat_of_ne_zero (a : ℕ) {b : ℕ} (hb : (b : α) ≠ 0) :
    divNat a b = (a / b : α) := by
  rcases e : divNat a b with ⟨⟨n, d, h, c⟩, hn⟩
  rw [← Rat.num_nonneg] at hn
  lift n to ℕ using hn
  have hd : (d : α) ≠ 0 := by
    refine fun hd ↦ hb ?_
    have : Rat.divInt a b = _ := congr_arg NNRat.cast e
    obtain ⟨k, rfl⟩ : d ∣ b := by simpa [Int.natCast_dvd_natCast, this] using Rat.den_dvd a b
    simp [*]
  have hb' : b ≠ 0 := by rintro rfl; exact hb Nat.cast_zero
  have hd' : d ≠ 0 := by rintro rfl; exact hd Nat.cast_zero
  simp_rw [Rat.mk'_eq_divInt, mk_divInt, divNat_inj hb' hd'] at e
  rw [cast_def]
  dsimp
  rw [Commute.div_eq_div_iff _ hd hb]
  · norm_cast
    rw [e]
  exact b.commute_cast _

@[norm_cast]
lemma cast_add_of_ne_zero (hq : (q.den : α) ≠ 0) (hr : (r.den : α) ≠ 0) :
    ↑(q + r) = (q + r : α) := by
  rw [add_def, cast_divNat_of_ne_zero, cast_def, cast_def, mul_comm _ q.den,
    (Nat.commute_cast _ _).div_add_div (Nat.commute_cast _ _) hq hr]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hq hr

@[norm_cast]
lemma cast_mul_of_ne_zero (hq : (q.den : α) ≠ 0) (hr : (r.den : α) ≠ 0) :
    ↑(q * r) = (q * r : α) := by
  rw [mul_def, cast_divNat_of_ne_zero, cast_def, cast_def,
    (Nat.commute_cast _ _).div_mul_div_comm (Nat.commute_cast _ _)]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hq hr

@[norm_cast]
lemma cast_inv_of_ne_zero (hq : (q.num : α) ≠ 0) : (q⁻¹ : ℚ≥0) = (q⁻¹ : α) := by
  rw [inv_def, cast_divNat_of_ne_zero _ hq, cast_def, inv_div]

@[norm_cast]
lemma cast_div_of_ne_zero (hq : (q.den : α) ≠ 0) (hr : (r.num : α) ≠ 0) :
    ↑(q / r) = (q / r : α) := by
  rw [div_def, cast_divNat_of_ne_zero, cast_def, cast_def, div_eq_mul_inv (_ / _),
    inv_div, (Nat.commute_cast _ _).div_mul_div_comm (Nat.commute_cast _ _)]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hq hr

end NNRat

namespace Rat

variable [DivisionRing α] {p q : ℚ}

@[simp, norm_cast]
theorem cast_intCast (n : ℤ) : ((n : ℚ) : α) = n :=
  (cast_def _).trans <| show (n / (1 : ℕ) : α) = n by rw [Nat.cast_one, div_one]
#align rat.cast_coe_int Rat.cast_intCast

@[simp, norm_cast]
theorem cast_natCast (n : ℕ) : ((n : ℚ) : α) = n := by
  rw [← Int.cast_natCast, cast_intCast, Int.cast_natCast]
#align rat.cast_coe_nat Rat.cast_natCast

@[deprecated (since := "2024-03-21")] alias cast_coe_int := cast_intCast
@[deprecated (since := "2024-03-21")] alias cast_coe_nat := cast_natCast

-- See note [no_index around OfNat.ofNat]
@[simp, norm_cast] lemma cast_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((no_index (OfNat.ofNat n : ℚ)) : α) = (OfNat.ofNat n : α) := by
  simp [cast_def]

@[simp, norm_cast]
theorem cast_zero : ((0 : ℚ) : α) = 0 :=
  (cast_intCast _).trans Int.cast_zero
#align rat.cast_zero Rat.cast_zero

@[simp, norm_cast]
theorem cast_one : ((1 : ℚ) : α) = 1 :=
  (cast_intCast _).trans Int.cast_one
#align rat.cast_one Rat.cast_one

theorem cast_commute (r : ℚ) (a : α) : Commute (↑r) a := by
  simpa only [cast_def] using (r.1.cast_commute a).div_left (r.2.cast_commute a)
#align rat.cast_commute Rat.cast_commute

theorem cast_comm (r : ℚ) (a : α) : (r : α) * a = a * r :=
  (cast_commute r a).eq
#align rat.cast_comm Rat.cast_comm

theorem commute_cast (a : α) (r : ℚ) : Commute a r :=
  (r.cast_commute a).symm
#align rat.commute_cast Rat.commute_cast

@[norm_cast]
lemma cast_divInt_of_ne_zero (a : ℤ) {b : ℤ} (b0 : (b : α) ≠ 0) : (a /. b : α) = a / b := by
  have b0' : b ≠ 0 := by
    refine mt ?_ b0
    simp (config := { contextual := true })
  cases' e : a /. b with n d h c
  have d0 : (d : α) ≠ 0 := by
    intro d0
    have dd := den_dvd a b
    cases' show (d : ℤ) ∣ b by rwa [e] at dd with k ke
    have : (b : α) = (d : α) * (k : α) := by rw [ke, Int.cast_mul, Int.cast_natCast]
    rw [d0, zero_mul] at this
    contradiction
  rw [mk'_eq_divInt] at e
  have := congr_arg ((↑) : ℤ → α)
    ((divInt_eq_iff b0' <| ne_of_gt <| Int.natCast_pos.2 h.bot_lt).1 e)
  rw [Int.cast_mul, Int.cast_mul, Int.cast_natCast] at this
  rw [eq_comm, cast_def, div_eq_mul_inv, eq_div_iff_mul_eq d0, mul_assoc, (d.commute_cast _).eq,
    ← mul_assoc, this, mul_assoc, mul_inv_cancel b0, mul_one]
#align rat.cast_mk_of_ne_zero Rat.cast_divInt_of_ne_zero

@[norm_cast]
lemma cast_mkRat_of_ne_zero (a : ℤ) {b : ℕ} (hb : (b : α) ≠ 0) : (mkRat a b : α) = a / b := by
  rw [Rat.mkRat_eq_divInt, cast_divInt_of_ne_zero, Int.cast_natCast]; rwa [Int.cast_natCast]

@[norm_cast]
lemma cast_add_of_ne_zero {q r : ℚ} (hq : (q.den : α) ≠ 0) (hr : (r.den : α) ≠ 0) :
    (q + r : ℚ) = (q + r : α) := by
  rw [add_def', cast_mkRat_of_ne_zero, cast_def, cast_def, mul_comm r.num,
    (Nat.cast_commute _ _).div_add_div (Nat.commute_cast _ _) hq hr]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hq hr
#align rat.cast_add_of_ne_zero Rat.cast_add_of_ne_zero

@[simp, norm_cast] lemma cast_neg (q : ℚ) : ↑(-q) = (-q : α) := by simp [cast_def, neg_div]
#align rat.cast_neg Rat.cast_neg

@[norm_cast] lemma cast_sub_of_ne_zero (hp : (p.den : α) ≠ 0) (hq : (q.den : α) ≠ 0) :
    ↑(p - q) = (p - q : α) := by simp [sub_eq_add_neg, cast_add_of_ne_zero, hp, hq]
#align rat.cast_sub_of_ne_zero Rat.cast_sub_of_ne_zero

@[norm_cast] lemma cast_mul_of_ne_zero (hp : (p.den : α) ≠ 0) (hq : (q.den : α) ≠ 0) :
    ↑(p * q) = (p * q : α) := by
  rw [mul_eq_mkRat, cast_mkRat_of_ne_zero, cast_def, cast_def,
    (Nat.commute_cast _ _).div_mul_div_comm (Int.commute_cast _ _)]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hp hq
#align rat.cast_mul_of_ne_zero Rat.cast_mul_of_ne_zero

@[norm_cast]
lemma cast_inv_of_ne_zero (hq : (q.num : α) ≠ 0) : ↑(q⁻¹) = (q⁻¹ : α) := by
  rw [inv_def', cast_divInt_of_ne_zero _ hq, cast_def, inv_div, Int.cast_natCast]
#align rat.cast_inv_of_ne_zero Rat.cast_inv_of_ne_zero

@[norm_cast] lemma cast_div_of_ne_zero (hp : (p.den : α) ≠ 0) (hq : (q.num : α) ≠ 0) :
    ↑(p / q) = (p / q : α) := by
  rw [div_def', cast_divInt_of_ne_zero, cast_def, cast_def, div_eq_mul_inv (_ / _), inv_div,
    (Int.commute_cast _ _).div_mul_div_comm (Nat.commute_cast _ _)]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hp hq
#align rat.cast_div_of_ne_zero Rat.cast_div_of_ne_zero

end Rat

open Rat

variable [FunLike F α β]

@[simp] lemma map_nnratCast [DivisionSemiring α] [DivisionSemiring β] [RingHomClass F α β] (f : F)
    (q : ℚ≥0) : f q = q := by simp_rw [NNRat.cast_def, map_div₀, map_natCast]

@[simp]
lemma eq_nnratCast [DivisionSemiring α] [FunLike F ℚ≥0 α] [RingHomClass F ℚ≥0 α] (f : F) (q : ℚ≥0) :
    f q = q := by rw [← map_nnratCast f, NNRat.cast_id]

@[simp]
theorem map_ratCast [DivisionRing α] [DivisionRing β] [RingHomClass F α β] (f : F) (q : ℚ) :
    f q = q := by rw [cast_def, map_div₀, map_intCast, map_natCast, cast_def]
#align map_rat_cast map_ratCast

@[simp] lemma eq_ratCast [DivisionRing α] [FunLike F ℚ α] [RingHomClass F ℚ α] (f : F) (q : ℚ) :
    f q = q := by rw [← map_ratCast f, Rat.cast_id]
#align eq_rat_cast eq_ratCast

namespace MonoidWithZeroHom

variable {M₀ : Type*} [MonoidWithZero M₀] [FunLike F ℚ M₀] [MonoidWithZeroHomClass F ℚ M₀]
variable {f g : F}

/-- If `f` and `g` agree on the integers then they are equal `φ`. -/
theorem ext_rat' (h : ∀ m : ℤ, f m = g m) : f = g :=
  (DFunLike.ext f g) fun r => by
    rw [← r.num_div_den, div_eq_mul_inv, map_mul, map_mul, h, ← Int.cast_natCast,
      eq_on_inv₀ f g]
    apply h
#align monoid_with_zero_hom.ext_rat' MonoidWithZeroHom.ext_rat'

/-- If `f` and `g` agree on the integers then they are equal `φ`.

See note [partially-applied ext lemmas] for why `comp` is used here. -/
@[ext]
theorem ext_rat {f g : ℚ →*₀ M₀}
    (h : f.comp (Int.castRingHom ℚ : ℤ →*₀ ℚ) = g.comp (Int.castRingHom ℚ)) : f = g :=
  ext_rat' <| DFunLike.congr_fun h
#align monoid_with_zero_hom.ext_rat MonoidWithZeroHom.ext_rat

/-- Positive integer values of a morphism `φ` and its value on `-1` completely determine `φ`. -/
theorem ext_rat_on_pnat (same_on_neg_one : f (-1) = g (-1))
    (same_on_pnat : ∀ n : ℕ, 0 < n → f n = g n) : f = g :=
  ext_rat' <|
    DFunLike.congr_fun <|
      show
        (f : ℚ →*₀ M₀).comp (Int.castRingHom ℚ : ℤ →*₀ ℚ) =
          (g : ℚ →*₀ M₀).comp (Int.castRingHom ℚ : ℤ →*₀ ℚ)
        from ext_int' (by simpa) (by simpa)
#align monoid_with_zero_hom.ext_rat_on_pnat MonoidWithZeroHom.ext_rat_on_pnat

end MonoidWithZeroHom

/-- Any two ring homomorphisms from `ℚ` to a semiring are equal. If the codomain is a division ring,
then this lemma follows from `eq_ratCast`. -/
theorem RingHom.ext_rat {R : Type*} [Semiring R] [FunLike F ℚ R] [RingHomClass F ℚ R] (f g : F) :
    f = g :=
  MonoidWithZeroHom.ext_rat' <|
    RingHom.congr_fun <|
      ((f : ℚ →+* R).comp (Int.castRingHom ℚ)).ext_int ((g : ℚ →+* R).comp (Int.castRingHom ℚ))
#align ring_hom.ext_rat RingHom.ext_rat

instance Rat.subsingleton_ringHom {R : Type*} [Semiring R] : Subsingleton (ℚ →+* R) :=
  ⟨RingHom.ext_rat⟩
#align rat.subsingleton_ring_hom Rat.subsingleton_ringHom

/-! ### Scalar multiplication -/

namespace NNRat
variable [DivisionSemiring α]

instance (priority := 100) instDistribSMul : DistribSMul ℚ≥0 α where
  smul_zero a := by rw [smul_def, mul_zero]
  smul_add a x y := by rw [smul_def, smul_def, smul_def, mul_add]

instance instIsScalarTowerRight : IsScalarTower ℚ≥0 α α where
  smul_assoc a x y := by simp only [smul_def, smul_eq_mul, mul_assoc]

end NNRat

namespace Rat
variable [DivisionRing α]

instance (priority := 100) instDistribSMul : DistribSMul ℚ α where
  smul_zero a := by rw [smul_def, mul_zero]
  smul_add a x y := by rw [smul_def, smul_def, smul_def, mul_add]
#align rat.distrib_smul Rat.instDistribSMul

instance instIsScalarTowerRight : IsScalarTower ℚ α α where
  smul_assoc a x y := by simp only [smul_def, smul_eq_mul, mul_assoc]
#align rat.is_scalar_tower_right Rat.instIsScalarTowerRight

end Rat
