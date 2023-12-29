/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Rat.Lemmas

#align_import data.rat.cast from "leanprover-community/mathlib"@"acebd8d49928f6ed8920e502a6c90674e75bd441"


/-!
# Casts for Rational Numbers

## Summary

We define the canonical injection from ℚ into an arbitrary division ring and prove various
casting lemmas showing the well-behavedness of this injection.

## Notations

- `/.` is infix notation for `rat.mk`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, cast, coercion, casting
-/


variable {F ι α β : Type*}

namespace Rat

open Rat

section WithDivRing

variable [DivisionRing α]

@[simp, norm_cast]
theorem cast_coe_int (n : ℤ) : ((n : ℚ) : α) = n :=
  (cast_def _).trans <| show (n / (1 : ℕ) : α) = n by rw [Nat.cast_one, div_one]
#align rat.cast_coe_int Rat.cast_coe_int

@[simp, norm_cast]
theorem cast_coe_nat (n : ℕ) : ((n : ℚ) : α) = n := by
  rw [← Int.cast_ofNat, cast_coe_int, Int.cast_ofNat]
#align rat.cast_coe_nat Rat.cast_coe_nat

-- See note [no_index around OfNat.ofNat]
@[simp, norm_cast] lemma cast_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((no_index (OfNat.ofNat n : ℚ)) : α) = (OfNat.ofNat n : α) := by
  simp [cast_def]

@[simp, norm_cast]
theorem cast_zero : ((0 : ℚ) : α) = 0 :=
  (cast_coe_int _).trans Int.cast_zero
#align rat.cast_zero Rat.cast_zero

@[simp, norm_cast]
theorem cast_one : ((1 : ℚ) : α) = 1 :=
  (cast_coe_int _).trans Int.cast_one
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
theorem cast_mk_of_ne_zero (a b : ℤ) (b0 : (b : α) ≠ 0) : (a /. b : α) = a / b := by
  have b0' : b ≠ 0 := by
    refine' mt _ b0
    simp (config := { contextual := true })
  cases' e : a /. b with n d h c
  have d0 : (d : α) ≠ 0 := by
    intro d0
    have dd := den_dvd a b
    cases' show (d : ℤ) ∣ b by rwa [e] at dd with k ke
    have : (b : α) = (d : α) * (k : α) := by rw [ke, Int.cast_mul, Int.cast_ofNat]
    rw [d0, zero_mul] at this
    contradiction
  rw [num_den'] at e
  have := congr_arg ((↑) : ℤ → α)
    ((divInt_eq_iff b0' <| ne_of_gt <| Int.coe_nat_pos.2 h.bot_lt).1 e)
  rw [Int.cast_mul, Int.cast_mul, Int.cast_ofNat] at this
  -- Porting note: was `symm`
  apply Eq.symm
  rw [cast_def, div_eq_mul_inv, eq_div_iff_mul_eq d0, mul_assoc, (d.commute_cast _).eq, ← mul_assoc,
    this, mul_assoc, mul_inv_cancel b0, mul_one]
#align rat.cast_mk_of_ne_zero Rat.cast_mk_of_ne_zero

@[norm_cast]
theorem cast_add_of_ne_zero :
    ∀ {m n : ℚ}, (m.den : α) ≠ 0 → (n.den : α) ≠ 0 → ((m + n : ℚ) : α) = m + n
  | ⟨n₁, d₁, h₁, c₁⟩, ⟨n₂, d₂, h₂, c₂⟩ => fun (d₁0 : (d₁ : α) ≠ 0) (d₂0 : (d₂ : α) ≠ 0) => by
    have d₁0' : (d₁ : ℤ) ≠ 0 :=
      Int.coe_nat_ne_zero.2 fun e => by rw [e] at d₁0; exact d₁0 Nat.cast_zero
    have d₂0' : (d₂ : ℤ) ≠ 0 :=
      Int.coe_nat_ne_zero.2 fun e => by rw [e] at d₂0; exact d₂0 Nat.cast_zero
    rw [num_den', num_den', add_def'' d₁0' d₂0']
    suffices (n₁ * (d₂ * ((d₂ : α)⁻¹ * (d₁ : α)⁻¹)) + n₂ * (d₁ * (d₂ : α)⁻¹) * (d₁ : α)⁻¹ : α)
        = n₁ * (d₁ : α)⁻¹ + n₂ * (d₂ : α)⁻¹ by
      rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero, cast_mk_of_ne_zero]
      · simpa [division_def, left_distrib, right_distrib, mul_inv_rev, d₁0, d₂0, mul_assoc]
      all_goals simp [d₁0, d₂0]
    rw [← mul_assoc (d₂ : α), mul_inv_cancel d₂0, one_mul, (Nat.cast_commute _ _).eq]
    simp [d₁0, mul_assoc]
#align rat.cast_add_of_ne_zero Rat.cast_add_of_ne_zero

@[simp, norm_cast]
theorem cast_neg : ∀ n, ((-n : ℚ) : α) = -n
  | ⟨n, d, h, c⟩ => by
    simpa only [cast_def] using
      show (↑(-n) / d : α) = -(n / d) by
        rw [div_eq_mul_inv, div_eq_mul_inv, Int.cast_neg, neg_mul_eq_neg_mul]
#align rat.cast_neg Rat.cast_neg

@[norm_cast]
theorem cast_sub_of_ne_zero {m n : ℚ} (m0 : (m.den : α) ≠ 0) (n0 : (n.den : α) ≠ 0) :
    ((m - n : ℚ) : α) = m - n := by
  have : ((-n).den : α) ≠ 0 := by cases n; exact n0
  simp [sub_eq_add_neg, cast_add_of_ne_zero m0 this]
#align rat.cast_sub_of_ne_zero Rat.cast_sub_of_ne_zero

@[norm_cast]
theorem cast_mul_of_ne_zero :
    ∀ {m n : ℚ}, (m.den : α) ≠ 0 → (n.den : α) ≠ 0 → ((m * n : ℚ) : α) = m * n
  | ⟨n₁, d₁, h₁, c₁⟩, ⟨n₂, d₂, h₂, c₂⟩ => fun (d₁0 : (d₁ : α) ≠ 0) (d₂0 : (d₂ : α) ≠ 0) => by
    have d₁0' : (d₁ : ℤ) ≠ 0 :=
      Int.coe_nat_ne_zero.2 fun e => by rw [e] at d₁0; exact d₁0 Nat.cast_zero
    have d₂0' : (d₂ : ℤ) ≠ 0 :=
      Int.coe_nat_ne_zero.2 fun e => by rw [e] at d₂0; exact d₂0 Nat.cast_zero
    rw [num_den', num_den', mul_def' d₁0' d₂0']
    suffices (n₁ * (n₂ * (d₂ : α)⁻¹ * (d₁ : α)⁻¹) : α) = n₁ * ((d₁ : α)⁻¹ * (n₂ * (d₂ : α)⁻¹)) by
      rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero, cast_mk_of_ne_zero]
      · simpa [division_def, mul_inv_rev, d₁0, d₂0, mul_assoc]
      all_goals simp [d₁0, d₂0]
    rw [(d₁.commute_cast (_ : α)).inv_right₀.eq]
#align rat.cast_mul_of_ne_zero Rat.cast_mul_of_ne_zero

@[norm_cast]
theorem cast_inv_of_ne_zero :
    ∀ {n : ℚ}, (n.num : α) ≠ 0 → (n.den : α) ≠ 0 → ((n⁻¹ : ℚ) : α) = (n : α)⁻¹
  | ⟨n, d, h, c⟩ => fun (n0 : (n : α) ≠ 0) (d0 : (d : α) ≠ 0) => by
    rw [num_den', inv_def']
    rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero, inv_div] <;> simp [n0, d0]
#align rat.cast_inv_of_ne_zero Rat.cast_inv_of_ne_zero

@[norm_cast]
theorem cast_div_of_ne_zero {m n : ℚ} (md : (m.den : α) ≠ 0) (nn : (n.num : α) ≠ 0)
    (nd : (n.den : α) ≠ 0) : ((m / n : ℚ) : α) = m / n := by
  have : (n⁻¹.den : ℤ) ∣ n.num := by
    conv in n⁻¹.den => rw [← @num_den n, inv_def']
    apply den_dvd
  have : (n⁻¹.den : α) = 0 → (n.num : α) = 0 := fun h => by
    let ⟨k, e⟩ := this
    have := congr_arg ((↑) : ℤ → α) e; rwa [Int.cast_mul, Int.cast_ofNat, h, zero_mul] at this
  rw [division_def, cast_mul_of_ne_zero md (mt this nn), cast_inv_of_ne_zero nn nd, division_def]
#align rat.cast_div_of_ne_zero Rat.cast_div_of_ne_zero

end WithDivRing

-- Porting note: statement made more explicit
@[norm_cast]
theorem cast_id (n : ℚ) : Rat.cast n = n := rfl
#align rat.cast_id Rat.cast_id

@[simp]
theorem cast_eq_id : ((↑) : ℚ → ℚ) = id :=
  funext fun _ => rfl
#align rat.cast_eq_id Rat.cast_eq_id

end Rat

open Rat

@[simp]
theorem map_ratCast [DivisionRing α] [DivisionRing β] [RingHomClass F α β] (f : F) (q : ℚ) :
    f q = q := by rw [cast_def, map_div₀, map_intCast, map_natCast, cast_def]
#align map_rat_cast map_ratCast

@[simp]
theorem eq_ratCast {k} [DivisionRing k] [RingHomClass F ℚ k] (f : F) (r : ℚ) : f r = r := by
  rw [← map_ratCast f, Rat.cast_id]
#align eq_rat_cast eq_ratCast

namespace MonoidWithZeroHom

variable {M₀ : Type*} [MonoidWithZero M₀] [MonoidWithZeroHomClass F ℚ M₀] {f g : F}


/-- If `f` and `g` agree on the integers then they are equal `φ`. -/
theorem ext_rat' (h : ∀ m : ℤ, f m = g m) : f = g :=
  (FunLike.ext f g) fun r => by
    rw [← r.num_div_den, div_eq_mul_inv, map_mul, map_mul, h, ← Int.cast_ofNat,
      eq_on_inv₀ f g]
    apply h
#align monoid_with_zero_hom.ext_rat' MonoidWithZeroHom.ext_rat'

/-- If `f` and `g` agree on the integers then they are equal `φ`.

See note [partially-applied ext lemmas] for why `comp` is used here. -/
@[ext]
theorem ext_rat {f g : ℚ →*₀ M₀}
    (h : f.comp (Int.castRingHom ℚ : ℤ →*₀ ℚ) = g.comp (Int.castRingHom ℚ)) : f = g :=
  ext_rat' <| FunLike.congr_fun h
#align monoid_with_zero_hom.ext_rat MonoidWithZeroHom.ext_rat

/-- Positive integer values of a morphism `φ` and its value on `-1` completely determine `φ`. -/
theorem ext_rat_on_pnat (same_on_neg_one : f (-1) = g (-1))
    (same_on_pnat : ∀ n : ℕ, 0 < n → f n = g n) : f = g :=
  ext_rat' <|
    FunLike.congr_fun <|
      show
        (f : ℚ →*₀ M₀).comp (Int.castRingHom ℚ : ℤ →*₀ ℚ) =
          (g : ℚ →*₀ M₀).comp (Int.castRingHom ℚ : ℤ →*₀ ℚ)
        from ext_int' (by simpa) (by simpa)
#align monoid_with_zero_hom.ext_rat_on_pnat MonoidWithZeroHom.ext_rat_on_pnat

end MonoidWithZeroHom

/-- Any two ring homomorphisms from `ℚ` to a semiring are equal. If the codomain is a division ring,
then this lemma follows from `eq_ratCast`. -/
theorem RingHom.ext_rat {R : Type*} [Semiring R] [RingHomClass F ℚ R] (f g : F) : f = g :=
  MonoidWithZeroHom.ext_rat' <|
    RingHom.congr_fun <|
      ((f : ℚ →+* R).comp (Int.castRingHom ℚ)).ext_int ((g : ℚ →+* R).comp (Int.castRingHom ℚ))
#align ring_hom.ext_rat RingHom.ext_rat

instance Rat.subsingleton_ringHom {R : Type*} [Semiring R] : Subsingleton (ℚ →+* R) :=
  ⟨RingHom.ext_rat⟩
#align rat.subsingleton_ring_hom Rat.subsingleton_ringHom

section SMul

namespace Rat

variable {K : Type*} [DivisionRing K]

instance (priority := 100) distribSMul : DistribSMul ℚ K where
  smul := (· • ·)
  smul_zero a := by rw [smul_def, mul_zero]
  smul_add a x y := by rw [smul_def, smul_def, smul_def, mul_add]
#align rat.distrib_smul Rat.distribSMul

instance isScalarTower_right : IsScalarTower ℚ K K :=
  ⟨fun a x y => by simp only [smul_def, smul_eq_mul, mul_assoc]⟩
#align rat.is_scalar_tower_right Rat.isScalarTower_right

end Rat

end SMul

-- Guard against import creep regression.
assert_not_exists add_div
