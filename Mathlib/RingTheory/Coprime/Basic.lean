/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Ken Lee, Chris Hughes
-/
import Mathlib.Algebra.Group.Action.Units
import Mathlib.Algebra.Group.Nat.Units
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Logic.Basic
import Mathlib.Tactic.Ring

/-!
# Coprime elements of a ring or monoid

## Main definition

* `IsCoprime x y`: that `x` and `y` are coprime, defined to be the existence of `a` and `b` such
  that `a * x + b * y = 1`. Note that elements with no common divisors (`IsRelPrime`) are not
  necessarily coprime, e.g., the multivariate polynomials `x₁` and `x₂` are not coprime.
  The two notions are equivalent in Bézout rings, see `isRelPrime_iff_isCoprime`.

This file also contains lemmas about `IsRelPrime` parallel to `IsCoprime`.

See also `RingTheory.Coprime.Lemmas` for further development of coprime elements.
-/


universe u v

section CommSemiring

variable {R : Type u} [CommSemiring R] (x y z w : R)

/-- The proposition that `x` and `y` are coprime, defined to be the existence of `a` and `b` such
that `a * x + b * y = 1`. Note that elements with no common divisors are not necessarily coprime,
e.g., the multivariate polynomials `x₁` and `x₂` are not coprime. -/
def IsCoprime : Prop :=
  ∃ a b, a * x + b * y = 1

variable {x y z w}

@[symm]
theorem IsCoprime.symm (H : IsCoprime x y) : IsCoprime y x :=
  let ⟨a, b, H⟩ := H
  ⟨b, a, by rw [add_comm, H]⟩

theorem isCoprime_comm : IsCoprime x y ↔ IsCoprime y x :=
  ⟨IsCoprime.symm, IsCoprime.symm⟩

theorem isCoprime_self : IsCoprime x x ↔ IsUnit x :=
  ⟨fun ⟨a, b, h⟩ => isUnit_of_mul_eq_one x (a + b) <| by rwa [mul_comm, add_mul], fun h =>
    let ⟨b, hb⟩ := isUnit_iff_exists_inv'.1 h
    ⟨b, 0, by rwa [zero_mul, add_zero]⟩⟩

theorem isCoprime_zero_left : IsCoprime 0 x ↔ IsUnit x :=
  ⟨fun ⟨a, b, H⟩ => isUnit_of_mul_eq_one x b <| by rwa [mul_zero, zero_add, mul_comm] at H, fun H =>
    let ⟨b, hb⟩ := isUnit_iff_exists_inv'.1 H
    ⟨1, b, by rwa [one_mul, zero_add]⟩⟩

theorem isCoprime_zero_right : IsCoprime x 0 ↔ IsUnit x :=
  isCoprime_comm.trans isCoprime_zero_left

theorem not_isCoprime_zero_zero [Nontrivial R] : ¬IsCoprime (0 : R) 0 :=
  mt isCoprime_zero_right.mp not_isUnit_zero

lemma IsCoprime.intCast {R : Type*} [CommRing R] {a b : ℤ} (h : IsCoprime a b) :
    IsCoprime (a : R) (b : R) := by
  rcases h with ⟨u, v, H⟩
  use u, v
  rw_mod_cast [H]
  exact Int.cast_one

/-- If a 2-vector `p` satisfies `IsCoprime (p 0) (p 1)`, then `p ≠ 0`. -/
theorem IsCoprime.ne_zero [Nontrivial R] {p : Fin 2 → R} (h : IsCoprime (p 0) (p 1)) : p ≠ 0 := by
  rintro rfl
  exact not_isCoprime_zero_zero h

theorem IsCoprime.ne_zero_or_ne_zero [Nontrivial R] (h : IsCoprime x y) : x ≠ 0 ∨ y ≠ 0 := by
  apply not_or_of_imp
  rintro rfl rfl
  exact not_isCoprime_zero_zero h

theorem isCoprime_one_left : IsCoprime 1 x :=
  ⟨1, 0, by rw [one_mul, zero_mul, add_zero]⟩

theorem isCoprime_one_right : IsCoprime x 1 :=
  ⟨0, 1, by rw [one_mul, zero_mul, zero_add]⟩

theorem IsCoprime.dvd_of_dvd_mul_right (H1 : IsCoprime x z) (H2 : x ∣ y * z) : x ∣ y := by
  let ⟨a, b, H⟩ := H1
  rw [← mul_one y, ← H, mul_add, ← mul_assoc, mul_left_comm]
  exact dvd_add (dvd_mul_left _ _) (H2.mul_left _)

theorem IsCoprime.dvd_of_dvd_mul_left (H1 : IsCoprime x y) (H2 : x ∣ y * z) : x ∣ z := by
  let ⟨a, b, H⟩ := H1
  rw [← one_mul z, ← H, add_mul, mul_right_comm, mul_assoc b]
  exact dvd_add (dvd_mul_left _ _) (H2.mul_left _)

theorem IsCoprime.mul_left (H1 : IsCoprime x z) (H2 : IsCoprime y z) : IsCoprime (x * y) z :=
  let ⟨a, b, h1⟩ := H1
  let ⟨c, d, h2⟩ := H2
  ⟨a * c, a * x * d + b * c * y + b * d * z,
    calc a * c * (x * y) + (a * x * d + b * c * y + b * d * z) * z
      _ = (a * x + b * z) * (c * y + d * z) := by ring
      _ = 1 := by rw [h1, h2, mul_one]
      ⟩

theorem IsCoprime.mul_right (H1 : IsCoprime x y) (H2 : IsCoprime x z) : IsCoprime x (y * z) := by
  rw [isCoprime_comm] at H1 H2 ⊢
  exact H1.mul_left H2

theorem IsCoprime.mul_dvd (H : IsCoprime x y) (H1 : x ∣ z) (H2 : y ∣ z) : x * y ∣ z := by
  obtain ⟨a, b, h⟩ := H
  rw [← mul_one z, ← h, mul_add]
  apply dvd_add
  · rw [mul_comm z, mul_assoc]
    exact (mul_dvd_mul_left _ H2).mul_left _
  · rw [mul_comm b, ← mul_assoc]
    exact (mul_dvd_mul_right H1 _).mul_right _

theorem IsCoprime.of_mul_left_left (H : IsCoprime (x * y) z) : IsCoprime x z :=
  let ⟨a, b, h⟩ := H
  ⟨a * y, b, by rwa [mul_right_comm, mul_assoc]⟩

theorem IsCoprime.of_mul_left_right (H : IsCoprime (x * y) z) : IsCoprime y z := by
  rw [mul_comm] at H
  exact H.of_mul_left_left

theorem IsCoprime.of_mul_right_left (H : IsCoprime x (y * z)) : IsCoprime x y := by
  rw [isCoprime_comm] at H ⊢
  exact H.of_mul_left_left

theorem IsCoprime.of_mul_right_right (H : IsCoprime x (y * z)) : IsCoprime x z := by
  rw [mul_comm] at H
  exact H.of_mul_right_left

theorem IsCoprime.mul_left_iff : IsCoprime (x * y) z ↔ IsCoprime x z ∧ IsCoprime y z :=
  ⟨fun H => ⟨H.of_mul_left_left, H.of_mul_left_right⟩, fun ⟨H1, H2⟩ => H1.mul_left H2⟩

theorem IsCoprime.mul_right_iff : IsCoprime x (y * z) ↔ IsCoprime x y ∧ IsCoprime x z := by
  rw [isCoprime_comm, IsCoprime.mul_left_iff, isCoprime_comm, @isCoprime_comm _ _ z]

theorem IsCoprime.of_isCoprime_of_dvd_left (h : IsCoprime y z) (hdvd : x ∣ y) : IsCoprime x z := by
  obtain ⟨d, rfl⟩ := hdvd
  exact IsCoprime.of_mul_left_left h

theorem IsCoprime.of_isCoprime_of_dvd_right (h : IsCoprime z y) (hdvd : x ∣ y) : IsCoprime z x :=
  (h.symm.of_isCoprime_of_dvd_left hdvd).symm

@[gcongr]
theorem IsCoprime.mono (h₁ : x ∣ y) (h₂ : z ∣ w) (h : IsCoprime y w) : IsCoprime x z :=
  h.of_isCoprime_of_dvd_left h₁ |>.of_isCoprime_of_dvd_right h₂

theorem IsCoprime.isUnit_of_dvd (H : IsCoprime x y) (d : x ∣ y) : IsUnit x :=
  let ⟨k, hk⟩ := d
  isCoprime_self.1 <| IsCoprime.of_mul_right_left <| show IsCoprime x (x * k) from hk ▸ H

theorem IsCoprime.isUnit_of_dvd' {a b x : R} (h : IsCoprime a b) (ha : x ∣ a) (hb : x ∣ b) :
    IsUnit x :=
  (h.of_isCoprime_of_dvd_left ha).isUnit_of_dvd hb

theorem IsCoprime.isRelPrime {a b : R} (h : IsCoprime a b) : IsRelPrime a b :=
  fun _ ↦ h.isUnit_of_dvd'

theorem IsCoprime.map (H : IsCoprime x y) {S : Type v} [CommSemiring S] (f : R →+* S) :
    IsCoprime (f x) (f y) :=
  let ⟨a, b, h⟩ := H
  ⟨f a, f b, by rw [← f.map_mul, ← f.map_mul, ← f.map_add, h, f.map_one]⟩

theorem IsCoprime.of_add_mul_left_left (h : IsCoprime (x + y * z) y) : IsCoprime x y :=
  let ⟨a, b, H⟩ := h
  ⟨a, a * z + b, by
    simpa only [add_mul, mul_add, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm,
      mul_left_comm] using H⟩

theorem IsCoprime.of_add_mul_right_left (h : IsCoprime (x + z * y) y) : IsCoprime x y := by
  rw [mul_comm] at h
  exact h.of_add_mul_left_left

theorem IsCoprime.of_add_mul_left_right (h : IsCoprime x (y + x * z)) : IsCoprime x y := by
  rw [isCoprime_comm] at h ⊢
  exact h.of_add_mul_left_left

theorem IsCoprime.of_add_mul_right_right (h : IsCoprime x (y + z * x)) : IsCoprime x y := by
  rw [mul_comm] at h
  exact h.of_add_mul_left_right

theorem IsCoprime.of_mul_add_left_left (h : IsCoprime (y * z + x) y) : IsCoprime x y := by
  rw [add_comm] at h
  exact h.of_add_mul_left_left

theorem IsCoprime.of_mul_add_right_left (h : IsCoprime (z * y + x) y) : IsCoprime x y := by
  rw [add_comm] at h
  exact h.of_add_mul_right_left

theorem IsCoprime.of_mul_add_left_right (h : IsCoprime x (x * z + y)) : IsCoprime x y := by
  rw [add_comm] at h
  exact h.of_add_mul_left_right

theorem IsCoprime.of_mul_add_right_right (h : IsCoprime x (z * x + y)) : IsCoprime x y := by
  rw [add_comm] at h
  exact h.of_add_mul_right_right

theorem IsRelPrime.of_add_mul_left_left (h : IsRelPrime (x + y * z) y) : IsRelPrime x y :=
  fun _ hx hy ↦ h (dvd_add hx <| dvd_mul_of_dvd_left hy z) hy

theorem IsRelPrime.of_add_mul_right_left (h : IsRelPrime (x + z * y) y) : IsRelPrime x y :=
  (mul_comm z y ▸ h).of_add_mul_left_left

theorem IsRelPrime.of_add_mul_left_right (h : IsRelPrime x (y + x * z)) : IsRelPrime x y := by
  rw [isRelPrime_comm] at h ⊢
  exact h.of_add_mul_left_left

theorem IsRelPrime.of_add_mul_right_right (h : IsRelPrime x (y + z * x)) : IsRelPrime x y :=
  (mul_comm z x ▸ h).of_add_mul_left_right

theorem IsRelPrime.of_mul_add_left_left (h : IsRelPrime (y * z + x) y) : IsRelPrime x y :=
  (add_comm _ x ▸ h).of_add_mul_left_left

theorem IsRelPrime.of_mul_add_right_left (h : IsRelPrime (z * y + x) y) : IsRelPrime x y :=
  (add_comm _ x ▸ h).of_add_mul_right_left

theorem IsRelPrime.of_mul_add_left_right (h : IsRelPrime x (x * z + y)) : IsRelPrime x y :=
  (add_comm _ y ▸ h).of_add_mul_left_right

theorem IsRelPrime.of_mul_add_right_right (h : IsRelPrime x (z * x + y)) : IsRelPrime x y :=
  (add_comm _ y ▸ h).of_add_mul_right_right

end CommSemiring

section ScalarTower

variable {R G : Type*} [CommSemiring R] [Group G] [MulAction G R] [SMulCommClass G R R]
  [IsScalarTower G R R] (x : G) (y z : R)

theorem isCoprime_group_smul_left : IsCoprime (x • y) z ↔ IsCoprime y z :=
  ⟨fun ⟨a, b, h⟩ => ⟨x • a, b, by rwa [smul_mul_assoc, ← mul_smul_comm]⟩, fun ⟨a, b, h⟩ =>
    ⟨x⁻¹ • a, b, by rwa [smul_mul_smul_comm, inv_mul_cancel, one_smul]⟩⟩

theorem isCoprime_group_smul_right : IsCoprime y (x • z) ↔ IsCoprime y z :=
  isCoprime_comm.trans <| (isCoprime_group_smul_left x z y).trans isCoprime_comm

theorem isCoprime_group_smul : IsCoprime (x • y) (x • z) ↔ IsCoprime y z :=
  (isCoprime_group_smul_left x y (x • z)).trans (isCoprime_group_smul_right x y z)

end ScalarTower

section CommSemiringUnit

variable {R : Type*} [CommSemiring R] {x u v : R}

theorem isCoprime_mul_unit_left_left (hu : IsUnit x) (y z : R) :
    IsCoprime (x * y) z ↔ IsCoprime y z :=
  let ⟨u, hu⟩ := hu
  hu ▸ isCoprime_group_smul_left u y z

theorem isCoprime_mul_unit_left_right (hu : IsUnit x) (y z : R) :
    IsCoprime y (x * z) ↔ IsCoprime y z :=
  let ⟨u, hu⟩ := hu
  hu ▸ isCoprime_group_smul_right u y z

theorem isCoprime_mul_unit_right_left (hu : IsUnit x) (y z : R) :
    IsCoprime (y * x) z ↔ IsCoprime y z :=
  mul_comm x y ▸ isCoprime_mul_unit_left_left hu y z

theorem isCoprime_mul_unit_right_right (hu : IsUnit x) (y z : R) :
    IsCoprime y (z * x) ↔ IsCoprime y z :=
  mul_comm x z ▸ isCoprime_mul_unit_left_right hu y z

theorem isCoprime_mul_units_left (hu : IsUnit u) (hv : IsUnit v) (y z : R) :
    IsCoprime (u * y) (v * z) ↔ IsCoprime y z :=
  Iff.trans
    (isCoprime_mul_unit_left_left hu _ _)
    (isCoprime_mul_unit_left_right hv _ _)

theorem isCoprime_mul_units_right (hu : IsUnit u) (hv : IsUnit v) (y z : R) :
    IsCoprime (y * u) (z * v) ↔ IsCoprime y z :=
  Iff.trans
    (isCoprime_mul_unit_right_left hu _ _)
    (isCoprime_mul_unit_right_right hv _ _)

theorem isCoprime_mul_unit_left (hu : IsUnit x) (y z : R) :
    IsCoprime (x * y) (x * z) ↔ IsCoprime y z :=
  isCoprime_mul_units_left hu hu _ _

theorem isCoprime_mul_unit_right (hu : IsUnit x) (y z : R) :
    IsCoprime (y * x) (z * x) ↔ IsCoprime y z :=
  isCoprime_mul_units_right hu hu _ _

end CommSemiringUnit

namespace IsCoprime

section CommRing

variable {R : Type u} [CommRing R]

theorem add_mul_left_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (x + y * z) y :=
  @of_add_mul_left_left R _ _ _ (-z) <| by simpa only [mul_neg, add_neg_cancel_right] using h

theorem add_mul_right_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (x + z * y) y := by
  rw [mul_comm]
  exact h.add_mul_left_left z

theorem add_mul_left_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (y + x * z) := by
  rw [isCoprime_comm]
  exact h.symm.add_mul_left_left z

theorem add_mul_right_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (y + z * x) := by
  rw [isCoprime_comm]
  exact h.symm.add_mul_right_left z

theorem mul_add_left_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (y * z + x) y := by
  rw [add_comm]
  exact h.add_mul_left_left z

theorem mul_add_right_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (z * y + x) y := by
  rw [add_comm]
  exact h.add_mul_right_left z

theorem mul_add_left_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (x * z + y) := by
  rw [add_comm]
  exact h.add_mul_left_right z

theorem mul_add_right_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (z * x + y) := by
  rw [add_comm]
  exact h.add_mul_right_right z

theorem add_mul_left_left_iff {x y z : R} : IsCoprime (x + y * z) y ↔ IsCoprime x y :=
  ⟨of_add_mul_left_left, fun h => h.add_mul_left_left z⟩

theorem add_mul_right_left_iff {x y z : R} : IsCoprime (x + z * y) y ↔ IsCoprime x y :=
  ⟨of_add_mul_right_left, fun h => h.add_mul_right_left z⟩

theorem add_mul_left_right_iff {x y z : R} : IsCoprime x (y + x * z) ↔ IsCoprime x y :=
  ⟨of_add_mul_left_right, fun h => h.add_mul_left_right z⟩

theorem add_mul_right_right_iff {x y z : R} : IsCoprime x (y + z * x) ↔ IsCoprime x y :=
  ⟨of_add_mul_right_right, fun h => h.add_mul_right_right z⟩

theorem mul_add_left_left_iff {x y z : R} : IsCoprime (y * z + x) y ↔ IsCoprime x y :=
  ⟨of_mul_add_left_left, fun h => h.mul_add_left_left z⟩

theorem mul_add_right_left_iff {x y z : R} : IsCoprime (z * y + x) y ↔ IsCoprime x y :=
  ⟨of_mul_add_right_left, fun h => h.mul_add_right_left z⟩

theorem mul_add_left_right_iff {x y z : R} : IsCoprime x (x * z + y) ↔ IsCoprime x y :=
  ⟨of_mul_add_left_right, fun h => h.mul_add_left_right z⟩

theorem mul_add_right_right_iff {x y z : R} : IsCoprime x (z * x + y) ↔ IsCoprime x y :=
  ⟨of_mul_add_right_right, fun h => h.mul_add_right_right z⟩

theorem neg_left {x y : R} (h : IsCoprime x y) : IsCoprime (-x) y := by
  obtain ⟨a, b, h⟩ := h
  use -a, b
  rwa [neg_mul_neg]

theorem neg_left_iff (x y : R) : IsCoprime (-x) y ↔ IsCoprime x y :=
  ⟨fun h => neg_neg x ▸ h.neg_left, neg_left⟩

theorem neg_right {x y : R} (h : IsCoprime x y) : IsCoprime x (-y) :=
  h.symm.neg_left.symm

theorem neg_right_iff (x y : R) : IsCoprime x (-y) ↔ IsCoprime x y :=
  ⟨fun h => neg_neg y ▸ h.neg_right, neg_right⟩

theorem neg_neg {x y : R} (h : IsCoprime x y) : IsCoprime (-x) (-y) :=
  h.neg_left.neg_right

theorem neg_neg_iff (x y : R) : IsCoprime (-x) (-y) ↔ IsCoprime x y :=
  (neg_left_iff _ _).trans (neg_right_iff _ _)

section abs

variable [LinearOrder R] [AddLeftMono R]

lemma abs_left_iff (x y : R) : IsCoprime |x| y ↔ IsCoprime x y := by
  cases le_or_gt 0 x with
  | inl h => rw [abs_of_nonneg h]
  | inr h => rw [abs_of_neg h, IsCoprime.neg_left_iff]

lemma abs_left {x y : R} (h : IsCoprime x y) : IsCoprime |x| y := abs_left_iff _ _ |>.2 h

lemma abs_right_iff (x y : R) : IsCoprime x |y| ↔ IsCoprime x y := by
  rw [isCoprime_comm, IsCoprime.abs_left_iff, isCoprime_comm]

lemma abs_right {x y : R} (h : IsCoprime x y) : IsCoprime x |y| := abs_right_iff _ _ |>.2 h

theorem abs_abs_iff (x y : R) : IsCoprime |x| |y| ↔ IsCoprime x y :=
  (abs_left_iff _ _).trans (abs_right_iff _ _)

theorem abs_abs {x y : R} (h : IsCoprime x y) : IsCoprime |x| |y| := h.abs_left.abs_right

end abs

end CommRing

theorem sq_add_sq_ne_zero {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {a b : R} (h : IsCoprime a b) :
    a ^ 2 + b ^ 2 ≠ 0 := by
  intro h'
  obtain ⟨ha, hb⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp h'
  obtain rfl := eq_zero_of_pow_eq_zero ha
  obtain rfl := eq_zero_of_pow_eq_zero hb
  exact not_isCoprime_zero_zero h

end IsCoprime

/-- `IsCoprime` is not a useful definition for `Nat`; consider using `Nat.Coprime` instead. -/
@[simp]
lemma Nat.isCoprime_iff {m n : ℕ} : IsCoprime m n ↔ m = 1 ∨ n = 1 := by
  refine ⟨fun ⟨a, b, H⟩ => ?_, fun h => ?_⟩
  · simp_rw [Nat.add_eq_one_iff, mul_eq_one, mul_eq_zero] at H
    exact H.symm.imp (·.1.2) (·.2.2)
  · obtain rfl | rfl := h
    · exact isCoprime_one_left
    · exact isCoprime_one_right

/-- `IsCoprime` is not a useful definition for `PNat`; consider using `Nat.Coprime` instead. -/
lemma PNat.isCoprime_iff {m n : ℕ+} : IsCoprime (m : ℕ) n ↔ m = 1 ∨ n = 1 := by simp

/-- `IsCoprime` is not a useful definition if an inverse is available. -/
@[simp]
lemma Semifield.isCoprime_iff {R : Type*} [Semifield R] {m n : R} :
    IsCoprime m n ↔ m ≠ 0 ∨ n ≠ 0 := by
  obtain rfl | hn := eq_or_ne n 0
  · simp [isCoprime_zero_right]
  suffices IsCoprime m n by simpa [hn]
  refine ⟨0, n⁻¹, ?_⟩
  simp [inv_mul_cancel₀ hn]

namespace IsRelPrime

variable {R} [CommRing R] {x y : R}

theorem add_mul_left_left (h : IsRelPrime x y) (z : R) : IsRelPrime (x + y * z) y :=
  @of_add_mul_left_left R _ _ _ (-z) <| by simpa only [mul_neg, add_neg_cancel_right] using h

theorem add_mul_right_left (h : IsRelPrime x y) (z : R) : IsRelPrime (x + z * y) y :=
  mul_comm z y ▸ h.add_mul_left_left z

theorem add_mul_left_right (h : IsRelPrime x y) (z : R) : IsRelPrime x (y + x * z) :=
  (h.symm.add_mul_left_left z).symm

theorem add_mul_right_right (h : IsRelPrime x y) (z : R) : IsRelPrime x (y + z * x) :=
  (h.symm.add_mul_right_left z).symm

theorem mul_add_left_left (h : IsRelPrime x y) (z : R) : IsRelPrime (y * z + x) y :=
  add_comm x _ ▸ h.add_mul_left_left z

theorem mul_add_right_left (h : IsRelPrime x y) (z : R) : IsRelPrime (z * y + x) y :=
  add_comm x _ ▸ h.add_mul_right_left z

theorem mul_add_left_right (h : IsRelPrime x y) (z : R) : IsRelPrime x (x * z + y) :=
  add_comm y _ ▸ h.add_mul_left_right z

theorem mul_add_right_right (h : IsRelPrime x y) (z : R) : IsRelPrime x (z * x + y) :=
  add_comm y _ ▸ h.add_mul_right_right z

variable {z}

theorem add_mul_left_left_iff : IsRelPrime (x + y * z) y ↔ IsRelPrime x y :=
  ⟨of_add_mul_left_left, fun h ↦ h.add_mul_left_left z⟩

theorem add_mul_right_left_iff : IsRelPrime (x + z * y) y ↔ IsRelPrime x y :=
  ⟨of_add_mul_right_left, fun h ↦ h.add_mul_right_left z⟩

theorem add_mul_left_right_iff : IsRelPrime x (y + x * z) ↔ IsRelPrime x y :=
  ⟨of_add_mul_left_right, fun h ↦ h.add_mul_left_right z⟩

theorem add_mul_right_right_iff : IsRelPrime x (y + z * x) ↔ IsRelPrime x y :=
  ⟨of_add_mul_right_right, fun h ↦ h.add_mul_right_right z⟩

theorem mul_add_left_left_iff {x y z : R} : IsRelPrime (y * z + x) y ↔ IsRelPrime x y :=
  ⟨of_mul_add_left_left, fun h ↦ h.mul_add_left_left z⟩

theorem mul_add_right_left_iff {x y z : R} : IsRelPrime (z * y + x) y ↔ IsRelPrime x y :=
  ⟨of_mul_add_right_left, fun h ↦ h.mul_add_right_left z⟩

theorem mul_add_left_right_iff {x y z : R} : IsRelPrime x (x * z + y) ↔ IsRelPrime x y :=
  ⟨of_mul_add_left_right, fun h ↦ h.mul_add_left_right z⟩

theorem mul_add_right_right_iff {x y z : R} : IsRelPrime x (z * x + y) ↔ IsRelPrime x y :=
  ⟨of_mul_add_right_right, fun h ↦ h.mul_add_right_right z⟩

theorem neg_left (h : IsRelPrime x y) : IsRelPrime (-x) y := fun _ ↦ (h <| dvd_neg.mp ·)
theorem neg_right (h : IsRelPrime x y) : IsRelPrime x (-y) := h.symm.neg_left.symm
protected theorem neg_neg (h : IsRelPrime x y) : IsRelPrime (-x) (-y) := h.neg_left.neg_right

theorem neg_left_iff (x y : R) : IsRelPrime (-x) y ↔ IsRelPrime x y :=
  ⟨fun h ↦ neg_neg x ▸ h.neg_left, neg_left⟩

theorem neg_right_iff (x y : R) : IsRelPrime x (-y) ↔ IsRelPrime x y :=
  ⟨fun h ↦ neg_neg y ▸ h.neg_right, neg_right⟩

theorem neg_neg_iff (x y : R) : IsRelPrime (-x) (-y) ↔ IsRelPrime x y :=
  (neg_left_iff _ _).trans (neg_right_iff _ _)

end IsRelPrime
