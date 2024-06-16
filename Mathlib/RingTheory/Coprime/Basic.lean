/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Ken Lee, Chris Hughes
-/
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.GroupTheory.GroupAction.Units
import Mathlib.Logic.Basic
import Mathlib.Tactic.Ring

#align_import ring_theory.coprime.basic from "leanprover-community/mathlib"@"a95b16cbade0f938fc24abd05412bde1e84bab9b"

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

variable {R : Type u} [CommSemiring R] (x y z : R)

/-- The proposition that `x` and `y` are coprime, defined to be the existence of `a` and `b` such
that `a * x + b * y = 1`. Note that elements with no common divisors are not necessarily coprime,
e.g., the multivariate polynomials `x₁` and `x₂` are not coprime. -/
def IsCoprime : Prop :=
  ∃ a b, a * x + b * y = 1
#align is_coprime IsCoprime

variable {x y z}

@[symm]
theorem IsCoprime.symm (H : IsCoprime x y) : IsCoprime y x :=
  let ⟨a, b, H⟩ := H
  ⟨b, a, by rw [add_comm, H]⟩
#align is_coprime.symm IsCoprime.symm

theorem isCoprime_comm : IsCoprime x y ↔ IsCoprime y x :=
  ⟨IsCoprime.symm, IsCoprime.symm⟩
#align is_coprime_comm isCoprime_comm

theorem isCoprime_self : IsCoprime x x ↔ IsUnit x :=
  ⟨fun ⟨a, b, h⟩ => isUnit_of_mul_eq_one x (a + b) <| by rwa [mul_comm, add_mul], fun h =>
    let ⟨b, hb⟩ := isUnit_iff_exists_inv'.1 h
    ⟨b, 0, by rwa [zero_mul, add_zero]⟩⟩
#align is_coprime_self isCoprime_self

theorem isCoprime_zero_left : IsCoprime 0 x ↔ IsUnit x :=
  ⟨fun ⟨a, b, H⟩ => isUnit_of_mul_eq_one x b <| by rwa [mul_zero, zero_add, mul_comm] at H, fun H =>
    let ⟨b, hb⟩ := isUnit_iff_exists_inv'.1 H
    ⟨1, b, by rwa [one_mul, zero_add]⟩⟩
#align is_coprime_zero_left isCoprime_zero_left

theorem isCoprime_zero_right : IsCoprime x 0 ↔ IsUnit x :=
  isCoprime_comm.trans isCoprime_zero_left
#align is_coprime_zero_right isCoprime_zero_right

theorem not_isCoprime_zero_zero [Nontrivial R] : ¬IsCoprime (0 : R) 0 :=
  mt isCoprime_zero_right.mp not_isUnit_zero
#align not_coprime_zero_zero not_isCoprime_zero_zero

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
#align is_coprime.ne_zero IsCoprime.ne_zero

theorem IsCoprime.ne_zero_or_ne_zero [Nontrivial R] (h : IsCoprime x y) : x ≠ 0 ∨ y ≠ 0 := by
  apply not_or_of_imp
  rintro rfl rfl
  exact not_isCoprime_zero_zero h

theorem isCoprime_one_left : IsCoprime 1 x :=
  ⟨1, 0, by rw [one_mul, zero_mul, add_zero]⟩
#align is_coprime_one_left isCoprime_one_left

theorem isCoprime_one_right : IsCoprime x 1 :=
  ⟨0, 1, by rw [one_mul, zero_mul, zero_add]⟩
#align is_coprime_one_right isCoprime_one_right

theorem IsCoprime.dvd_of_dvd_mul_right (H1 : IsCoprime x z) (H2 : x ∣ y * z) : x ∣ y := by
  let ⟨a, b, H⟩ := H1
  rw [← mul_one y, ← H, mul_add, ← mul_assoc, mul_left_comm]
  exact dvd_add (dvd_mul_left _ _) (H2.mul_left _)
#align is_coprime.dvd_of_dvd_mul_right IsCoprime.dvd_of_dvd_mul_right

theorem IsCoprime.dvd_of_dvd_mul_left (H1 : IsCoprime x y) (H2 : x ∣ y * z) : x ∣ z := by
  let ⟨a, b, H⟩ := H1
  rw [← one_mul z, ← H, add_mul, mul_right_comm, mul_assoc b]
  exact dvd_add (dvd_mul_left _ _) (H2.mul_left _)
#align is_coprime.dvd_of_dvd_mul_left IsCoprime.dvd_of_dvd_mul_left

theorem IsCoprime.mul_left (H1 : IsCoprime x z) (H2 : IsCoprime y z) : IsCoprime (x * y) z :=
  let ⟨a, b, h1⟩ := H1
  let ⟨c, d, h2⟩ := H2
  ⟨a * c, a * x * d + b * c * y + b * d * z,
    calc a * c * (x * y) + (a * x * d + b * c * y + b * d * z) * z
      _ = (a * x + b * z) * (c * y + d * z) := by ring
      _ = 1 := by rw [h1, h2, mul_one]
      ⟩
#align is_coprime.mul_left IsCoprime.mul_left

theorem IsCoprime.mul_right (H1 : IsCoprime x y) (H2 : IsCoprime x z) : IsCoprime x (y * z) := by
  rw [isCoprime_comm] at H1 H2 ⊢
  exact H1.mul_left H2
#align is_coprime.mul_right IsCoprime.mul_right

theorem IsCoprime.mul_dvd (H : IsCoprime x y) (H1 : x ∣ z) (H2 : y ∣ z) : x * y ∣ z := by
  obtain ⟨a, b, h⟩ := H
  rw [← mul_one z, ← h, mul_add]
  apply dvd_add
  · rw [mul_comm z, mul_assoc]
    exact (mul_dvd_mul_left _ H2).mul_left _
  · rw [mul_comm b, ← mul_assoc]
    exact (mul_dvd_mul_right H1 _).mul_right _
#align is_coprime.mul_dvd IsCoprime.mul_dvd

theorem IsCoprime.of_mul_left_left (H : IsCoprime (x * y) z) : IsCoprime x z :=
  let ⟨a, b, h⟩ := H
  ⟨a * y, b, by rwa [mul_right_comm, mul_assoc]⟩
#align is_coprime.of_mul_left_left IsCoprime.of_mul_left_left

theorem IsCoprime.of_mul_left_right (H : IsCoprime (x * y) z) : IsCoprime y z := by
  rw [mul_comm] at H
  exact H.of_mul_left_left
#align is_coprime.of_mul_left_right IsCoprime.of_mul_left_right

theorem IsCoprime.of_mul_right_left (H : IsCoprime x (y * z)) : IsCoprime x y := by
  rw [isCoprime_comm] at H ⊢
  exact H.of_mul_left_left
#align is_coprime.of_mul_right_left IsCoprime.of_mul_right_left

theorem IsCoprime.of_mul_right_right (H : IsCoprime x (y * z)) : IsCoprime x z := by
  rw [mul_comm] at H
  exact H.of_mul_right_left
#align is_coprime.of_mul_right_right IsCoprime.of_mul_right_right

theorem IsCoprime.mul_left_iff : IsCoprime (x * y) z ↔ IsCoprime x z ∧ IsCoprime y z :=
  ⟨fun H => ⟨H.of_mul_left_left, H.of_mul_left_right⟩, fun ⟨H1, H2⟩ => H1.mul_left H2⟩
#align is_coprime.mul_left_iff IsCoprime.mul_left_iff

theorem IsCoprime.mul_right_iff : IsCoprime x (y * z) ↔ IsCoprime x y ∧ IsCoprime x z := by
  rw [isCoprime_comm, IsCoprime.mul_left_iff, isCoprime_comm, @isCoprime_comm _ _ z]
#align is_coprime.mul_right_iff IsCoprime.mul_right_iff

theorem IsCoprime.of_isCoprime_of_dvd_left (h : IsCoprime y z) (hdvd : x ∣ y) : IsCoprime x z := by
  obtain ⟨d, rfl⟩ := hdvd
  exact IsCoprime.of_mul_left_left h
#align is_coprime.of_coprime_of_dvd_left IsCoprime.of_isCoprime_of_dvd_left

theorem IsCoprime.of_isCoprime_of_dvd_right (h : IsCoprime z y) (hdvd : x ∣ y) : IsCoprime z x :=
  (h.symm.of_isCoprime_of_dvd_left hdvd).symm
#align is_coprime.of_coprime_of_dvd_right IsCoprime.of_isCoprime_of_dvd_right

theorem IsCoprime.isUnit_of_dvd (H : IsCoprime x y) (d : x ∣ y) : IsUnit x :=
  let ⟨k, hk⟩ := d
  isCoprime_self.1 <| IsCoprime.of_mul_right_left <| show IsCoprime x (x * k) from hk ▸ H
#align is_coprime.is_unit_of_dvd IsCoprime.isUnit_of_dvd

theorem IsCoprime.isUnit_of_dvd' {a b x : R} (h : IsCoprime a b) (ha : x ∣ a) (hb : x ∣ b) :
    IsUnit x :=
  (h.of_isCoprime_of_dvd_left ha).isUnit_of_dvd hb
#align is_coprime.is_unit_of_dvd' IsCoprime.isUnit_of_dvd'

theorem IsCoprime.isRelPrime {a b : R} (h : IsCoprime a b) : IsRelPrime a b :=
  fun _ ↦ h.isUnit_of_dvd'

theorem IsCoprime.map (H : IsCoprime x y) {S : Type v} [CommSemiring S] (f : R →+* S) :
    IsCoprime (f x) (f y) :=
  let ⟨a, b, h⟩ := H
  ⟨f a, f b, by rw [← f.map_mul, ← f.map_mul, ← f.map_add, h, f.map_one]⟩
#align is_coprime.map IsCoprime.map

theorem IsCoprime.of_add_mul_left_left (h : IsCoprime (x + y * z) y) : IsCoprime x y :=
  let ⟨a, b, H⟩ := h
  ⟨a, a * z + b, by
    simpa only [add_mul, mul_add, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm,
      mul_left_comm] using H⟩
#align is_coprime.of_add_mul_left_left IsCoprime.of_add_mul_left_left

theorem IsCoprime.of_add_mul_right_left (h : IsCoprime (x + z * y) y) : IsCoprime x y := by
  rw [mul_comm] at h
  exact h.of_add_mul_left_left
#align is_coprime.of_add_mul_right_left IsCoprime.of_add_mul_right_left

theorem IsCoprime.of_add_mul_left_right (h : IsCoprime x (y + x * z)) : IsCoprime x y := by
  rw [isCoprime_comm] at h ⊢
  exact h.of_add_mul_left_left
#align is_coprime.of_add_mul_left_right IsCoprime.of_add_mul_left_right

theorem IsCoprime.of_add_mul_right_right (h : IsCoprime x (y + z * x)) : IsCoprime x y := by
  rw [mul_comm] at h
  exact h.of_add_mul_left_right
#align is_coprime.of_add_mul_right_right IsCoprime.of_add_mul_right_right

theorem IsCoprime.of_mul_add_left_left (h : IsCoprime (y * z + x) y) : IsCoprime x y := by
  rw [add_comm] at h
  exact h.of_add_mul_left_left
#align is_coprime.of_mul_add_left_left IsCoprime.of_mul_add_left_left

theorem IsCoprime.of_mul_add_right_left (h : IsCoprime (z * y + x) y) : IsCoprime x y := by
  rw [add_comm] at h
  exact h.of_add_mul_right_left
#align is_coprime.of_mul_add_right_left IsCoprime.of_mul_add_right_left

theorem IsCoprime.of_mul_add_left_right (h : IsCoprime x (x * z + y)) : IsCoprime x y := by
  rw [add_comm] at h
  exact h.of_add_mul_left_right
#align is_coprime.of_mul_add_left_right IsCoprime.of_mul_add_left_right

theorem IsCoprime.of_mul_add_right_right (h : IsCoprime x (z * x + y)) : IsCoprime x y := by
  rw [add_comm] at h
  exact h.of_add_mul_right_right
#align is_coprime.of_mul_add_right_right IsCoprime.of_mul_add_right_right

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
    ⟨x⁻¹ • a, b, by rwa [smul_mul_smul, inv_mul_self, one_smul]⟩⟩
#align is_coprime_group_smul_left isCoprime_group_smul_left

theorem isCoprime_group_smul_right : IsCoprime y (x • z) ↔ IsCoprime y z :=
  isCoprime_comm.trans <| (isCoprime_group_smul_left x z y).trans isCoprime_comm
#align is_coprime_group_smul_right isCoprime_group_smul_right

theorem isCoprime_group_smul : IsCoprime (x • y) (x • z) ↔ IsCoprime y z :=
  (isCoprime_group_smul_left x y (x • z)).trans (isCoprime_group_smul_right x y z)
#align is_coprime_group_smul isCoprime_group_smul

end ScalarTower

section CommSemiringUnit

variable {R : Type*} [CommSemiring R] {x : R} (hu : IsUnit x) (y z : R)

theorem isCoprime_mul_unit_left_left : IsCoprime (x * y) z ↔ IsCoprime y z :=
  let ⟨u, hu⟩ := hu
  hu ▸ isCoprime_group_smul_left u y z
#align is_coprime_mul_unit_left_left isCoprime_mul_unit_left_left

theorem isCoprime_mul_unit_left_right : IsCoprime y (x * z) ↔ IsCoprime y z :=
  let ⟨u, hu⟩ := hu
  hu ▸ isCoprime_group_smul_right u y z
#align is_coprime_mul_unit_left_right isCoprime_mul_unit_left_right

theorem isCoprime_mul_unit_left : IsCoprime (x * y) (x * z) ↔ IsCoprime y z :=
  (isCoprime_mul_unit_left_left hu y (x * z)).trans (isCoprime_mul_unit_left_right hu y z)
#align is_coprime_mul_unit_left isCoprime_mul_unit_left

theorem isCoprime_mul_unit_right_left : IsCoprime (y * x) z ↔ IsCoprime y z :=
  mul_comm x y ▸ isCoprime_mul_unit_left_left hu y z
#align is_coprime_mul_unit_right_left isCoprime_mul_unit_right_left

theorem isCoprime_mul_unit_right_right : IsCoprime y (z * x) ↔ IsCoprime y z :=
  mul_comm x z ▸ isCoprime_mul_unit_left_right hu y z
#align is_coprime_mul_unit_right_right isCoprime_mul_unit_right_right

theorem isCoprime_mul_unit_right : IsCoprime (y * x) (z * x) ↔ IsCoprime y z :=
  (isCoprime_mul_unit_right_left hu y (z * x)).trans (isCoprime_mul_unit_right_right hu y z)
#align is_coprime_mul_unit_right isCoprime_mul_unit_right

end CommSemiringUnit

namespace IsCoprime

section CommRing

variable {R : Type u} [CommRing R]

theorem add_mul_left_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (x + y * z) y :=
  @of_add_mul_left_left R _ _ _ (-z) <| by simpa only [mul_neg, add_neg_cancel_right] using h
#align is_coprime.add_mul_left_left IsCoprime.add_mul_left_left

theorem add_mul_right_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (x + z * y) y := by
  rw [mul_comm]
  exact h.add_mul_left_left z
#align is_coprime.add_mul_right_left IsCoprime.add_mul_right_left

theorem add_mul_left_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (y + x * z) := by
  rw [isCoprime_comm]
  exact h.symm.add_mul_left_left z
#align is_coprime.add_mul_left_right IsCoprime.add_mul_left_right

theorem add_mul_right_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (y + z * x) := by
  rw [isCoprime_comm]
  exact h.symm.add_mul_right_left z
#align is_coprime.add_mul_right_right IsCoprime.add_mul_right_right

theorem mul_add_left_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (y * z + x) y := by
  rw [add_comm]
  exact h.add_mul_left_left z
#align is_coprime.mul_add_left_left IsCoprime.mul_add_left_left

theorem mul_add_right_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (z * y + x) y := by
  rw [add_comm]
  exact h.add_mul_right_left z
#align is_coprime.mul_add_right_left IsCoprime.mul_add_right_left

theorem mul_add_left_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (x * z + y) := by
  rw [add_comm]
  exact h.add_mul_left_right z
#align is_coprime.mul_add_left_right IsCoprime.mul_add_left_right

theorem mul_add_right_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (z * x + y) := by
  rw [add_comm]
  exact h.add_mul_right_right z
#align is_coprime.mul_add_right_right IsCoprime.mul_add_right_right

theorem add_mul_left_left_iff {x y z : R} : IsCoprime (x + y * z) y ↔ IsCoprime x y :=
  ⟨of_add_mul_left_left, fun h => h.add_mul_left_left z⟩
#align is_coprime.add_mul_left_left_iff IsCoprime.add_mul_left_left_iff

theorem add_mul_right_left_iff {x y z : R} : IsCoprime (x + z * y) y ↔ IsCoprime x y :=
  ⟨of_add_mul_right_left, fun h => h.add_mul_right_left z⟩
#align is_coprime.add_mul_right_left_iff IsCoprime.add_mul_right_left_iff

theorem add_mul_left_right_iff {x y z : R} : IsCoprime x (y + x * z) ↔ IsCoprime x y :=
  ⟨of_add_mul_left_right, fun h => h.add_mul_left_right z⟩
#align is_coprime.add_mul_left_right_iff IsCoprime.add_mul_left_right_iff

theorem add_mul_right_right_iff {x y z : R} : IsCoprime x (y + z * x) ↔ IsCoprime x y :=
  ⟨of_add_mul_right_right, fun h => h.add_mul_right_right z⟩
#align is_coprime.add_mul_right_right_iff IsCoprime.add_mul_right_right_iff

theorem mul_add_left_left_iff {x y z : R} : IsCoprime (y * z + x) y ↔ IsCoprime x y :=
  ⟨of_mul_add_left_left, fun h => h.mul_add_left_left z⟩
#align is_coprime.mul_add_left_left_iff IsCoprime.mul_add_left_left_iff

theorem mul_add_right_left_iff {x y z : R} : IsCoprime (z * y + x) y ↔ IsCoprime x y :=
  ⟨of_mul_add_right_left, fun h => h.mul_add_right_left z⟩
#align is_coprime.mul_add_right_left_iff IsCoprime.mul_add_right_left_iff

theorem mul_add_left_right_iff {x y z : R} : IsCoprime x (x * z + y) ↔ IsCoprime x y :=
  ⟨of_mul_add_left_right, fun h => h.mul_add_left_right z⟩
#align is_coprime.mul_add_left_right_iff IsCoprime.mul_add_left_right_iff

theorem mul_add_right_right_iff {x y z : R} : IsCoprime x (z * x + y) ↔ IsCoprime x y :=
  ⟨of_mul_add_right_right, fun h => h.mul_add_right_right z⟩
#align is_coprime.mul_add_right_right_iff IsCoprime.mul_add_right_right_iff

theorem neg_left {x y : R} (h : IsCoprime x y) : IsCoprime (-x) y := by
  obtain ⟨a, b, h⟩ := h
  use -a, b
  rwa [neg_mul_neg]
#align is_coprime.neg_left IsCoprime.neg_left

theorem neg_left_iff (x y : R) : IsCoprime (-x) y ↔ IsCoprime x y :=
  ⟨fun h => neg_neg x ▸ h.neg_left, neg_left⟩
#align is_coprime.neg_left_iff IsCoprime.neg_left_iff

theorem neg_right {x y : R} (h : IsCoprime x y) : IsCoprime x (-y) :=
  h.symm.neg_left.symm
#align is_coprime.neg_right IsCoprime.neg_right

theorem neg_right_iff (x y : R) : IsCoprime x (-y) ↔ IsCoprime x y :=
  ⟨fun h => neg_neg y ▸ h.neg_right, neg_right⟩
#align is_coprime.neg_right_iff IsCoprime.neg_right_iff

theorem neg_neg {x y : R} (h : IsCoprime x y) : IsCoprime (-x) (-y) :=
  h.neg_left.neg_right
#align is_coprime.neg_neg IsCoprime.neg_neg

theorem neg_neg_iff (x y : R) : IsCoprime (-x) (-y) ↔ IsCoprime x y :=
  (neg_left_iff _ _).trans (neg_right_iff _ _)
#align is_coprime.neg_neg_iff IsCoprime.neg_neg_iff

end CommRing

theorem sq_add_sq_ne_zero {R : Type*} [LinearOrderedCommRing R] {a b : R} (h : IsCoprime a b) :
    a ^ 2 + b ^ 2 ≠ 0 := by
  intro h'
  obtain ⟨ha, hb⟩ := (add_eq_zero_iff'
  --Porting TODO: replace with sq_nonneg when that file is ported
    (by rw [pow_two]; exact mul_self_nonneg _)
    (by rw [pow_two]; exact mul_self_nonneg _)).mp h'
  obtain rfl := pow_eq_zero ha
  obtain rfl := pow_eq_zero hb
  exact not_isCoprime_zero_zero h
#align is_coprime.sq_add_sq_ne_zero IsCoprime.sq_add_sq_ne_zero

end IsCoprime

namespace IsRelPrime

variable {R} [CommRing R] {x y : R} (h : IsRelPrime x y) (z : R)

theorem add_mul_left_left : IsRelPrime (x + y * z) y :=
  @of_add_mul_left_left R _ _ _ (-z) <| by simpa only [mul_neg, add_neg_cancel_right] using h

theorem add_mul_right_left : IsRelPrime (x + z * y) y :=
  mul_comm z y ▸ h.add_mul_left_left z

theorem add_mul_left_right : IsRelPrime x (y + x * z) :=
  (h.symm.add_mul_left_left z).symm

theorem add_mul_right_right : IsRelPrime x (y + z * x) :=
  (h.symm.add_mul_right_left z).symm

theorem mul_add_left_left : IsRelPrime (y * z + x) y :=
  add_comm x _ ▸ h.add_mul_left_left z

theorem mul_add_right_left : IsRelPrime (z * y + x) y :=
  add_comm x _ ▸ h.add_mul_right_left z

theorem mul_add_left_right : IsRelPrime x (x * z + y) :=
  add_comm y _ ▸ h.add_mul_left_right z

theorem mul_add_right_right : IsRelPrime x (z * x + y) :=
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

theorem neg_left : IsRelPrime (-x) y := fun _ ↦ (h <| dvd_neg.mp ·)
theorem neg_right : IsRelPrime x (-y) := h.symm.neg_left.symm
protected theorem neg_neg : IsRelPrime (-x) (-y) := h.neg_left.neg_right

theorem neg_left_iff (x y : R) : IsRelPrime (-x) y ↔ IsRelPrime x y :=
  ⟨fun h ↦ neg_neg x ▸ h.neg_left, neg_left⟩

theorem neg_right_iff (x y : R) : IsRelPrime x (-y) ↔ IsRelPrime x y :=
  ⟨fun h ↦ neg_neg y ▸ h.neg_right, neg_right⟩

theorem neg_neg_iff (x y : R) : IsRelPrime (-x) (-y) ↔ IsRelPrime x y :=
  (neg_left_iff _ _).trans (neg_right_iff _ _)

end IsRelPrime
