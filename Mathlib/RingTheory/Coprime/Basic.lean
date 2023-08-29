/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Ken Lee, Chris Hughes
-/
import Mathlib.Tactic.Ring
import Mathlib.GroupTheory.GroupAction.Units
import Mathlib.Algebra.Ring.Divisibility
import Mathlib.Algebra.Hom.Ring
import Mathlib.Algebra.GroupPower.Ring

#align_import ring_theory.coprime.basic from "leanprover-community/mathlib"@"a95b16cbade0f938fc24abd05412bde1e84bab9b"

/-!
# Coprime elements of a ring

## Main definitions

* `IsCoprime x y`: that `x` and `y` are coprime, defined to be the existence of `a` and `b` such
that `a * x + b * y = 1`. Note that elements with no common divisors are not necessarily coprime,
e.g., the multivariate polynomials `x₁` and `x₂` are not coprime.

See also `RingTheory.Coprime.Lemmas` for further development of coprime elements.
-/


open Classical

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
            -- 🎉 no goals
#align is_coprime.symm IsCoprime.symm

theorem isCoprime_comm : IsCoprime x y ↔ IsCoprime y x :=
  ⟨IsCoprime.symm, IsCoprime.symm⟩
#align is_coprime_comm isCoprime_comm

theorem isCoprime_self : IsCoprime x x ↔ IsUnit x :=
  ⟨fun ⟨a, b, h⟩ => isUnit_of_mul_eq_one x (a + b) <| by rwa [mul_comm, add_mul], fun h =>
                                                         -- 🎉 no goals
    let ⟨b, hb⟩ := isUnit_iff_exists_inv'.1 h
    ⟨b, 0, by rwa [zero_mul, add_zero]⟩⟩
              -- 🎉 no goals
#align is_coprime_self isCoprime_self

theorem isCoprime_zero_left : IsCoprime 0 x ↔ IsUnit x :=
  ⟨fun ⟨a, b, H⟩ => isUnit_of_mul_eq_one x b <| by rwa [mul_zero, zero_add, mul_comm] at H, fun H =>
                                                   -- 🎉 no goals
    let ⟨b, hb⟩ := isUnit_iff_exists_inv'.1 H
    ⟨1, b, by rwa [one_mul, zero_add]⟩⟩
              -- 🎉 no goals
#align is_coprime_zero_left isCoprime_zero_left

theorem isCoprime_zero_right : IsCoprime x 0 ↔ IsUnit x :=
  isCoprime_comm.trans isCoprime_zero_left
#align is_coprime_zero_right isCoprime_zero_right

theorem not_isCoprime_zero_zero [Nontrivial R] : ¬IsCoprime (0 : R) 0 :=
  mt isCoprime_zero_right.mp not_isUnit_zero
#align not_coprime_zero_zero not_isCoprime_zero_zero

/-- If a 2-vector `p` satisfies `IsCoprime (p 0) (p 1)`, then `p ≠ 0`. -/
theorem IsCoprime.ne_zero [Nontrivial R] {p : Fin 2 → R} (h : IsCoprime (p 0) (p 1)) : p ≠ 0 := by
  rintro rfl
  -- ⊢ False
  exact not_isCoprime_zero_zero h
  -- 🎉 no goals
#align is_coprime.ne_zero IsCoprime.ne_zero

theorem IsCoprime.ne_zero_or_ne_zero [Nontrivial R] (h : IsCoprime x y) : x ≠ 0 ∨ y ≠ 0 := by
  apply not_or_of_imp
  -- ⊢ x = 0 → y ≠ 0
  rintro rfl rfl
  -- ⊢ False
  exact not_isCoprime_zero_zero h
  -- 🎉 no goals

theorem isCoprime_one_left : IsCoprime 1 x :=
  ⟨1, 0, by rw [one_mul, zero_mul, add_zero]⟩
            -- 🎉 no goals
#align is_coprime_one_left isCoprime_one_left

theorem isCoprime_one_right : IsCoprime x 1 :=
  ⟨0, 1, by rw [one_mul, zero_mul, zero_add]⟩
            -- 🎉 no goals
#align is_coprime_one_right isCoprime_one_right

theorem IsCoprime.dvd_of_dvd_mul_right (H1 : IsCoprime x z) (H2 : x ∣ y * z) : x ∣ y := by
  let ⟨a, b, H⟩ := H1
  -- ⊢ x ∣ y
  rw [← mul_one y, ← H, mul_add, ← mul_assoc, mul_left_comm]
  -- ⊢ x ∣ y * a * x + b * (y * z)
  exact dvd_add (dvd_mul_left _ _) (H2.mul_left _)
  -- 🎉 no goals
#align is_coprime.dvd_of_dvd_mul_right IsCoprime.dvd_of_dvd_mul_right

theorem IsCoprime.dvd_of_dvd_mul_left (H1 : IsCoprime x y) (H2 : x ∣ y * z) : x ∣ z := by
  let ⟨a, b, H⟩ := H1
  -- ⊢ x ∣ z
  rw [← one_mul z, ← H, add_mul, mul_right_comm, mul_assoc b]
  -- ⊢ x ∣ a * z * x + b * (y * z)
  exact dvd_add (dvd_mul_left _ _) (H2.mul_left _)
  -- 🎉 no goals
#align is_coprime.dvd_of_dvd_mul_left IsCoprime.dvd_of_dvd_mul_left

theorem IsCoprime.mul_left (H1 : IsCoprime x z) (H2 : IsCoprime y z) : IsCoprime (x * y) z :=
  let ⟨a, b, h1⟩ := H1
  let ⟨c, d, h2⟩ := H2
  ⟨a * c, a * x * d + b * c * y + b * d * z,
    calc
      a * c * (x * y) + (a * x * d + b * c * y + b * d * z) * z =
          (a * x + b * z) * (c * y + d * z) :=
        by ring
           -- 🎉 no goals
      _ = 1 := by rw [h1, h2, mul_one]
                  -- 🎉 no goals
      ⟩
#align is_coprime.mul_left IsCoprime.mul_left

theorem IsCoprime.mul_right (H1 : IsCoprime x y) (H2 : IsCoprime x z) : IsCoprime x (y * z) := by
  rw [isCoprime_comm] at H1 H2 ⊢
  -- ⊢ IsCoprime (y * z) x
  exact H1.mul_left H2
  -- 🎉 no goals
#align is_coprime.mul_right IsCoprime.mul_right

theorem IsCoprime.mul_dvd (H : IsCoprime x y) (H1 : x ∣ z) (H2 : y ∣ z) : x * y ∣ z := by
  obtain ⟨a, b, h⟩ := H
  -- ⊢ x * y ∣ z
  rw [← mul_one z, ← h, mul_add]
  -- ⊢ x * y ∣ z * (a * x) + z * (b * y)
  apply dvd_add
  -- ⊢ x * y ∣ z * (a * x)
  · rw [mul_comm z, mul_assoc]
    -- ⊢ x * y ∣ a * (x * z)
    exact (mul_dvd_mul_left _ H2).mul_left _
    -- 🎉 no goals
  · rw [mul_comm b, ← mul_assoc]
    -- ⊢ x * y ∣ z * y * b
    exact (mul_dvd_mul_right H1 _).mul_right _
    -- 🎉 no goals
#align is_coprime.mul_dvd IsCoprime.mul_dvd

theorem IsCoprime.of_mul_left_left (H : IsCoprime (x * y) z) : IsCoprime x z :=
  let ⟨a, b, h⟩ := H
  ⟨a * y, b, by rwa [mul_right_comm, mul_assoc]⟩
                -- 🎉 no goals
#align is_coprime.of_mul_left_left IsCoprime.of_mul_left_left

theorem IsCoprime.of_mul_left_right (H : IsCoprime (x * y) z) : IsCoprime y z := by
  rw [mul_comm] at H
  -- ⊢ IsCoprime y z
  exact H.of_mul_left_left
  -- 🎉 no goals
#align is_coprime.of_mul_left_right IsCoprime.of_mul_left_right

theorem IsCoprime.of_mul_right_left (H : IsCoprime x (y * z)) : IsCoprime x y := by
  rw [isCoprime_comm] at H ⊢
  -- ⊢ IsCoprime y x
  exact H.of_mul_left_left
  -- 🎉 no goals
#align is_coprime.of_mul_right_left IsCoprime.of_mul_right_left

theorem IsCoprime.of_mul_right_right (H : IsCoprime x (y * z)) : IsCoprime x z := by
  rw [mul_comm] at H
  -- ⊢ IsCoprime x z
  exact H.of_mul_right_left
  -- 🎉 no goals
#align is_coprime.of_mul_right_right IsCoprime.of_mul_right_right

theorem IsCoprime.mul_left_iff : IsCoprime (x * y) z ↔ IsCoprime x z ∧ IsCoprime y z :=
  ⟨fun H => ⟨H.of_mul_left_left, H.of_mul_left_right⟩, fun ⟨H1, H2⟩ => H1.mul_left H2⟩
#align is_coprime.mul_left_iff IsCoprime.mul_left_iff

theorem IsCoprime.mul_right_iff : IsCoprime x (y * z) ↔ IsCoprime x y ∧ IsCoprime x z := by
  rw [isCoprime_comm, IsCoprime.mul_left_iff, isCoprime_comm, @isCoprime_comm _ _ z]
  -- 🎉 no goals
#align is_coprime.mul_right_iff IsCoprime.mul_right_iff

theorem IsCoprime.of_isCoprime_of_dvd_left (h : IsCoprime y z) (hdvd : x ∣ y) : IsCoprime x z := by
  obtain ⟨d, rfl⟩ := hdvd
  -- ⊢ IsCoprime x z
  exact IsCoprime.of_mul_left_left h
  -- 🎉 no goals
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

theorem IsCoprime.map (H : IsCoprime x y) {S : Type v} [CommSemiring S] (f : R →+* S) :
    IsCoprime (f x) (f y) :=
  let ⟨a, b, h⟩ := H
  ⟨f a, f b, by rw [← f.map_mul, ← f.map_mul, ← f.map_add, h, f.map_one]⟩
                -- 🎉 no goals
#align is_coprime.map IsCoprime.map

theorem IsCoprime.of_add_mul_left_left (h : IsCoprime (x + y * z) y) : IsCoprime x y :=
  let ⟨a, b, H⟩ := h
  ⟨a, a * z + b, by
    simpa only [add_mul, mul_add, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm,
      mul_left_comm] using H⟩
#align is_coprime.of_add_mul_left_left IsCoprime.of_add_mul_left_left

theorem IsCoprime.of_add_mul_right_left (h : IsCoprime (x + z * y) y) : IsCoprime x y := by
  rw [mul_comm] at h
  -- ⊢ IsCoprime x y
  exact h.of_add_mul_left_left
  -- 🎉 no goals
#align is_coprime.of_add_mul_right_left IsCoprime.of_add_mul_right_left

theorem IsCoprime.of_add_mul_left_right (h : IsCoprime x (y + x * z)) : IsCoprime x y := by
  rw [isCoprime_comm] at h ⊢
  -- ⊢ IsCoprime y x
  exact h.of_add_mul_left_left
  -- 🎉 no goals
#align is_coprime.of_add_mul_left_right IsCoprime.of_add_mul_left_right

theorem IsCoprime.of_add_mul_right_right (h : IsCoprime x (y + z * x)) : IsCoprime x y := by
  rw [mul_comm] at h
  -- ⊢ IsCoprime x y
  exact h.of_add_mul_left_right
  -- 🎉 no goals
#align is_coprime.of_add_mul_right_right IsCoprime.of_add_mul_right_right

theorem IsCoprime.of_mul_add_left_left (h : IsCoprime (y * z + x) y) : IsCoprime x y := by
  rw [add_comm] at h
  -- ⊢ IsCoprime x y
  exact h.of_add_mul_left_left
  -- 🎉 no goals
#align is_coprime.of_mul_add_left_left IsCoprime.of_mul_add_left_left

theorem IsCoprime.of_mul_add_right_left (h : IsCoprime (z * y + x) y) : IsCoprime x y := by
  rw [add_comm] at h
  -- ⊢ IsCoprime x y
  exact h.of_add_mul_right_left
  -- 🎉 no goals
#align is_coprime.of_mul_add_right_left IsCoprime.of_mul_add_right_left

theorem IsCoprime.of_mul_add_left_right (h : IsCoprime x (x * z + y)) : IsCoprime x y := by
  rw [add_comm] at h
  -- ⊢ IsCoprime x y
  exact h.of_add_mul_left_right
  -- 🎉 no goals
#align is_coprime.of_mul_add_left_right IsCoprime.of_mul_add_left_right

theorem IsCoprime.of_mul_add_right_right (h : IsCoprime x (z * x + y)) : IsCoprime x y := by
  rw [add_comm] at h
  -- ⊢ IsCoprime x y
  exact h.of_add_mul_right_right
  -- 🎉 no goals
#align is_coprime.of_mul_add_right_right IsCoprime.of_mul_add_right_right

end CommSemiring

section ScalarTower

variable {R G : Type*} [CommSemiring R] [Group G] [MulAction G R] [SMulCommClass G R R]
  [IsScalarTower G R R] (x : G) (y z : R)

theorem isCoprime_group_smul_left : IsCoprime (x • y) z ↔ IsCoprime y z :=
  ⟨fun ⟨a, b, h⟩ => ⟨x • a, b, by rwa [smul_mul_assoc, ← mul_smul_comm]⟩, fun ⟨a, b, h⟩ =>
                                  -- 🎉 no goals
    ⟨x⁻¹ • a, b, by rwa [smul_mul_smul, inv_mul_self, one_smul]⟩⟩
                    -- 🎉 no goals
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
                                           -- 🎉 no goals
#align is_coprime.add_mul_left_left IsCoprime.add_mul_left_left

theorem add_mul_right_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (x + z * y) y := by
  rw [mul_comm]
  -- ⊢ IsCoprime (x + y * z) y
  exact h.add_mul_left_left z
  -- 🎉 no goals
#align is_coprime.add_mul_right_left IsCoprime.add_mul_right_left

theorem add_mul_left_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (y + x * z) := by
  rw [isCoprime_comm]
  -- ⊢ IsCoprime (y + x * z) x
  exact h.symm.add_mul_left_left z
  -- 🎉 no goals
#align is_coprime.add_mul_left_right IsCoprime.add_mul_left_right

theorem add_mul_right_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (y + z * x) := by
  rw [isCoprime_comm]
  -- ⊢ IsCoprime (y + z * x) x
  exact h.symm.add_mul_right_left z
  -- 🎉 no goals
#align is_coprime.add_mul_right_right IsCoprime.add_mul_right_right

theorem mul_add_left_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (y * z + x) y := by
  rw [add_comm]
  -- ⊢ IsCoprime (x + y * z) y
  exact h.add_mul_left_left z
  -- 🎉 no goals
#align is_coprime.mul_add_left_left IsCoprime.mul_add_left_left

theorem mul_add_right_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (z * y + x) y := by
  rw [add_comm]
  -- ⊢ IsCoprime (x + z * y) y
  exact h.add_mul_right_left z
  -- 🎉 no goals
#align is_coprime.mul_add_right_left IsCoprime.mul_add_right_left

theorem mul_add_left_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (x * z + y) := by
  rw [add_comm]
  -- ⊢ IsCoprime x (y + x * z)
  exact h.add_mul_left_right z
  -- 🎉 no goals
#align is_coprime.mul_add_left_right IsCoprime.mul_add_left_right

theorem mul_add_right_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (z * x + y) := by
  rw [add_comm]
  -- ⊢ IsCoprime x (y + z * x)
  exact h.add_mul_right_right z
  -- 🎉 no goals
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
  -- ⊢ IsCoprime (-x) y
  use -a, b
  -- ⊢ -a * -x + b * y = 1
  rwa [neg_mul_neg]
  -- 🎉 no goals
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
  -- ⊢ False
  obtain ⟨ha, hb⟩ := (add_eq_zero_iff'
  --Porting TODO: replace with sq_nonneg when that file is ported
    (by rw [pow_two]; exact mul_self_nonneg _)
    (by rw [pow_two]; exact mul_self_nonneg _)).mp h'
  obtain rfl := pow_eq_zero ha
  -- ⊢ False
  obtain rfl := pow_eq_zero hb
  -- ⊢ False
  exact not_isCoprime_zero_zero h
  -- 🎉 no goals
#align is_coprime.sq_add_sq_ne_zero IsCoprime.sq_add_sq_ne_zero

end IsCoprime
