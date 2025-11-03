/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland, Aaron Anderson
-/
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Units.Basic

/-!
# Divisibility and units

## Main definition

* `IsRelPrime x y`: that `x` and `y` are relatively prime, defined to mean that the only common
  divisors of `x` and `y` are the units.

-/

variable {α : Type*}

namespace Units

section Monoid

variable [Monoid α] {a b : α} {u : αˣ}

/-- Elements of the unit group of a monoid represented as elements of the monoid
divide any element of the monoid. -/
theorem coe_dvd : ↑u ∣ a :=
  ⟨↑u⁻¹ * a, by simp⟩

/-- In a monoid, an element `a` divides an element `b` iff `a` divides all associates of `b`. -/
theorem dvd_mul_right : a ∣ b * u ↔ a ∣ b :=
  Iff.intro (fun ⟨c, eq⟩ ↦ ⟨c * ↑u⁻¹, by rw [← mul_assoc, ← eq, Units.mul_inv_cancel_right]⟩)
    fun ⟨_, eq⟩ ↦ eq.symm ▸ (_root_.dvd_mul_right _ _).mul_right _

/-- In a monoid, an element `a` divides an element `b` iff all associates of `a` divide `b`. -/
theorem mul_right_dvd : a * u ∣ b ↔ a ∣ b :=
  Iff.intro (fun ⟨c, eq⟩ => ⟨↑u * c, eq.trans (mul_assoc _ _ _)⟩) fun h =>
    dvd_trans (Dvd.intro (↑u⁻¹) (by rw [mul_assoc, u.mul_inv, mul_one])) h

end Monoid

section CommMonoid

variable [CommMonoid α] {a b : α} {u : αˣ}

/-- In a commutative monoid, an element `a` divides an element `b` iff `a` divides all left
associates of `b`. -/
theorem dvd_mul_left : a ∣ u * b ↔ a ∣ b := by
  rw [mul_comm]
  apply dvd_mul_right

/-- In a commutative monoid, an element `a` divides an element `b` iff all
  left associates of `a` divide `b`. -/
theorem mul_left_dvd : ↑u * a ∣ b ↔ a ∣ b := by
  rw [mul_comm]
  apply mul_right_dvd

end CommMonoid

end Units

namespace IsUnit

section Monoid

variable [Monoid α] {a b u : α}

/-- Units of a monoid divide any element of the monoid. -/
@[simp]
theorem dvd (hu : IsUnit u) : u ∣ a := by
  rcases hu with ⟨u, rfl⟩
  apply Units.coe_dvd

@[simp]
theorem dvd_mul_right (hu : IsUnit u) : a ∣ b * u ↔ a ∣ b := by
  rcases hu with ⟨u, rfl⟩
  apply Units.dvd_mul_right

/-- In a monoid, an element a divides an element b iff all associates of `a` divide `b`. -/
@[simp]
theorem mul_right_dvd (hu : IsUnit u) : a * u ∣ b ↔ a ∣ b := by
  rcases hu with ⟨u, rfl⟩
  apply Units.mul_right_dvd

theorem isPrimal (hu : IsUnit u) : IsPrimal u :=
  fun _ _ _ ↦ ⟨u, 1, hu.dvd, one_dvd _, (mul_one u).symm⟩

end Monoid

section CommMonoid

variable [CommMonoid α] {a b u : α}

/-- In a commutative monoid, an element `a` divides an element `b` iff `a` divides all left
associates of `b`. -/
@[simp]
theorem dvd_mul_left (hu : IsUnit u) : a ∣ u * b ↔ a ∣ b := by
  rcases hu with ⟨u, rfl⟩
  apply Units.dvd_mul_left

/-- In a commutative monoid, an element `a` divides an element `b` iff all
  left associates of `a` divide `b`. -/
@[simp]
theorem mul_left_dvd (hu : IsUnit u) : u * a ∣ b ↔ a ∣ b := by
  rcases hu with ⟨u, rfl⟩
  apply Units.mul_left_dvd

end CommMonoid

end IsUnit

section CommMonoid

variable [CommMonoid α]

theorem isUnit_iff_dvd_one {x : α} : IsUnit x ↔ x ∣ 1 :=
  ⟨IsUnit.dvd, fun ⟨y, h⟩ => ⟨⟨x, y, h.symm, by rw [h, mul_comm]⟩, rfl⟩⟩

theorem isUnit_iff_forall_dvd {x : α} : IsUnit x ↔ ∀ y, x ∣ y :=
  isUnit_iff_dvd_one.trans ⟨fun h _ => h.trans (one_dvd _), fun h => h _⟩

theorem isUnit_of_dvd_unit {x y : α} (xy : x ∣ y) (hu : IsUnit y) : IsUnit x :=
  isUnit_iff_dvd_one.2 <| xy.trans <| isUnit_iff_dvd_one.1 hu

theorem isUnit_of_dvd_one {a : α} (h : a ∣ 1) : IsUnit (a : α) :=
  isUnit_iff_dvd_one.mpr h

theorem not_isUnit_of_not_isUnit_dvd {a b : α} (ha : ¬IsUnit a) (hb : a ∣ b) : ¬IsUnit b :=
  mt (isUnit_of_dvd_unit hb) ha

@[simp]
lemma dvd_pow_self_iff {x : α} {n : ℕ} :
    x ∣ x ^ n ↔ n ≠ 0 ∨ IsUnit x := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [isUnit_iff_dvd_one]
  · simp [hn, dvd_pow_self]

end CommMonoid

section RelPrime

/-- `x` and `y` are relatively prime if every common divisor is a unit. -/
def IsRelPrime [Monoid α] (x y : α) : Prop := ∀ ⦃d⦄, d ∣ x → d ∣ y → IsUnit d

variable [CommMonoid α] {x y z : α}

@[symm] theorem IsRelPrime.symm (H : IsRelPrime x y) : IsRelPrime y x := fun _ hx hy ↦ H hy hx
theorem symmetric_isRelPrime : Symmetric (IsRelPrime : α → α → Prop) := fun _ _ ↦ .symm

theorem isRelPrime_comm : IsRelPrime x y ↔ IsRelPrime y x :=
  ⟨IsRelPrime.symm, IsRelPrime.symm⟩

theorem isRelPrime_self : IsRelPrime x x ↔ IsUnit x :=
  ⟨(· dvd_rfl dvd_rfl), fun hu _ _ dvd ↦ isUnit_of_dvd_unit dvd hu⟩

theorem IsUnit.isRelPrime_left (h : IsUnit x) : IsRelPrime x y :=
  fun _ hx _ ↦ isUnit_of_dvd_unit hx h
theorem IsUnit.isRelPrime_right (h : IsUnit y) : IsRelPrime x y := h.isRelPrime_left.symm
theorem isRelPrime_one_left : IsRelPrime 1 x := isUnit_one.isRelPrime_left
theorem isRelPrime_one_right : IsRelPrime x 1 := isUnit_one.isRelPrime_right

theorem IsRelPrime.of_mul_left_left (H : IsRelPrime (x * y) z) : IsRelPrime x z :=
  fun _ hx ↦ H (dvd_mul_of_dvd_left hx _)

theorem IsRelPrime.of_mul_left_right (H : IsRelPrime (x * y) z) : IsRelPrime y z :=
  (mul_comm x y ▸ H).of_mul_left_left

theorem IsRelPrime.of_mul_right_left (H : IsRelPrime x (y * z)) : IsRelPrime x y := by
  rw [isRelPrime_comm] at H ⊢
  exact H.of_mul_left_left

theorem IsRelPrime.of_mul_right_right (H : IsRelPrime x (y * z)) : IsRelPrime x z :=
  (mul_comm y z ▸ H).of_mul_right_left

theorem IsRelPrime.of_dvd_left (h : IsRelPrime y z) (dvd : x ∣ y) : IsRelPrime x z := by
  obtain ⟨d, rfl⟩ := dvd; exact IsRelPrime.of_mul_left_left h

theorem IsRelPrime.of_dvd_right (h : IsRelPrime z y) (dvd : x ∣ y) : IsRelPrime z x :=
  (h.symm.of_dvd_left dvd).symm

theorem IsRelPrime.isUnit_of_dvd (H : IsRelPrime x y) (d : x ∣ y) : IsUnit x := H dvd_rfl d

section IsUnit

variable (hu : IsUnit x)

include hu

theorem isRelPrime_mul_unit_left_left : IsRelPrime (x * y) z ↔ IsRelPrime y z :=
  ⟨IsRelPrime.of_mul_left_right, fun H _ h ↦ H (hu.dvd_mul_left.mp h)⟩

theorem isRelPrime_mul_unit_left_right : IsRelPrime y (x * z) ↔ IsRelPrime y z := by
  rw [isRelPrime_comm, isRelPrime_mul_unit_left_left hu, isRelPrime_comm]

theorem isRelPrime_mul_unit_left : IsRelPrime (x * y) (x * z) ↔ IsRelPrime y z := by
  rw [isRelPrime_mul_unit_left_left hu, isRelPrime_mul_unit_left_right hu]

theorem isRelPrime_mul_unit_right_left : IsRelPrime (y * x) z ↔ IsRelPrime y z := by
  rw [mul_comm, isRelPrime_mul_unit_left_left hu]

theorem isRelPrime_mul_unit_right_right : IsRelPrime y (z * x) ↔ IsRelPrime y z := by
  rw [mul_comm, isRelPrime_mul_unit_left_right hu]

theorem isRelPrime_mul_unit_right : IsRelPrime (y * x) (z * x) ↔ IsRelPrime y z := by
  rw [isRelPrime_mul_unit_right_left hu, isRelPrime_mul_unit_right_right hu]

end IsUnit

theorem IsRelPrime.dvd_of_dvd_mul_right_of_isPrimal (H1 : IsRelPrime x z) (H2 : x ∣ y * z)
    (h : IsPrimal x) : x ∣ y := by
  obtain ⟨a, b, ha, hb, rfl⟩ := h H2
  exact (H1.of_mul_left_right.isUnit_of_dvd hb).mul_right_dvd.mpr ha

theorem IsRelPrime.dvd_of_dvd_mul_left_of_isPrimal (H1 : IsRelPrime x y) (H2 : x ∣ y * z)
    (h : IsPrimal x) : x ∣ z :=
  H1.dvd_of_dvd_mul_right_of_isPrimal (mul_comm y z ▸ H2) h

theorem IsRelPrime.mul_dvd_of_right_isPrimal (H : IsRelPrime x y) (H1 : x ∣ z) (H2 : y ∣ z)
    (hy : IsPrimal y) : x * y ∣ z := by
  obtain ⟨w, rfl⟩ := H1
  exact mul_dvd_mul_left x (H.symm.dvd_of_dvd_mul_left_of_isPrimal H2 hy)

theorem IsRelPrime.mul_dvd_of_left_isPrimal (H : IsRelPrime x y) (H1 : x ∣ z) (H2 : y ∣ z)
    (hx : IsPrimal x) : x * y ∣ z := by
  rw [mul_comm]; exact H.symm.mul_dvd_of_right_isPrimal H2 H1 hx

/-! `IsRelPrime` enjoys desirable properties in a decomposition monoid.
See Lemma 6.3 in *On properties of square-free elements in commutative cancellative monoids*,
https://doi.org/10.1007/s00233-019-10022-3. -/

variable [DecompositionMonoid α]

theorem IsRelPrime.dvd_of_dvd_mul_right (H1 : IsRelPrime x z) (H2 : x ∣ y * z) : x ∣ y :=
  H1.dvd_of_dvd_mul_right_of_isPrimal H2 (DecompositionMonoid.primal x)

theorem IsRelPrime.dvd_of_dvd_mul_left (H1 : IsRelPrime x y) (H2 : x ∣ y * z) : x ∣ z :=
  H1.dvd_of_dvd_mul_right (mul_comm y z ▸ H2)

theorem IsRelPrime.mul_left (H1 : IsRelPrime x z) (H2 : IsRelPrime y z) : IsRelPrime (x * y) z :=
  fun _ h hz ↦ by
    obtain ⟨a, b, ha, hb, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul h
    exact (H1 ha <| (dvd_mul_right a b).trans hz).mul (H2 hb <| (dvd_mul_left b a).trans hz)

theorem IsRelPrime.mul_right (H1 : IsRelPrime x y) (H2 : IsRelPrime x z) :
    IsRelPrime x (y * z) := by
  rw [isRelPrime_comm] at H1 H2 ⊢; exact H1.mul_left H2

theorem IsRelPrime.mul_left_iff : IsRelPrime (x * y) z ↔ IsRelPrime x z ∧ IsRelPrime y z :=
  ⟨fun H ↦ ⟨H.of_mul_left_left, H.of_mul_left_right⟩, fun ⟨H1, H2⟩ ↦ H1.mul_left H2⟩

theorem IsRelPrime.mul_right_iff : IsRelPrime x (y * z) ↔ IsRelPrime x y ∧ IsRelPrime x z :=
  ⟨fun H ↦ ⟨H.of_mul_right_left, H.of_mul_right_right⟩, fun ⟨H1, H2⟩ ↦ H1.mul_right H2⟩

theorem IsRelPrime.mul_dvd (H : IsRelPrime x y) (H1 : x ∣ z) (H2 : y ∣ z) : x * y ∣ z :=
  H.mul_dvd_of_left_isPrimal H1 H2 (DecompositionMonoid.primal x)

end RelPrime
