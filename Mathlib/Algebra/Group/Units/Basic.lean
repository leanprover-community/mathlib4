/-
Copyright (c) 2017 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johannes Hölzl, Chris Hughes, Jens Wagemaker, Jon Eugster
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Logic.Unique
import Mathlib.Tactic.Nontriviality
import Mathlib.Tactic.Lift
import Mathlib.Tactic.Subsingleton

/-!
# Units (i.e., invertible elements) of a monoid

An element of a `Monoid` is a unit if it has a two-sided inverse.
This file contains the basic lemmas on units in a monoid, especially focussing on singleton types
and unique types.

## TODO

The results here should be used to golf the basic `Group` lemmas.
-/

assert_not_exists Multiplicative MonoidWithZero DenselyOrdered

open Function

universe u

variable {α : Type u}

section HasElem

@[to_additive]
theorem unique_one {α : Type*} [Unique α] [One α] : default = (1 : α) :=
  Unique.default_eq 1

end HasElem

namespace Units
section Monoid
variable [Monoid α]

variable (b c : αˣ) {u : αˣ}

@[to_additive (attr := simp)]
theorem mul_inv_cancel_right (a : α) (b : αˣ) : a * b * ↑b⁻¹ = a := by
  rw [mul_assoc, mul_inv, mul_one]

@[to_additive (attr := simp)]
theorem inv_mul_cancel_right (a : α) (b : αˣ) : a * ↑b⁻¹ * b = a := by
  rw [mul_assoc, inv_mul, mul_one]

@[to_additive (attr := simp)]
theorem mul_right_inj (a : αˣ) {b c : α} : (a : α) * b = a * c ↔ b = c :=
  ⟨fun h => by simpa only [inv_mul_cancel_left] using congr_arg (fun x : α => ↑(a⁻¹ : αˣ) * x) h,
    congr_arg _⟩

@[to_additive (attr := simp)]
theorem mul_left_inj (a : αˣ) {b c : α} : b * a = c * a ↔ b = c :=
  ⟨fun h => by simpa only [mul_inv_cancel_right] using congr_arg (fun x : α => x * ↑(a⁻¹ : αˣ)) h,
    congr_arg (· * a.val)⟩

@[to_additive]
theorem eq_mul_inv_iff_mul_eq {a b : α} : a = b * ↑c⁻¹ ↔ a * c = b :=
  ⟨fun h => by rw [h, inv_mul_cancel_right], fun h => by rw [← h, mul_inv_cancel_right]⟩

@[to_additive]
theorem eq_inv_mul_iff_mul_eq {a c : α} : a = ↑b⁻¹ * c ↔ ↑b * a = c :=
  ⟨fun h => by rw [h, mul_inv_cancel_left], fun h => by rw [← h, inv_mul_cancel_left]⟩

@[to_additive]
theorem mul_inv_eq_iff_eq_mul {a c : α} : a * ↑b⁻¹ = c ↔ a = c * b :=
  ⟨fun h => by rw [← h, inv_mul_cancel_right], fun h => by rw [h, mul_inv_cancel_right]⟩

@[to_additive]
protected theorem inv_eq_of_mul_eq_one_left {a : α} (h : a * u = 1) : ↑u⁻¹ = a :=
  calc
    ↑u⁻¹ = 1 * ↑u⁻¹ := by rw [one_mul]
    _ = a := by rw [← h, mul_inv_cancel_right]

@[to_additive]
protected theorem inv_eq_of_mul_eq_one_right {a : α} (h : ↑u * a = 1) : ↑u⁻¹ = a :=
  calc
    ↑u⁻¹ = ↑u⁻¹ * 1 := by rw [mul_one]
    _ = a := by rw [← h, inv_mul_cancel_left]

@[to_additive]
protected theorem eq_inv_of_mul_eq_one_left {a : α} (h : ↑u * a = 1) : a = ↑u⁻¹ :=
  (Units.inv_eq_of_mul_eq_one_right h).symm

@[to_additive]
protected theorem eq_inv_of_mul_eq_one_right {a : α} (h : a * u = 1) : a = ↑u⁻¹ :=
  (Units.inv_eq_of_mul_eq_one_left h).symm

@[to_additive (attr := simp)]
theorem mul_inv_eq_one {a : α} : a * ↑u⁻¹ = 1 ↔ a = u :=
  ⟨inv_inv u ▸ Units.eq_inv_of_mul_eq_one_right, fun h => mul_inv_of_eq h.symm⟩

@[to_additive (attr := simp)]
theorem inv_mul_eq_one {a : α} : ↑u⁻¹ * a = 1 ↔ ↑u = a :=
  ⟨inv_inv u ▸ Units.inv_eq_of_mul_eq_one_right, inv_mul_of_eq⟩

@[to_additive]
theorem mul_eq_one_iff_eq_inv {a : α} : a * u = 1 ↔ a = ↑u⁻¹ := by rw [← mul_inv_eq_one, inv_inv]

@[to_additive]
theorem mul_eq_one_iff_inv_eq {a : α} : ↑u * a = 1 ↔ ↑u⁻¹ = a := by rw [← inv_mul_eq_one, inv_inv]

@[to_additive]
theorem inv_unique {u₁ u₂ : αˣ} (h : (↑u₁ : α) = ↑u₂) : (↑u₁⁻¹ : α) = ↑u₂⁻¹ :=
  Units.inv_eq_of_mul_eq_one_right <| by rw [h, u₂.mul_inv]

end Monoid

section CommMonoid

variable [CommMonoid α] (a c : α) (b d : αˣ)

@[to_additive]
theorem mul_inv_eq_mul_inv_iff : a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b := by
  rw [mul_comm c, Units.mul_inv_eq_iff_eq_mul, mul_assoc, Units.eq_inv_mul_iff_mul_eq, mul_comm]

@[to_additive]
theorem inv_mul_eq_inv_mul_iff : b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b := by
  rw [mul_comm, mul_comm _ c, mul_inv_eq_mul_inv_iff]

end CommMonoid

end Units

section Monoid

variable [Monoid α]

@[simp]
theorem divp_left_inj (u : αˣ) {a b : α} : a /ₚ u = b /ₚ u ↔ a = b :=
  Units.mul_left_inj _

-- to match the mathlib3 behavior,
-- this needs to have higher simp priority than eq_divp_iff_mul_eq.
@[field_simps 1010]
theorem divp_eq_iff_mul_eq {x : α} {u : αˣ} {y : α} : x /ₚ u = y ↔ y * u = x :=
  u.mul_left_inj.symm.trans <| by rw [divp_mul_cancel]; exact ⟨Eq.symm, Eq.symm⟩

@[field_simps]
theorem eq_divp_iff_mul_eq {x : α} {u : αˣ} {y : α} : x = y /ₚ u ↔ x * u = y := by
  rw [eq_comm, divp_eq_iff_mul_eq]

theorem divp_eq_one_iff_eq {a : α} {u : αˣ} : a /ₚ u = 1 ↔ a = u :=
  (Units.mul_left_inj u).symm.trans <| by rw [divp_mul_cancel, one_mul]

/-- Used for `field_simp` to deal with inverses of units. This form of the lemma
is essential since `field_simp` likes to use `inv_eq_one_div` to rewrite
`↑u⁻¹ = ↑(1 / u)`. -/
@[field_simps]
theorem inv_eq_one_divp' (u : αˣ) : ((1 / u : αˣ) : α) = 1 /ₚ u := by
  rw [one_div, one_divp]

end Monoid

namespace LeftCancelMonoid

variable [LeftCancelMonoid α] [Subsingleton αˣ] {a b : α}

@[to_additive]
protected theorem eq_one_of_mul_right (h : a * b = 1) : a = 1 :=
  congr_arg Units.inv <| Subsingleton.elim (Units.mk _ _ (by
    rw [← mul_left_cancel_iff (a := a), ← mul_assoc, h, one_mul, mul_one]) h) 1

@[to_additive]
protected theorem eq_one_of_mul_left (h : a * b = 1) : b = 1 := by
  rwa [LeftCancelMonoid.eq_one_of_mul_right h, one_mul] at h

@[to_additive (attr := simp)]
protected theorem mul_eq_one : a * b = 1 ↔ a = 1 ∧ b = 1 :=
  ⟨fun h => ⟨LeftCancelMonoid.eq_one_of_mul_right h, LeftCancelMonoid.eq_one_of_mul_left h⟩, by
    rintro ⟨rfl, rfl⟩
    exact mul_one _⟩

@[to_additive]
protected theorem mul_ne_one : a * b ≠ 1 ↔ a ≠ 1 ∨ b ≠ 1 := by rw [not_iff_comm]; simp

end LeftCancelMonoid

namespace RightCancelMonoid

variable [RightCancelMonoid α] [Subsingleton αˣ] {a b : α}

@[to_additive]
protected theorem eq_one_of_mul_right (h : a * b = 1) : a = 1 :=
  congr_arg Units.inv <| Subsingleton.elim (Units.mk _ _ (by
    rw [← mul_right_cancel_iff (a := b), mul_assoc, h, one_mul, mul_one]) h) 1

@[to_additive]
protected theorem eq_one_of_mul_left (h : a * b = 1) : b = 1 := by
  rwa [RightCancelMonoid.eq_one_of_mul_right h, one_mul] at h

@[to_additive (attr := simp)]
protected theorem mul_eq_one : a * b = 1 ↔ a = 1 ∧ b = 1 :=
  ⟨fun h => ⟨RightCancelMonoid.eq_one_of_mul_right h, RightCancelMonoid.eq_one_of_mul_left h⟩, by
    rintro ⟨rfl, rfl⟩
    exact mul_one _⟩

@[to_additive]
protected theorem mul_ne_one : a * b ≠ 1 ↔ a ≠ 1 ∨ b ≠ 1 := by rw [not_iff_comm]; simp

end RightCancelMonoid

section CancelMonoid

variable [CancelMonoid α] [Subsingleton αˣ] {a b : α}

@[to_additive]
theorem eq_one_of_mul_right' (h : a * b = 1) : a = 1 := LeftCancelMonoid.eq_one_of_mul_right h

@[to_additive]
theorem eq_one_of_mul_left' (h : a * b = 1) : b = 1 := LeftCancelMonoid.eq_one_of_mul_left h

@[to_additive]
theorem mul_eq_one' : a * b = 1 ↔ a = 1 ∧ b = 1 := LeftCancelMonoid.mul_eq_one

@[to_additive]
theorem mul_ne_one' : a * b ≠ 1 ↔ a ≠ 1 ∨ b ≠ 1 := LeftCancelMonoid.mul_ne_one

end CancelMonoid

section CommMonoid

variable [CommMonoid α]

@[field_simps]
theorem divp_mul_eq_mul_divp (x y : α) (u : αˣ) : x /ₚ u * y = x * y /ₚ u := by
  rw [divp, divp, mul_right_comm]

-- Theoretically redundant as `field_simp` lemma.
@[field_simps]
theorem divp_eq_divp_iff {x y : α} {ux uy : αˣ} : x /ₚ ux = y /ₚ uy ↔ x * uy = y * ux := by
  rw [divp_eq_iff_mul_eq, divp_mul_eq_mul_divp, divp_eq_iff_mul_eq]

-- Theoretically redundant as `field_simp` lemma.
@[field_simps]
theorem divp_mul_divp (x y : α) (ux uy : αˣ) : x /ₚ ux * (y /ₚ uy) = x * y /ₚ (ux * uy) := by
  rw [divp_mul_eq_mul_divp, divp_assoc', divp_divp_eq_divp_mul]

variable [Subsingleton αˣ] {a b : α}

@[to_additive]
theorem eq_one_of_mul_right (h : a * b = 1) : a = 1 :=
  congr_arg Units.inv <| Subsingleton.elim (Units.mk _ _ (by rwa [mul_comm]) h) 1

@[to_additive]
theorem eq_one_of_mul_left (h : a * b = 1) : b = 1 :=
  congr_arg Units.inv <| Subsingleton.elim (Units.mk _ _ h <| by rwa [mul_comm]) 1

@[to_additive (attr := simp)]
theorem mul_eq_one : a * b = 1 ↔ a = 1 ∧ b = 1 :=
  ⟨fun h => ⟨eq_one_of_mul_right h, eq_one_of_mul_left h⟩, by
    rintro ⟨rfl, rfl⟩
    exact mul_one _⟩

@[to_additive] theorem mul_ne_one : a * b ≠ 1 ↔ a ≠ 1 ∨ b ≠ 1 := by rw [not_iff_comm]; simp

end CommMonoid

/-!
# `IsUnit` predicate
-/


section IsUnit

variable {M : Type*}

@[to_additive (attr := nontriviality)]
theorem isUnit_of_subsingleton [Monoid M] [Subsingleton M] (a : M) : IsUnit a :=
  ⟨⟨a, a, by subsingleton, by subsingleton⟩, rfl⟩

@[to_additive]
instance [Monoid M] : CanLift M Mˣ Units.val IsUnit :=
  { prf := fun _ ↦ id }

/-- A subsingleton `Monoid` has a unique unit. -/
@[to_additive "A subsingleton `AddMonoid` has a unique additive unit."]
instance [Monoid M] [Subsingleton M] : Unique Mˣ where
  uniq _ := Units.val_eq_one.mp (by subsingleton)

section Monoid
variable [Monoid M]

theorem units_eq_one [Subsingleton Mˣ] (u : Mˣ) : u = 1 := by subsingleton

end Monoid

namespace IsUnit

section Monoid

variable [Monoid M] {a b c : M}

@[to_additive]
theorem mul_left_inj (h : IsUnit a) : b * a = c * a ↔ b = c :=
  let ⟨u, hu⟩ := h
  hu ▸ u.mul_left_inj

@[to_additive]
theorem mul_right_inj (h : IsUnit a) : a * b = a * c ↔ b = c :=
  let ⟨u, hu⟩ := h
  hu ▸ u.mul_right_inj

@[to_additive]
protected theorem mul_left_cancel (h : IsUnit a) : a * b = a * c → b = c :=
  h.mul_right_inj.1

@[to_additive]
protected theorem mul_right_cancel (h : IsUnit b) : a * b = c * b → a = c :=
  h.mul_left_inj.1

@[to_additive]
theorem mul_eq_right (h : IsUnit b) : a * b = b ↔ a = 1 := calc
  a * b = b ↔ a * b = 1 * b := by rw [one_mul]
    _ ↔ a = 1 := by rw [h.mul_left_inj]

@[to_additive]
theorem mul_eq_left (h : IsUnit a) : a * b = a ↔ b = 1 := calc
  a * b = a ↔ a * b = a * 1 := by rw [mul_one]
    _ ↔ b = 1 := by rw [h.mul_right_inj]

@[to_additive]
protected theorem mul_right_injective (h : IsUnit a) : Injective (a * ·) :=
  fun _ _ => h.mul_left_cancel

@[to_additive]
protected theorem mul_left_injective (h : IsUnit b) : Injective (· * b) :=
  fun _ _ => h.mul_right_cancel

@[to_additive]
theorem isUnit_iff_mulLeft_bijective {a : M} :
    IsUnit a ↔ Function.Bijective (a * ·) :=
  ⟨fun h ↦ ⟨h.mul_right_injective, fun y ↦ ⟨h.unit⁻¹ * y, by simp [← mul_assoc]⟩⟩, fun h ↦
    ⟨⟨a, _, (h.2 1).choose_spec, h.1
      (by simpa [mul_assoc] using congr_arg (· * a) (h.2 1).choose_spec)⟩, rfl⟩⟩

@[to_additive]
theorem isUnit_iff_mulRight_bijective {a : M} :
    IsUnit a ↔ Function.Bijective (· * a) :=
  ⟨fun h ↦ ⟨h.mul_left_injective, fun y ↦ ⟨y * h.unit⁻¹, by simp [mul_assoc]⟩⟩,
    fun h ↦ ⟨⟨a, _, h.1 (by simpa [mul_assoc] using congr_arg (a * ·) (h.2 1).choose_spec),
      (h.2 1).choose_spec⟩, rfl⟩⟩

end Monoid

section DivisionMonoid
variable [DivisionMonoid α] {a b c : α}

@[to_additive (attr := simp)]
protected lemma mul_inv_cancel_right (h : IsUnit b) (a : α) : a * b * b⁻¹ = a :=
  h.unit'.mul_inv_cancel_right _

@[to_additive (attr := simp)]
protected lemma inv_mul_cancel_right (h : IsUnit b) (a : α) : a * b⁻¹ * b = a :=
  h.unit'.inv_mul_cancel_right _

@[to_additive]
protected lemma eq_mul_inv_iff_mul_eq (h : IsUnit c) : a = b * c⁻¹ ↔ a * c = b :=
  h.unit'.eq_mul_inv_iff_mul_eq

@[to_additive]
protected lemma eq_inv_mul_iff_mul_eq (h : IsUnit b) : a = b⁻¹ * c ↔ b * a = c :=
  h.unit'.eq_inv_mul_iff_mul_eq

@[to_additive]
protected lemma inv_mul_eq_iff_eq_mul (h : IsUnit a) : a⁻¹ * b = c ↔ b = a * c :=
  h.unit'.inv_mul_eq_iff_eq_mul

@[to_additive]
protected lemma mul_inv_eq_iff_eq_mul (h : IsUnit b) : a * b⁻¹ = c ↔ a = c * b :=
  h.unit'.mul_inv_eq_iff_eq_mul

@[to_additive]
protected lemma mul_inv_eq_one (h : IsUnit b) : a * b⁻¹ = 1 ↔ a = b :=
  @Units.mul_inv_eq_one _ _ h.unit' _

@[to_additive]
protected lemma inv_mul_eq_one (h : IsUnit a) : a⁻¹ * b = 1 ↔ a = b :=
  @Units.inv_mul_eq_one _ _ h.unit' _

@[to_additive]
protected lemma mul_eq_one_iff_eq_inv (h : IsUnit b) : a * b = 1 ↔ a = b⁻¹ :=
  @Units.mul_eq_one_iff_eq_inv _ _ h.unit' _

@[to_additive]
protected lemma mul_eq_one_iff_inv_eq (h : IsUnit a) : a * b = 1 ↔ a⁻¹ = b :=
  @Units.mul_eq_one_iff_inv_eq _ _ h.unit' _

@[to_additive (attr := simp)]
protected lemma div_mul_cancel (h : IsUnit b) (a : α) : a / b * b = a := by
  rw [div_eq_mul_inv, h.inv_mul_cancel_right]

@[to_additive (attr := simp)]
protected lemma mul_div_cancel_right (h : IsUnit b) (a : α) : a * b / b = a := by
  rw [div_eq_mul_inv, h.mul_inv_cancel_right]

@[to_additive]
protected lemma mul_one_div_cancel (h : IsUnit a) : a * (1 / a) = 1 := by simp [h]

@[to_additive]
protected lemma one_div_mul_cancel (h : IsUnit a) : 1 / a * a = 1 := by simp [h]

@[to_additive]
protected lemma div_left_inj (h : IsUnit c) : a / c = b / c ↔ a = b := by
  simp only [div_eq_mul_inv]
  exact Units.mul_left_inj h.inv.unit'

@[to_additive]
protected lemma div_eq_iff (h : IsUnit b) : a / b = c ↔ a = c * b := by
  rw [div_eq_mul_inv, h.mul_inv_eq_iff_eq_mul]

@[to_additive]
protected lemma eq_div_iff (h : IsUnit c) : a = b / c ↔ a * c = b := by
  rw [div_eq_mul_inv, h.eq_mul_inv_iff_mul_eq]

@[to_additive]
protected lemma div_eq_of_eq_mul (h : IsUnit b) : a = c * b → a / b = c :=
  h.div_eq_iff.2

@[to_additive]
protected lemma eq_div_of_mul_eq (h : IsUnit c) : a * c = b → a = b / c :=
  h.eq_div_iff.2

@[to_additive]
protected lemma div_eq_one_iff_eq (h : IsUnit b) : a / b = 1 ↔ a = b :=
  ⟨eq_of_div_eq_one, fun hab => hab.symm ▸ h.div_self⟩

@[to_additive]
protected lemma div_mul_left (h : IsUnit b) : b / (a * b) = 1 / a := by
  rw [h.div_mul_cancel_right, one_div]

@[to_additive]
protected lemma mul_mul_div (a : α) (h : IsUnit b) : a * b * (1 / b) = a := by simp [h]

end DivisionMonoid

section DivisionCommMonoid
variable [DivisionCommMonoid α] {a b c d : α}

@[to_additive]
protected lemma div_mul_right (h : IsUnit a) (b : α) : a / (a * b) = 1 / b := by
  rw [mul_comm, h.div_mul_left]

@[to_additive]
protected lemma mul_div_cancel_left (h : IsUnit a) (b : α) : a * b / a = b := by
  rw [mul_comm, h.mul_div_cancel_right]

@[to_additive]
protected lemma mul_div_cancel (h : IsUnit a) (b : α) : a * (b / a) = b := by
  rw [mul_comm, h.div_mul_cancel]

@[to_additive]
protected lemma mul_eq_mul_of_div_eq_div (hb : IsUnit b) (hd : IsUnit d)
    (a c : α) (h : a / b = c / d) : a * d = c * b := by
  rw [← mul_one a, ← hb.div_self, ← mul_comm_div, h, div_mul_eq_mul_div, hd.div_mul_cancel]

@[to_additive]
protected lemma div_eq_div_iff (hb : IsUnit b) (hd : IsUnit d) :
    a / b = c / d ↔ a * d = c * b := by
  rw [← (hb.mul hd).mul_left_inj, ← mul_assoc, hb.div_mul_cancel, ← mul_assoc, mul_right_comm,
    hd.div_mul_cancel]

@[to_additive]
protected lemma mul_inv_eq_mul_inv_iff (hb : IsUnit b) (hd : IsUnit d) :
    a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b := by
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, hb.div_eq_div_iff hd]

@[to_additive]
protected lemma inv_mul_eq_inv_mul_iff (hb : IsUnit b) (hd : IsUnit d) :
    b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b := by
  rw [← div_eq_inv_mul, ← div_eq_inv_mul, hb.div_eq_div_iff hd]

@[to_additive]
protected lemma div_div_cancel (h : IsUnit a) : a / (a / b) = b := by
  rw [div_div_eq_mul_div, h.mul_div_cancel_left]

@[to_additive]
protected lemma div_div_cancel_left (h : IsUnit a) : a / b / a = b⁻¹ := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm, h.mul_inv_cancel, one_mul]

end DivisionCommMonoid
end IsUnit

-- namespace
end IsUnit
