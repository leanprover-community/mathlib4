/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Units in semirings and rings

-/


universe u v w x

variable {α : Type u} {β : Type v} {R : Type x}

open Function

namespace Units

section HasDistribNeg

variable [Monoid α] [HasDistribNeg α]

/-- Each element of the group of units of a ring has an additive inverse. -/
instance : Neg αˣ :=
  ⟨fun u => ⟨-↑u, -↑u⁻¹, by simp, by simp⟩⟩

/-- Representing an element of a ring's unit group as an element of the ring commutes with
    mapping this element to its additive inverse. -/
@[simp, norm_cast]
protected theorem val_neg (u : αˣ) : (↑(-u) : α) = -u :=
  rfl

@[simp, norm_cast]
protected theorem coe_neg_one : ((-1 : αˣ) : α) = -1 :=
  rfl

instance : HasDistribNeg αˣ :=
  Units.ext.hasDistribNeg _ Units.val_neg Units.val_mul

@[field_simps]
theorem neg_divp (a : α) (u : αˣ) : -(a /ₚ u) = -a /ₚ u := by simp only [divp, neg_mul]

end HasDistribNeg

section Semiring

variable [Semiring α]

-- Needs to have higher simp priority than divp_add_divp. 1000 is the default priority.
@[field_simps 1010]
theorem divp_add_divp_same (a b : α) (u : αˣ) : a /ₚ u + b /ₚ u = (a + b) /ₚ u := by
  simp only [divp, add_mul]

@[field_simps]
theorem add_divp (a b : α) (u : αˣ) : a + b /ₚ u = (a * u + b) /ₚ u := by
  simp only [divp, add_mul, Units.mul_inv_cancel_right]

@[field_simps]
theorem divp_add (a b : α) (u : αˣ) : a /ₚ u + b = (a + b * u) /ₚ u := by
  simp only [divp, add_mul, Units.mul_inv_cancel_right]

end Semiring

section Ring

variable [Ring α]

-- Needs to have higher simp priority than divp_sub_divp. 1000 is the default priority.
@[field_simps 1010]
theorem divp_sub_divp_same (a b : α) (u : αˣ) : a /ₚ u - b /ₚ u = (a - b) /ₚ u := by
  rw [sub_eq_add_neg, sub_eq_add_neg, neg_divp, divp_add_divp_same]

@[field_simps]
theorem sub_divp (a b : α) (u : αˣ) : a - b /ₚ u = (a * u - b) /ₚ u := by
  simp only [divp, sub_mul, Units.mul_inv_cancel_right]

@[field_simps]
theorem divp_sub (a b : α) (u : αˣ) : a /ₚ u - b = (a - b * u) /ₚ u := by
  simp only [divp, sub_mul, sub_right_inj]
  rw [mul_assoc, Units.mul_inv, mul_one]

@[simp]
protected theorem map_neg {F : Type*} [Ring β] [FunLike F α β] [RingHomClass F α β]
    (f : F) (u : αˣ) : map (f : α →* β) (-u) = -map (f : α →* β) u :=
  ext (by simp only [coe_map, Units.val_neg, MonoidHom.coe_coe, map_neg])

protected theorem map_neg_one {F : Type*} [Ring β] [FunLike F α β] [RingHomClass F α β]
    (f : F) : map (f : α →* β) (-1) = -1 := by
  simp only [Units.map_neg, map_one]

end Ring

end Units

theorem IsUnit.neg [Monoid α] [HasDistribNeg α] {a : α} : IsUnit a → IsUnit (-a)
  | ⟨x, hx⟩ => hx ▸ (-x).isUnit

@[simp]
theorem IsUnit.neg_iff [Monoid α] [HasDistribNeg α] (a : α) : IsUnit (-a) ↔ IsUnit a :=
  ⟨fun h => neg_neg a ▸ h.neg, IsUnit.neg⟩

theorem isUnit_neg_one [Monoid α] [HasDistribNeg α] : IsUnit (-1 : α) := isUnit_one.neg

theorem IsUnit.sub_iff [Ring α] {x y : α} : IsUnit (x - y) ↔ IsUnit (y - x) :=
  (IsUnit.neg_iff _).symm.trans <| neg_sub x y ▸ Iff.rfl

namespace Units

@[field_simps]
theorem divp_add_divp [CommSemiring α] (a b : α) (u₁ u₂ : αˣ) :
    a /ₚ u₁ + b /ₚ u₂ = (a * u₂ + u₁ * b) /ₚ (u₁ * u₂) := by
  simp only [divp, add_mul, mul_inv_rev, val_mul]
  rw [mul_comm (↑u₁ * b), mul_comm b]
  rw [← mul_assoc, ← mul_assoc, mul_assoc a, mul_assoc (↑u₂⁻¹ : α), mul_inv, inv_mul, mul_one,
    mul_one]
  -- Porting note: `assoc_rw` not ported: `assoc_rw [mul_inv, mul_inv, mul_one, mul_one]`

@[field_simps]
theorem divp_sub_divp [CommRing α] (a b : α) (u₁ u₂ : αˣ) :
    a /ₚ u₁ - b /ₚ u₂ = (a * u₂ - u₁ * b) /ₚ (u₁ * u₂) := by
  simp only [sub_eq_add_neg, neg_divp, divp_add_divp, mul_neg]

theorem add_eq_mul_one_add_div [Semiring R] {a : Rˣ} {b : R} : ↑a + b = a * (1 + ↑a⁻¹ * b) := by
  rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]

end Units

namespace RingHom

section Semiring

variable [Semiring α] [Semiring β]

theorem isUnit_map (f : α →+* β) {a : α} : IsUnit a → IsUnit (f a) :=
  IsUnit.map f

end Semiring

end RingHom

variable [Semiring α] [Semiring β]
