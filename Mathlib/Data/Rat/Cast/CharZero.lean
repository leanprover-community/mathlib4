/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Data.Rat.Cast.Defs

#align_import data.rat.cast from "leanprover-community/mathlib"@"acebd8d49928f6ed8920e502a6c90674e75bd441"


/-!
# Casts of rational numbers into characteristic zero fields (or division rings).
-/


variable {F ι α β : Type*}

namespace Rat

open Rat

section WithDivRing

variable [DivisionRing α]

@[simp, norm_cast]
theorem cast_inj [CharZero α] : ∀ {m n : ℚ}, (m : α) = n ↔ m = n
  | ⟨n₁, d₁, d₁0, c₁⟩, ⟨n₂, d₂, d₂0, c₂⟩ => by
    refine ⟨fun h => ?_, congr_arg _⟩
    have d₁a : (d₁ : α) ≠ 0 := Nat.cast_ne_zero.2 d₁0
    have d₂a : (d₂ : α) ≠ 0 := Nat.cast_ne_zero.2 d₂0
    rw [mk'_eq_divInt, mk'_eq_divInt] at h ⊢
    rw [cast_divInt_of_ne_zero, cast_divInt_of_ne_zero] at h <;> simp [d₁0, d₂0] at h ⊢
    rwa [eq_div_iff_mul_eq d₂a, division_def, mul_assoc, (d₁.cast_commute (d₂ : α)).inv_left₀.eq, ←
      mul_assoc, ← division_def, eq_comm, eq_div_iff_mul_eq d₁a, eq_comm, ← Int.cast_natCast d₁, ←
      Int.cast_mul, ← Int.cast_natCast d₂, ← Int.cast_mul, Int.cast_inj, ← mkRat_eq_iff d₁0 d₂0]
      at h
#align rat.cast_inj Rat.cast_inj

theorem cast_injective [CharZero α] : Function.Injective ((↑) : ℚ → α)
  | _, _ => cast_inj.1
#align rat.cast_injective Rat.cast_injective

@[simp]
theorem cast_eq_zero [CharZero α] {n : ℚ} : (n : α) = 0 ↔ n = 0 := by rw [← cast_zero, cast_inj]
#align rat.cast_eq_zero Rat.cast_eq_zero

theorem cast_ne_zero [CharZero α] {n : ℚ} : (n : α) ≠ 0 ↔ n ≠ 0 :=
  not_congr cast_eq_zero
#align rat.cast_ne_zero Rat.cast_ne_zero

@[simp, norm_cast]
theorem cast_add [CharZero α] (m n) : ((m + n : ℚ) : α) = m + n :=
  cast_add_of_ne_zero (Nat.cast_ne_zero.2 <| ne_of_gt m.pos) (Nat.cast_ne_zero.2 <| ne_of_gt n.pos)
#align rat.cast_add Rat.cast_add

@[simp, norm_cast]
theorem cast_sub [CharZero α] (m n) : ((m - n : ℚ) : α) = m - n :=
  cast_sub_of_ne_zero (Nat.cast_ne_zero.2 <| ne_of_gt m.pos) (Nat.cast_ne_zero.2 <| ne_of_gt n.pos)
#align rat.cast_sub Rat.cast_sub

@[simp, norm_cast]
theorem cast_mul [CharZero α] (m n) : ((m * n : ℚ) : α) = m * n :=
  cast_mul_of_ne_zero (Nat.cast_ne_zero.2 <| ne_of_gt m.pos) (Nat.cast_ne_zero.2 <| ne_of_gt n.pos)
#align rat.cast_mul Rat.cast_mul

section

set_option linter.deprecated false

@[simp, norm_cast]
theorem cast_bit0 [CharZero α] (n : ℚ) : ((bit0 n : ℚ) : α) = (bit0 n : α) :=
  cast_add _ _
#align rat.cast_bit0 Rat.cast_bit0

@[simp, norm_cast]
theorem cast_bit1 [CharZero α] (n : ℚ) : ((bit1 n : ℚ) : α) = (bit1 n : α) := by
  rw [bit1, cast_add, cast_one, cast_bit0]; rfl
#align rat.cast_bit1 Rat.cast_bit1

end

variable (α)
variable [CharZero α]

/-- Coercion `ℚ → α` as a `RingHom`. -/
def castHom : ℚ →+* α where
  toFun := (↑)
  map_one' := cast_one
  map_mul' := cast_mul
  map_zero' := cast_zero
  map_add' := cast_add
#align rat.cast_hom Rat.castHom

variable {α}

@[simp]
theorem coe_cast_hom : ⇑(castHom α) = ((↑) : ℚ → α) :=
  rfl
#align rat.coe_cast_hom Rat.coe_cast_hom

@[simp, norm_cast]
theorem cast_inv (n) : ((n⁻¹ : ℚ) : α) = (n : α)⁻¹ :=
  map_inv₀ (castHom α) _
#align rat.cast_inv Rat.cast_inv

@[simp, norm_cast]
theorem cast_div (m n) : ((m / n : ℚ) : α) = m / n :=
  map_div₀ (castHom α) _ _
#align rat.cast_div Rat.cast_div

@[simp, norm_cast]
theorem cast_zpow (q : ℚ) (n : ℤ) : ((q ^ n : ℚ) : α) = (q : α) ^ n :=
  map_zpow₀ (castHom α) q n
#align rat.cast_zpow Rat.cast_zpow

@[norm_cast]
theorem cast_mk (a b : ℤ) : (a /. b : α) = a / b := by
  simp only [divInt_eq_div, cast_div, cast_intCast]
#align rat.cast_mk Rat.cast_mk

@[simp, norm_cast]
theorem cast_pow (q : ℚ) (k : ℕ) : ↑(q ^ k) = (q : α) ^ k :=
  (castHom α).map_pow q k
#align rat.cast_pow Rat.cast_pow

end WithDivRing

end Rat
