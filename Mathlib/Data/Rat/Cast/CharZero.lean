/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Int.CharZero
import Mathlib.Algebra.GroupWithZero.Units.Lemmas

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
    refine' ⟨fun h => _, congr_arg _⟩
    have d₁a : (d₁ : α) ≠ 0 := Nat.cast_ne_zero.2 d₁0
    have d₂a : (d₂ : α) ≠ 0 := Nat.cast_ne_zero.2 d₂0
    rw [num_den', num_den'] at h ⊢
    rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero] at h <;> simp [d₁0, d₂0] at h ⊢
    rwa [eq_div_iff_mul_eq d₂a, division_def, mul_assoc, (d₁.cast_commute (d₂ : α)).inv_left₀.eq, ←
      mul_assoc, ← division_def, eq_comm, eq_div_iff_mul_eq d₁a, eq_comm, ← Int.cast_ofNat d₁, ←
      Int.cast_mul, ← Int.cast_ofNat d₂, ← Int.cast_mul, Int.cast_inj, ← mkRat_eq_iff d₁0 d₂0] at h

theorem cast_injective [CharZero α] : Function.Injective ((↑) : ℚ → α)
  | _, _ => cast_inj.1

@[simp]
theorem cast_eq_zero [CharZero α] {n : ℚ} : (n : α) = 0 ↔ n = 0 := by rw [← cast_zero, cast_inj]

theorem cast_ne_zero [CharZero α] {n : ℚ} : (n : α) ≠ 0 ↔ n ≠ 0 :=
  not_congr cast_eq_zero

@[simp, norm_cast]
theorem cast_add [CharZero α] (m n) : ((m + n : ℚ) : α) = m + n :=
  cast_add_of_ne_zero (Nat.cast_ne_zero.2 <| ne_of_gt m.pos) (Nat.cast_ne_zero.2 <| ne_of_gt n.pos)

@[simp, norm_cast]
theorem cast_sub [CharZero α] (m n) : ((m - n : ℚ) : α) = m - n :=
  cast_sub_of_ne_zero (Nat.cast_ne_zero.2 <| ne_of_gt m.pos) (Nat.cast_ne_zero.2 <| ne_of_gt n.pos)

@[simp, norm_cast]
theorem cast_mul [CharZero α] (m n) : ((m * n : ℚ) : α) = m * n :=
  cast_mul_of_ne_zero (Nat.cast_ne_zero.2 <| ne_of_gt m.pos) (Nat.cast_ne_zero.2 <| ne_of_gt n.pos)

section

set_option linter.deprecated false

@[simp, norm_cast]
theorem cast_bit0 [CharZero α] (n : ℚ) : ((bit0 n : ℚ) : α) = (bit0 n : α) :=
  cast_add _ _

@[simp, norm_cast]
theorem cast_bit1 [CharZero α] (n : ℚ) : ((bit1 n : ℚ) : α) = (bit1 n : α) := by
  rw [bit1, cast_add, cast_one, cast_bit0]; rfl

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

variable {α}

@[simp]
theorem coe_cast_hom : ⇑(castHom α) = ((↑) : ℚ → α) :=
  rfl

@[simp, norm_cast]
theorem cast_inv (n) : ((n⁻¹ : ℚ) : α) = (n : α)⁻¹ :=
  map_inv₀ (castHom α) _

@[simp, norm_cast]
theorem cast_div (m n) : ((m / n : ℚ) : α) = m / n :=
  map_div₀ (castHom α) _ _

@[simp, norm_cast]
theorem cast_zpow (q : ℚ) (n : ℤ) : ((q ^ n : ℚ) : α) = (q : α) ^ n :=
  map_zpow₀ (castHom α) q n

@[norm_cast]
theorem cast_mk (a b : ℤ) : (a /. b : α) = a / b := by
  simp only [divInt_eq_div, cast_div, cast_coe_int]

@[simp, norm_cast]
theorem cast_pow (q) (k : ℕ) : ((q : ℚ) ^ k : α) = (q : α) ^ k :=
  (castHom α).map_pow q k

end WithDivRing

end Rat

-- Guard against import creep regression.
assert_not_exists zpow_add₀
