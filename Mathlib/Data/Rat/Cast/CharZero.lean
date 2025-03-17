/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Data.Rat.Cast.Defs

/-!
# Casts of rational numbers into characteristic zero fields (or division rings).
-/

open Function

variable {F ι α β : Type*}

namespace Rat
variable [DivisionRing α] [CharZero α] {p q : ℚ}

@[stacks 09FR "Characteristic zero case."]
lemma cast_injective : Injective ((↑) : ℚ → α)
  | ⟨n₁, d₁, d₁0, c₁⟩, ⟨n₂, d₂, d₂0, c₂⟩, h => by
    have d₁a : (d₁ : α) ≠ 0 := Nat.cast_ne_zero.2 d₁0
    have d₂a : (d₂ : α) ≠ 0 := Nat.cast_ne_zero.2 d₂0
    rw [mk'_eq_divInt, mk'_eq_divInt] at h ⊢
    rw [cast_divInt_of_ne_zero, cast_divInt_of_ne_zero] at h <;> simp [d₁0, d₂0] at h ⊢
    rwa [eq_div_iff_mul_eq d₂a, division_def, mul_assoc, (d₁.cast_commute (d₂ : α)).inv_left₀.eq, ←
      mul_assoc, ← division_def, eq_comm, eq_div_iff_mul_eq d₁a, eq_comm, ← Int.cast_natCast d₁, ←
      Int.cast_mul, ← Int.cast_natCast d₂, ← Int.cast_mul, Int.cast_inj, ← mkRat_eq_iff d₁0 d₂0]
      at h

@[simp, norm_cast] lemma cast_inj : (p : α) = q ↔ p = q := cast_injective.eq_iff

@[simp, norm_cast] lemma cast_eq_zero : (p : α) = 0 ↔ p = 0 := cast_injective.eq_iff' cast_zero
lemma cast_ne_zero : (p : α) ≠ 0 ↔ p ≠ 0 := cast_eq_zero.ne

@[simp, norm_cast] lemma cast_add (p q : ℚ) : ↑(p + q) = (p + q : α) :=
  cast_add_of_ne_zero (Nat.cast_ne_zero.2 p.pos.ne') (Nat.cast_ne_zero.2 q.pos.ne')

@[simp, norm_cast] lemma cast_sub (p q : ℚ) : ↑(p - q) = (p - q : α) :=
  cast_sub_of_ne_zero (Nat.cast_ne_zero.2 p.pos.ne') (Nat.cast_ne_zero.2 q.pos.ne')

@[simp, norm_cast] lemma cast_mul (p q : ℚ) : ↑(p * q) = (p * q : α) :=
  cast_mul_of_ne_zero (Nat.cast_ne_zero.2 p.pos.ne') (Nat.cast_ne_zero.2 q.pos.ne')

variable (α) in
/-- Coercion `ℚ → α` as a `RingHom`. -/
def castHom : ℚ →+* α where
  toFun := (↑)
  map_one' := cast_one
  map_mul' := cast_mul
  map_zero' := cast_zero
  map_add' := cast_add

@[simp] lemma coe_castHom : ⇑(castHom α) = ((↑) : ℚ → α) := rfl

@[simp, norm_cast] lemma cast_inv (p : ℚ) : ↑(p⁻¹) = (p⁻¹ : α) := map_inv₀ (castHom α) _
@[simp, norm_cast] lemma cast_div (p q : ℚ) : ↑(p / q) = (p / q : α) := map_div₀ (castHom α) ..

@[simp, norm_cast]
lemma cast_zpow (p : ℚ) (n : ℤ) : ↑(p ^ n) = (p ^ n : α) := map_zpow₀ (castHom α) ..

@[norm_cast]
theorem cast_mk (a b : ℤ) : (a /. b : α) = a / b := by
  simp only [divInt_eq_div, cast_div, cast_intCast]

end Rat

namespace NNRat
variable [DivisionSemiring α] [CharZero α] {p q : ℚ≥0}

lemma cast_injective : Injective ((↑) : ℚ≥0 → α) := by
  rintro p q hpq
  rw [NNRat.cast_def, NNRat.cast_def, Commute.div_eq_div_iff] at hpq
  on_goal 1 => rw [← p.num_div_den, ← q.num_div_den, div_eq_div_iff]
  · norm_cast at hpq ⊢
  any_goals norm_cast
  any_goals apply den_ne_zero
  exact Nat.cast_commute ..

@[simp, norm_cast] lemma cast_inj : (p : α) = q ↔ p = q := cast_injective.eq_iff

@[simp, norm_cast] lemma cast_eq_zero : (q : α) = 0 ↔ q = 0 := by rw [← cast_zero, cast_inj]
lemma cast_ne_zero : (q : α) ≠ 0 ↔ q ≠ 0 := cast_eq_zero.not

@[simp, norm_cast] lemma cast_add (p q : ℚ≥0) : ↑(p + q) = (p + q : α) :=
  cast_add_of_ne_zero (Nat.cast_ne_zero.2 p.den_pos.ne') (Nat.cast_ne_zero.2 q.den_pos.ne')

@[simp, norm_cast] lemma cast_mul (p q) : (p * q : ℚ≥0) = (p * q : α) :=
  cast_mul_of_ne_zero (Nat.cast_ne_zero.2 p.den_pos.ne') (Nat.cast_ne_zero.2 q.den_pos.ne')

variable (α) in
/-- Coercion `ℚ≥0 → α` as a `RingHom`. -/
def castHom : ℚ≥0 →+* α where
  toFun := (↑)
  map_one' := cast_one
  map_mul' := cast_mul
  map_zero' := cast_zero
  map_add' := cast_add

@[simp, norm_cast] lemma coe_castHom : ⇑(castHom α) = (↑) := rfl

@[simp, norm_cast] lemma cast_inv (p) : (p⁻¹ : ℚ≥0) = (p : α)⁻¹ := map_inv₀ (castHom α) _
@[simp, norm_cast] lemma cast_div (p q) : (p / q : ℚ≥0) = (p / q : α) := map_div₀ (castHom α) ..

@[simp, norm_cast]
lemma cast_zpow (q : ℚ≥0) (p : ℤ) : ↑(q ^ p) = ((q : α) ^ p : α) := map_zpow₀ (castHom α) ..

@[simp]
lemma cast_divNat (a b : ℕ) : (divNat a b : α) = a / b := by
  rw [← cast_natCast, ← cast_natCast b, ← cast_div]
  congr
  ext
  apply Rat.mkRat_eq_div

end NNRat
