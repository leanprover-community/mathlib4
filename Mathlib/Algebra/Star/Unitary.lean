/-
Copyright (c) 2022 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam, Frédéric Dupuis
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.GroupTheory.Submonoid.Operations

#align_import algebra.star.unitary from "leanprover-community/mathlib"@"247a102b14f3cebfee126293341af5f6bed00237"

/-!
# Unitary elements of a star monoid

This file defines `unitary R`, where `R` is a star monoid, as the submonoid made of the elements
that satisfy `star U * U = 1` and `U * star U = 1`, and these form a group.
This includes, for instance, unitary operators on Hilbert spaces.

See also `Matrix.UnitaryGroup` for specializations to `unitary (Matrix n n R)`.

## Tags

unitary
-/


/-- In a *-monoid, `unitary R` is the submonoid consisting of all the elements `U` of
`R` such that `star U * U = 1` and `U * star U = 1`.
-/
def unitary (R : Type*) [Monoid R] [StarSemigroup R] : Submonoid R where
  carrier := { U | star U * U = 1 ∧ U * star U = 1 }
  one_mem' := by simp only [mul_one, and_self_iff, Set.mem_setOf_eq, star_one]
                 -- 🎉 no goals
  mul_mem' := @fun U B ⟨hA₁, hA₂⟩ ⟨hB₁, hB₂⟩ => by
    -- ⊢ star (U * B) * (U * B) = 1
    refine' ⟨_, _⟩
    · calc
        star (U * B) * (U * B) = star B * star U * U * B := by simp only [mul_assoc, star_mul]
        _ = star B * (star U * U) * B := by rw [← mul_assoc]
        _ = 1 := by rw [hA₁, mul_one, hB₁]
    · calc
        U * B * star (U * B) = U * B * (star B * star U) := by rw [star_mul]
        _ = U * (B * star B) * star U := by simp_rw [← mul_assoc]
        _ = 1 := by rw [hB₂, mul_one, hA₂]
#align unitary unitary

variable {R : Type*}

namespace unitary

section Monoid

variable [Monoid R] [StarSemigroup R]

theorem mem_iff {U : R} : U ∈ unitary R ↔ star U * U = 1 ∧ U * star U = 1 :=
  Iff.rfl
#align unitary.mem_iff unitary.mem_iff

@[simp]
theorem star_mul_self_of_mem {U : R} (hU : U ∈ unitary R) : star U * U = 1 :=
  hU.1
#align unitary.star_mul_self_of_mem unitary.star_mul_self_of_mem

@[simp]
theorem mul_star_self_of_mem {U : R} (hU : U ∈ unitary R) : U * star U = 1 :=
  hU.2
#align unitary.mul_star_self_of_mem unitary.mul_star_self_of_mem

theorem star_mem {U : R} (hU : U ∈ unitary R) : star U ∈ unitary R :=
  ⟨by rw [star_star, mul_star_self_of_mem hU], by rw [star_star, star_mul_self_of_mem hU]⟩
      -- 🎉 no goals
                                                  -- 🎉 no goals
#align unitary.star_mem unitary.star_mem

@[simp]
theorem star_mem_iff {U : R} : star U ∈ unitary R ↔ U ∈ unitary R :=
  ⟨fun h => star_star U ▸ star_mem h, star_mem⟩
#align unitary.star_mem_iff unitary.star_mem_iff

instance : Star (unitary R) :=
  ⟨fun U => ⟨star U, star_mem U.prop⟩⟩

@[simp, norm_cast]
theorem coe_star {U : unitary R} : ↑(star U) = (star U : R) :=
  rfl
#align unitary.coe_star unitary.coe_star

theorem coe_star_mul_self (U : unitary R) : (star U : R) * U = 1 :=
  star_mul_self_of_mem U.prop
#align unitary.coe_star_mul_self unitary.coe_star_mul_self

theorem coe_mul_star_self (U : unitary R) : (U : R) * star U = 1 :=
  mul_star_self_of_mem U.prop
#align unitary.coe_mul_star_self unitary.coe_mul_star_self

@[simp]
theorem star_mul_self (U : unitary R) : star U * U = 1 :=
  Subtype.ext <| coe_star_mul_self U
#align unitary.star_mul_self unitary.star_mul_self

@[simp]
theorem mul_star_self (U : unitary R) : U * star U = 1 :=
  Subtype.ext <| coe_mul_star_self U
#align unitary.mul_star_self unitary.mul_star_self

instance : Group (unitary R) :=
  { Submonoid.toMonoid _ with
    inv := star
    mul_left_inv := star_mul_self }

instance : InvolutiveStar (unitary R) :=
  ⟨by
    intro x
    -- ⊢ star (star x) = x
    ext
    -- ⊢ ↑(star (star x)) = ↑x
    rw [coe_star, coe_star, star_star]⟩
    -- 🎉 no goals

instance : StarSemigroup (unitary R) :=
  ⟨by
    intro x y
    -- ⊢ star (x * y) = star y * star x
    ext
    -- ⊢ ↑(star (x * y)) = ↑(star y * star x)
    rw [coe_star, Submonoid.coe_mul, Submonoid.coe_mul, coe_star, coe_star, star_mul]⟩
    -- 🎉 no goals

instance : Inhabited (unitary R) :=
  ⟨1⟩

theorem star_eq_inv (U : unitary R) : star U = U⁻¹ :=
  rfl
#align unitary.star_eq_inv unitary.star_eq_inv

theorem star_eq_inv' : (star : unitary R → unitary R) = Inv.inv :=
  rfl
#align unitary.star_eq_inv' unitary.star_eq_inv'

/-- The unitary elements embed into the units. -/
@[simps]
def toUnits : unitary R →* Rˣ
    where
  toFun x := ⟨x, ↑x⁻¹, coe_mul_star_self x, coe_star_mul_self x⟩
  map_one' := Units.ext rfl
  map_mul' _ _ := Units.ext rfl
#align unitary.to_units unitary.toUnits

theorem to_units_injective : Function.Injective (toUnits : unitary R → Rˣ) := fun _ _ h =>
  Subtype.ext <| Units.ext_iff.mp h
#align unitary.to_units_injective unitary.to_units_injective

end Monoid

section CommMonoid

variable [CommMonoid R] [StarSemigroup R]

instance : CommGroup (unitary R) :=
  { inferInstanceAs (Group (unitary R)), Submonoid.toCommMonoid _ with }

theorem mem_iff_star_mul_self {U : R} : U ∈ unitary R ↔ star U * U = 1 :=
  mem_iff.trans <| and_iff_left_of_imp fun h => mul_comm (star U) U ▸ h
#align unitary.mem_iff_star_mul_self unitary.mem_iff_star_mul_self

theorem mem_iff_self_mul_star {U : R} : U ∈ unitary R ↔ U * star U = 1 :=
  mem_iff.trans <| and_iff_right_of_imp fun h => mul_comm U (star U) ▸ h
#align unitary.mem_iff_self_mul_star unitary.mem_iff_self_mul_star

end CommMonoid

section GroupWithZero

variable [GroupWithZero R] [StarSemigroup R]

@[norm_cast]
theorem coe_inv (U : unitary R) : ↑U⁻¹ = (U⁻¹ : R) :=
  eq_inv_of_mul_eq_one_right <| coe_mul_star_self _
#align unitary.coe_inv unitary.coe_inv

@[norm_cast]
theorem coe_div (U₁ U₂ : unitary R) : ↑(U₁ / U₂) = (U₁ / U₂ : R) := by
  simp only [div_eq_mul_inv, coe_inv, Submonoid.coe_mul]
  -- 🎉 no goals
#align unitary.coe_div unitary.coe_div

@[norm_cast]
theorem coe_zpow (U : unitary R) (z : ℤ) : ↑(U ^ z) = (U : R) ^ z := by
  induction z
  -- ⊢ ↑(U ^ Int.ofNat a✝) = ↑U ^ Int.ofNat a✝
  · simp [SubmonoidClass.coe_pow]
    -- 🎉 no goals
  · simp [coe_inv]
    -- 🎉 no goals
#align unitary.coe_zpow unitary.coe_zpow

end GroupWithZero

section Ring

variable [Ring R] [StarRing R]

instance : Neg (unitary R)
    where neg U :=
    ⟨-U, by simp [mem_iff, star_neg, neg_mul_neg]⟩
            -- 🎉 no goals

@[norm_cast]
theorem coe_neg (U : unitary R) : ↑(-U) = (-U : R) :=
  rfl
#align unitary.coe_neg unitary.coe_neg

instance : HasDistribNeg (unitary R) :=
  Subtype.coe_injective.hasDistribNeg _ coe_neg (unitary R).coe_mul

end Ring

end unitary
