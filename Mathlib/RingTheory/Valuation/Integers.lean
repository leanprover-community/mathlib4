/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Ideal.LocalRing
import Mathlib.RingTheory.Localization.FractionRing

#align_import ring_theory.valuation.integers from "leanprover-community/mathlib"@"7b7da89322fe46a16bf03eeb345b0acfc73fe10e"

/-!
# Ring of integers under a given valuation

The elements with valuation less than or equal to 1.

TODO: Define characteristic predicate.
-/


universe u v w

namespace Valuation

section Ring

variable {R : Type u} {Γ₀ : Type v} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]
variable (v : Valuation R Γ₀)

/-- The ring of integers under a given valuation is the subring of elements with valuation ≤ 1. -/
def integer : Subring R where
  carrier := { x | v x ≤ 1 }
  one_mem' := le_of_eq v.map_one
  mul_mem' {x y} hx hy := by simp only [Set.mem_setOf_eq, _root_.map_mul, mul_le_one' hx hy]
  zero_mem' := by simp only [Set.mem_setOf_eq, _root_.map_zero, zero_le']
  add_mem' {x y} hx hy := le_trans (v.map_add x y) (max_le hx hy)
  neg_mem' {x} hx := by simp only [Set.mem_setOf_eq] at hx; simpa only [Set.mem_setOf_eq, map_neg]
#align valuation.integer Valuation.integer

lemma mem_integer_iff (r : R) : r ∈ v.integer ↔ v r ≤ 1 := by rfl

end Ring

section CommRing

variable {R : Type u} {Γ₀ : Type v} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]
variable (v : Valuation R Γ₀)
variable (O : Type w) [CommRing O] [Algebra O R]

/-- Given a valuation v : R → Γ₀ and a ring homomorphism O →+* R, we say that O is the integers of v
if f is injective, and its range is exactly `v.integer`. -/
structure Integers : Prop where
  hom_inj : Function.Injective (algebraMap O R)
  map_le_one : ∀ x, v (algebraMap O R x) ≤ 1
  exists_of_le_one : ∀ ⦃r⦄, v r ≤ 1 → ∃ x, algebraMap O R x = r
#align valuation.integers Valuation.Integers

-- typeclass shortcut
instance : Algebra v.integer R :=
  Algebra.ofSubring v.integer

theorem integer.integers : v.Integers v.integer :=
  { hom_inj := Subtype.coe_injective
    map_le_one := fun r => r.2
    exists_of_le_one := fun r hr => ⟨⟨r, hr⟩, rfl⟩ }
#align valuation.integer.integers Valuation.integer.integers

namespace Integers

variable {v O} [CommRing O] [Algebra O R]

theorem one_of_isUnit' {x : O} (hx : IsUnit x) (H : ∀ x, v (algebraMap O R x) ≤ 1) :
    v (algebraMap O R x) = 1 :=
  let ⟨u, hu⟩ := hx
  le_antisymm (H _) <| by
    rw [← v.map_one, ← (algebraMap O R).map_one, ← u.mul_inv, ← mul_one (v (algebraMap O R x)), hu,
      (algebraMap O R).map_mul, v.map_mul]
    exact mul_le_mul_left' (H (u⁻¹ : Units O)) _

variable (hv : Integers v O)

theorem one_of_isUnit {x : O} (hx : IsUnit x) : v (algebraMap O R x) = 1 :=
  one_of_isUnit' hx hv.map_le_one

/--
Let `O` be the integers of the valuation `v` on some commutative ring `R`. For every element `x` in
`O`, `x` is a unit in `O` if and only if the image of `x` in `R` is a unit and has valuation 1.
-/
theorem isUnit_of_one {x : O} (hx : IsUnit (algebraMap O R x)) (hvx : v (algebraMap O R x) = 1) :
    IsUnit x :=
  let ⟨u, hu⟩ := hx
  have h1 : v u ≤ 1 := hu.symm ▸ hv.2 x
  have h2 : v (u⁻¹ : Rˣ) ≤ 1 := by
    rw [← one_mul (v _), ← hvx, ← v.map_mul, ← hu, u.mul_inv, hu, hvx, v.map_one]
  let ⟨r1, hr1⟩ := hv.3 h1
  let ⟨r2, hr2⟩ := hv.3 h2
  ⟨⟨r1, r2, hv.1 <| by rw [RingHom.map_mul, RingHom.map_one, hr1, hr2, Units.mul_inv],
      hv.1 <| by rw [RingHom.map_mul, RingHom.map_one, hr1, hr2, Units.inv_mul]⟩,
    hv.1 <| hr1.trans hu⟩
#align valuation.integers.is_unit_of_one Valuation.Integers.isUnit_of_one

theorem le_of_dvd {x y : O} (h : x ∣ y) : v (algebraMap O R y) ≤ v (algebraMap O R x) := by
  let ⟨z, hz⟩ := h
  rw [← mul_one (v (algebraMap O R x)), hz, RingHom.map_mul, v.map_mul]
  exact mul_le_mul_left' (hv.2 z) _
#align valuation.integers.le_of_dvd Valuation.Integers.le_of_dvd

end Integers

end CommRing

section Field

variable {F : Type u} {Γ₀ : Type v} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
variable {v : Valuation F Γ₀} {O : Type w} [CommRing O] [Algebra O F] (hv : Integers v O)

namespace Integers

theorem dvd_of_le {x y : O} (h : v (algebraMap O F x) ≤ v (algebraMap O F y)) : y ∣ x :=
  by_cases
    (fun hy : algebraMap O F y = 0 =>
      have hx : x = 0 :=
        hv.1 <|
          (algebraMap O F).map_zero.symm ▸ (v.zero_iff.1 <| le_zero_iff.1 (v.map_zero ▸ hy ▸ h))
      hx.symm ▸ dvd_zero y)
    fun hy : algebraMap O F y ≠ 0 =>
    have : v ((algebraMap O F y)⁻¹ * algebraMap O F x) ≤ 1 := by
      rw [← v.map_one, ← inv_mul_cancel hy, v.map_mul, v.map_mul]
      exact mul_le_mul_left' h _
    let ⟨z, hz⟩ := hv.3 this
    ⟨z, hv.1 <| ((algebraMap O F).map_mul y z).symm ▸ hz.symm ▸ (mul_inv_cancel_left₀ hy _).symm⟩
#align valuation.integers.dvd_of_le Valuation.Integers.dvd_of_le

theorem dvd_iff_le {x y : O} : x ∣ y ↔ v (algebraMap O F y) ≤ v (algebraMap O F x) :=
  ⟨hv.le_of_dvd, hv.dvd_of_le⟩
#align valuation.integers.dvd_iff_le Valuation.Integers.dvd_iff_le

theorem le_iff_dvd {x y : O} : v (algebraMap O F x) ≤ v (algebraMap O F y) ↔ y ∣ x :=
  ⟨hv.dvd_of_le, hv.le_of_dvd⟩
#align valuation.integers.le_iff_dvd Valuation.Integers.le_iff_dvd

/--
This is the special case of `Valuation.Integers.isUnit_of_one` when the valuation is defined
over a field. Let `v` be a valuation on some field `F` and `O` be its integers. For every element
`x` in `O`, `x` is a unit in `O` if and only if the image of `x` in `F` has valuation 1.
-/
theorem isUnit_of_one' {x : O} (hvx : v (algebraMap O F x) = 1) :
    IsUnit x := by
  apply isUnit_of_one hv _ hvx
  apply IsUnit.mk0
  rw [← v.ne_zero_iff]
  simp only [hvx, ne_eq, one_ne_zero, not_false_eq_true]

end Integers

instance instIsFractionRingInteger: IsFractionRing v.integer F where
  map_units' x := by
    field_simp
    apply ((injective_iff_map_eq_zero _).mp (integer.integers v).hom_inj x).mt
    exact nonZeroDivisors.coe_ne_zero x
  surj' z := by
    by_cases h : v z ≤ 1
    · use ⟨⟨z, h⟩, 1⟩
      simp only [OneMemClass.coe_one, _root_.map_one, mul_one]
      rfl
    · simp only [not_le] at h
      have : z ≠ 0 := by
        by_contra! hz
        simp only [hz, _root_.map_zero, not_lt_zero'] at h
      let zinv : nonZeroDivisors v.integer := {
        val := ⟨z⁻¹, le_of_lt ((v.one_lt_val_iff this).mp h)⟩
        property := by
          apply mem_nonZeroDivisors_of_ne_zero
          apply Subtype.ext_iff.not.mpr
          simp only [ZeroMemClass.coe_zero, inv_eq_zero, this, not_false_eq_true]
      }
      use ⟨1, zinv⟩
      calc
      _ = z * z⁻¹ := by rfl
      _ = 1 := by field_simp
  exists_of_eq h := by
    use 1
    simp only [OneMemClass.coe_one, (integer.integers v).hom_inj h, one_mul]

end Field

end Valuation
