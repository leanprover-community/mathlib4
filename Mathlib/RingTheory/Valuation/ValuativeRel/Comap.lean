/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic

/-!
# Comap for Valuative Relations

We define the pullback (comap) of a `ValuativeRel` along a ring homomorphism.

## Main definitions

* `ValuativeRel.comap φ v` : Given `φ : A →+* B` and a valuative relation `v` on `B`,
  the induced `ValuativeRel A` defined by `a₁ ≤ᵥ a₂ ↔ φ(a₁) ≤ᵥ φ(a₂)`.

## Main results

* `ValuativeRel.not_vle_zero_of_isUnit` : If `f` is a unit, then `¬ f ≤ᵥ 0`.
-/

@[expose] public section

namespace ValuativeRel

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The pullback of a `ValuativeRel` along `φ : A →+* B`:
`a₁ ≤ᵥ a₂ ↔ φ(a₁) ≤ᵥ φ(a₂)`. -/
@[reducible]
def comap (φ : A →+* B) (v : ValuativeRel B) : ValuativeRel A where
  vle a₁ a₂ := v.vle (φ a₁) (φ a₂)
  vle_total a₁ a₂ := v.vle_total (φ a₁) (φ a₂)
  vle_trans h₁ h₂ := v.vle_trans h₁ h₂
  vle_add h₁ h₂ := by simpa [map_add] using v.vle_add h₁ h₂
  mul_vle_mul_left h z := by simpa [map_mul] using v.mul_vle_mul_left h (φ z)
  vle_mul_cancel h₀ h := by
    rw [map_zero] at h₀
    simpa [map_mul] using v.vle_mul_cancel h₀ (by simpa [map_mul] using h)
  not_vle_one_zero := by simp [map_one, map_zero, v.not_vle_one_zero]

@[simp]
theorem comap_vle (φ : A →+* B) (v : ValuativeRel B) (a₁ a₂ : A) :
    (comap φ v).vle a₁ a₂ = v.vle (φ a₁) (φ a₂) := rfl

/-- If `f` is a unit, then `¬ f ≤ᵥ 0`. -/
theorem not_vle_zero_of_isUnit [ValuativeRel A] {f : A} (hu : IsUnit f) :
    ¬ f ≤ᵥ (0 : A) := by
  obtain ⟨u, rfl⟩ := hu
  intro h
  have := mul_vle_mul_right h (↑u⁻¹ : A)
  rw [Units.inv_mul, mul_zero] at this
  exact absurd this (not_vle.mpr zero_vlt_one)

end ValuativeRel

end
