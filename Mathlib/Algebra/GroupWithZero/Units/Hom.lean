/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Commute
public import Mathlib.Algebra.GroupWithZero.Hom

/-! # Homomorphism interactions with `Ring.inverse` -/

@[expose] public section

assert_not_exists DenselyOrdered MulAction Ring

open scoped Ring

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀']
    [FunLike F M₀ M₀']

protected theorem IsUnit.map_ringInverse [MonoidHomClass F M₀ M₀'] (f : F) {a : M₀} (h : IsUnit a) :
    f a⁻¹ʳ = (f a)⁻¹ʳ := by
  lift a to M₀ˣ using h
  simpa [Ring.inverse_unit] using (Ring.inverse_unit (Units.map (.ofClass f) a)).symm

-- not marked `simp`, even at low priority because it applies unwanted in too many scenarios
theorem map_ringInverse {F G₀ : Type*} [GroupWithZero G₀] [FunLike F G₀ M₀]
    [MonoidWithZeroHomClass F G₀ M₀] (f : F) (a : G₀) :
    f a⁻¹ = (f a)⁻¹ʳ := by
  obtain (rfl | ha) := eq_or_ne a 0
  · simp
  · simpa using IsUnit.mk0 a ha |>.map_ringInverse f

/-- A homomorphism which reflects units commutes with `Ring.inverse`. This does not require any
`IsUnit` assumption. The `IsLocalHom f` hypothesis is satisfied when `f` is an isomorphism. -/
protected theorem IsLocalHom.map_ringInverse [MonoidWithZeroHomClass F M₀ M₀'] (f : F)
    [IsLocalHom f] (a : M₀) : f a⁻¹ʳ = (f a)⁻¹ʳ := by
  by_cases h : IsUnit a
  · exact h.map_ringInverse f
  · rw [Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ (h <| IsUnit.of_map f a ·), map_zero]

theorem isLocalHom_iff_map_ringInverse [MonoidWithZeroHomClass F M₀ M₀'] [Nontrivial M₀'] (f : F) :
    IsLocalHom f ↔ ∀ a, f a⁻¹ʳ = (f a)⁻¹ʳ := by
  refine ⟨fun h ↦ h.map_ringInverse f, fun h ↦ ⟨fun a ha ↦ by_contra fun ha' ↦ ?_⟩⟩
  rw [Ring.isUnit_iff_inverse_ne_zero] at ha
  exact ha <| by rw [← h a, Ring.inverse_non_unit _ ha', map_zero]

/-- We define the inverse as a `MonoidWithZeroHom` by extending the inverse map by zero
on non-units. -/
noncomputable def MonoidWithZero.inverse {M : Type*} [CommMonoidWithZero M] :
    M →*₀ M where
  toFun := Ring.inverse
  map_zero' := Ring.inverse_zero _
  map_one' := Ring.inverse_one _
  map_mul' x y := (Ring.mul_inverse_rev x y).trans (mul_comm _ _)

@[simp]
theorem MonoidWithZero.coe_inverse {M : Type*} [CommMonoidWithZero M] :
    (MonoidWithZero.inverse : M → M) = Ring.inverse :=
  rfl

@[simp]
theorem MonoidWithZero.inverse_apply {M : Type*} [CommMonoidWithZero M] (a : M) :
    MonoidWithZero.inverse a = a⁻¹ʳ :=
  rfl
