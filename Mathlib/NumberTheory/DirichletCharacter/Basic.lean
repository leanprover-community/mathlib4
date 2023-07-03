/-
Copyright (c) 2023 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan, Moritz Firsching
-/
import Mathlib.Data.ZMod.Quotient

/-!
# Dirichlet characters
This file defines Dirichlet characters over (ℤ/nℤ)ˣ.

## Main definitions
 * `DirichletCharacter`
 * `ExtendedDirichletCharacter`

## Tags
p-adic, Dirichlet character
-/

/-- A Dirichlet character is defined as a monoid homomorphism which is periodic for n ≠ 0. -/
@[reducible]
def DirichletCharacter  (R : Type _) [Monoid R] (n : ℕ) := ((ZMod n)ˣ →*  Rˣ)

attribute [local instance] Classical.propDecidable

theorem extended_apply_unit [MonoidWithZero R] {n : ℕ}
  (χ : DirichletCharacter R n) {x : ZMod n} (hx : IsUnit x) :
  Function.extend (Units.coeHom (ZMod n)) ((Units.coeHom R) ∘ χ) 0 x = χ hx.unit := by
  conv_lhs =>
    congr
    · skip
    · skip
    · skip
    · rw [←IsUnit.unit_spec hx]
  rw [← Units.coeHom_apply]
  rw [Function.Injective.extend_apply _]
  · simp only [Units.coeHom_apply, Function.comp_apply]
  · exact Units.ext

theorem extended_apply_non_unit {R : Type _} [MonoidWithZero R] {n : ℕ}
  (χ : DirichletCharacter R n) {x : ZMod n} (hx : ¬ IsUnit x) :
  Function.extend (Units.coeHom (ZMod n)) ((Units.coeHom R) ∘ χ) 0 x = 0 := by
  rw [Function.extend_def, dif_neg]
  · simp only [Pi.zero_apply]
  · contrapose hx
    rw [not_not] at *
    cases' hx with a ha
    rw [←ha]
    apply Units.isUnit

/-- The Dirichlet character on ℤ/nℤ →* R determined by χ, 0 on non-units. -/
noncomputable abbrev ExtendedDirichletCharacter {R : Type _} [MonoidWithZero R] {n : ℕ}
  (χ : DirichletCharacter R n) : ZMod n →* R where
    toFun := Function.extend (Units.coeHom (ZMod n)) ((Units.coeHom R) ∘ χ) 0
    map_one' := by
      rw [extended_apply_unit _ isUnit_one, Units.val_eq_one]
      convert χ.map_one'
      rw [← Units.eq_iff, IsUnit.unit_spec, Units.val_one]
    map_mul' x y := by
      by_cases h : IsUnit x ∧ IsUnit y
      · dsimp only
        rw [extended_apply_unit _ (IsUnit.mul h.1 h.2), extended_apply_unit _ h.1,
            extended_apply_unit _ h.2]
        change (Units.coeHom R) (χ _) = (Units.coeHom R) (χ _) * (Units.coeHom R) (χ _)
        repeat rw [← MonoidHom.comp_apply _ χ]
        convert ← MonoidHom.map_mul' (MonoidHom.comp (Units.coeHom R) χ) _ _
        rw [IsUnit.unit_mul h.1 h.2]
      · have : ¬ (IsUnit (x * y)) := by
          contrapose! h
          exact IsUnit.mul_iff.mp h
        dsimp only
        rw [extended_apply_non_unit χ this]
        push_neg at h
        by_cases h' : IsUnit x
        · rw [extended_apply_non_unit _ (h h'), mul_zero]
        · rw [extended_apply_non_unit _ h', zero_mul]
