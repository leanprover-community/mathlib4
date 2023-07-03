/-
Copyright (c) 2023 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan, Moritz Firsching
-/
import Mathlib.Data.ZMod.Quotient
import Mathlib.Algebra.Hom.Group
import Mathlib.Tactic
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.PermuteGoals
import Mathlib.Logic.Function.Basic
--import Mathlib.RingTheory.RootsOfUnity
--import Mathlib.ZMod.Properties
/-!
# Dirichlet characters
This file defines Dirichlet characters over (ℤ/nℤ)* and then relates them
to multiplicative homomorphisms over ℤ/nℤ for any n divisible by the conductor.

## Main definitions
 * `dirichletCharacter`
 * `asso_dirichletCharacter`
 * `change_level`
 * `conductor`

## Tags
p-adic, L-function, Bernoulli measure, Dirichlet character
-/

/-- A Dirichlet character is defined as a monoid homomorphism which is periodic for n ≠ 0. -/
@[reducible]
def dirichletCharacter  (R : Type _) [Monoid R] (n : ℕ) := ((ZMod n)ˣ →*  Rˣ)

attribute [local instance] Classical.propDecidable

theorem extend_eq_char [MonoidWithZero R] {n : ℕ}
  (χ : dirichletCharacter R n) {x : ZMod n} (hx : IsUnit x) :
  Function.extend (Units.coeHom (ZMod n)) ((Units.coeHom R) ∘ χ) 0 x = χ hx.unit := by
  conv_lhs =>
    congr
    · skip
    · skip
    · skip
    · rw [←IsUnit.unit_spec hx]
  rw [←Units.coeHom_apply]
  rw [Function.Injective.extend_apply _]
  · simp only [Units.coeHom_apply, Function.comp_apply]
  · exact Units.ext

theorem extend_eq_zero {R : Type _} [MonoidWithZero R] {n : ℕ}
  (χ : dirichletCharacter R n) {x : ZMod n} (hx : ¬ IsUnit x) :
  Function.extend (Units.coeHom (ZMod n)) ((Units.coeHom R) ∘ χ) 0 x = 0 := by
  rw [Function.extend_def, dif_neg]
  · simp only [Pi.zero_apply]
  · contrapose hx
    rw [not_not] at *
    cases' hx with a ha
    rw [←ha]
    apply Units.isUnit

/-- The Dirichlet character on ℤ/nℤ →* R determined by χ, 0 on non-units. -/
noncomputable abbrev asso_dirichletCharacter {R : Type _} [MonoidWithZero R] {n : ℕ}
  (χ : dirichletCharacter R n) : ZMod n →* R where
    toFun := Function.extend (Units.coeHom (ZMod n)) ((Units.coeHom R) ∘ χ) 0
    map_one' := by
      rw [extend_eq_char _ isUnit_one, Units.val_eq_one]
      convert χ.map_one'
      rw [← Units.eq_iff, IsUnit.unit_spec, Units.val_one]
    map_mul' x y := by
      by_cases h : IsUnit x ∧ IsUnit y
      · dsimp only
        rw [extend_eq_char _ (IsUnit.mul h.1 h.2)]
        rw [extend_eq_char _ h.1, extend_eq_char _ h.2]
        change (Units.coeHom R) (χ _) = (Units.coeHom R) (χ _) * (Units.coeHom R) (χ _)
        rw [← MonoidHom.comp_apply _ χ]
        rw [← MonoidHom.comp_apply _ χ]
        rw [← MonoidHom.comp_apply _ χ]
        convert ←MonoidHom.map_mul' (MonoidHom.comp (Units.coeHom R) χ) _
        rw [IsUnit.unit_mul]
      · have : ¬ (IsUnit (x * y)) :=
          contrapose! h
          rw [not_not] at *
          rw [← is_unit.mul_iff]
          assumption
        rw [extend_eq_zero _ this]
        push_neg at h
        by_cases h' : IsUnit x
        · rw [extend_eq_zero _ (h h'), mul_zero]
        · rw [extend_eq_zero _ h', zero_mul]
