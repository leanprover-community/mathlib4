/-
Copyright (c) 2023 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan, Moritz Firsching, Michael Stoll
-/
import Mathlib.Algebra.Periodic
import Mathlib.Data.ZMod.Algebra
import Mathlib.NumberTheory.LegendreSymbol.MulCharacter
import Mathlib.Data.ZMod.Algebra
import Mathlib.Data.ZMod.Units

/-!
# Dirichlet Characters

Let `R` be a commutative monoid with zero. A Dirichlet character `χ` of level `n` over `R` is a
multiplicative character from `ZMod n` to `R` sending non-units to 0. We then obtain some properties
of `toUnitHom χ`, the restriction of `χ` to a group homomorphism `(ZMod n)ˣ →* Rˣ`.

Main definitions:

- `DirichletCharacter`: The type representing a Dirichlet character.
- `change_level`: Extend the Dirichlet character χ of level `n` to level `m`, where `n` divides `m`.

## TODO

- definition of conductor

## Tags

dirichlet character, multiplicative character
-/

/-- The type of Dirichlet characters of level `n`. -/
abbrev DirichletCharacter (R : Type) [CommMonoidWithZero R] (n : ℕ) := MulChar (ZMod n) R

open MulChar
variable {R : Type} [CommMonoidWithZero R] {n : ℕ} (χ : DirichletCharacter R n)

namespace DirichletCharacter
lemma toUnitHom_eq_char' {a : ZMod n} (ha : IsUnit a) :
  χ a = χ.toUnitHom ha.unit := by simp

lemma toUnitHom_eq_iff (ψ : DirichletCharacter R n) :
  toUnitHom χ = toUnitHom ψ ↔ χ = ψ := by simp

lemma eval_modulus_sub (x : ZMod n) :
  χ (n - x) = χ (-x) := by simp

lemma periodic {m : ℕ} (hm : n ∣ m) : Function.Periodic χ m := by
  intro a
  rw [← ZMod.nat_cast_zmod_eq_zero_iff_dvd] at hm
  simp only [hm, add_zero]

/-- A function that modifies the level of a Dirichlet character to some multiple
  of its original level. -/
noncomputable def change_level {R : Type} [CommMonoidWithZero R] {n m : ℕ} (hm : n ∣ m) :
    DirichletCharacter R n →* DirichletCharacter R m :=
  { toFun := fun ψ ↦ MulChar.ofUnitHom (ψ.toUnitHom.comp (ZMod.unitsMap hm)),
    map_one' := by ext; simp,
    map_mul' := fun ψ₁ ψ₂ ↦ by ext; simp }

lemma change_level_def {m : ℕ} (hm : n ∣ m) :
    change_level hm χ = MulChar.ofUnitHom (χ.toUnitHom.comp (ZMod.unitsMap hm)) := rfl

lemma change_level_def' {m : ℕ} (hm : n ∣ m) :
    (change_level hm χ).toUnitHom = χ.toUnitHom.comp (Units.map (ZMod.castHom hm (ZMod n))) := by
  ext
  rw [change_level_def, ZMod.unitsMap_def]
  simp

end DirichletCharacter
