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
- `changeLevel`: Extend the Dirichlet character χ of level `n` to level `m`, where `n` divides `m`.

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
noncomputable def changeLevel {R : Type} [CommMonoidWithZero R] {n m : ℕ} (hm : n ∣ m) :
    DirichletCharacter R n →* DirichletCharacter R m :=
  { toFun := fun ψ ↦ MulChar.ofUnitHom (ψ.toUnitHom.comp (ZMod.unitsMap hm)),
    map_one' := by ext; simp,
    map_mul' := fun ψ₁ ψ₂ ↦ by ext; simp }

lemma changeLevel_def {m : ℕ} (hm : n ∣ m) :
    changeLevel hm χ = MulChar.ofUnitHom (χ.toUnitHom.comp (ZMod.unitsMap hm)) := rfl

lemma changeLevel_def' {m : ℕ} (hm : n ∣ m) :
    (changeLevel hm χ).toUnitHom = χ.toUnitHom.comp (ZMod.unitsMap hm) := by
  ext
  rw [changeLevel_def, ZMod.unitsMap_def]
  simp

@[simp]
lemma changeLevel_self : changeLevel (dvd_refl n) χ = χ := by
  ext
  rw [changeLevel_def]
  simp [ZMod.unitsMap]

lemma changeLevel_self_toUnitHom : (changeLevel (dvd_refl n) χ).toUnitHom = χ.toUnitHom := by
  rw [changeLevel_self]

lemma changeLevel_trans {m d : ℕ} (hm : n ∣ m) (hd : m ∣ d) :
  changeLevel (dvd_trans hm hd) χ = changeLevel hd (changeLevel hm χ) := by
  simp only [changeLevel_def, toUnitHom_eq, ZMod.unitsMap, ofUnitHom_eq, Equiv.apply_symm_apply]
  rw [MonoidHom.comp_assoc, ←Units.map_comp]
  congr
  rw [← ZMod.castHom_comp hm hd]
  rfl

end DirichletCharacter
