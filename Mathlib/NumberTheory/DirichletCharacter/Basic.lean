/-
Copyright (c) 2023 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan, Moritz Firsching
-/
import Mathlib.NumberTheory.LegendreSymbol.MulCharacter
import Mathlib.Data.ZMod.Algebra

/-!
# Dirichlet Characters

Let `R` be a commutatvive monoid with zero. A Dirichlet character `χ` of level `n` over `R` is a
multiplicative character from `ZMod n` to `Rˣ`. We then obtain some properties of `toUnitHom χ`.

Main definitions:

- `DirichletCharacter`: The type representing a Dirichlet character.

## TODO

- `change_level`: Extend the Dirichlet character χ of level `n` to level `m`, where `n` divides `m`.
- definition of conductor

## Tags

dirichlet character, multiplicative character
-/

/-- The type of Dirichlet characters of level `n`. -/
@[reducible]
def DirichletCharacter (R : Type) [CommMonoidWithZero R] (n : ℕ) := MulChar (ZMod n) R

open MulChar
variable {R : Type} [CommMonoidWithZero R] {n : ℕ} (χ : DirichletCharacter R n)

namespace DirichletCharacter
lemma toUnitHom_eq_char' {a : ZMod n} (ha : IsUnit a) :
  χ a = χ.toUnitHom ha.unit := by simp

lemma toUnitHom_eq_iff (ψ : DirichletCharacter R n) :
  χ = ψ ↔ toUnitHom χ = toUnitHom ψ := by simp

lemma eval_sub (x : ZMod n) :
  χ (n - x) = χ (-x) := by simp

lemma isPeriodic {m : ℕ} (hm : n ∣ m) (a : ℤ) :
  χ (a + m) = χ a := by
  rw [← ZMod.nat_cast_zmod_eq_zero_iff_dvd] at hm
  simp only [hm, add_zero]

end DirichletCharacter
