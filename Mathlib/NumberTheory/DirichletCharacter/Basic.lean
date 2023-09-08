/-
Copyright (c) 2023 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan, Moritz Firsching
-/
import Mathlib.NumberTheory.LegendreSymbol.MulCharacter
import Mathlib.Data.ZMod.Algebra

/-!
# Dirichlet Characters

Let `R` be a monoid. A Dirichlet character `χ` of level `n` over `R` is a homomorphism from the unit
group `(ZMod n)ˣ` to `Rˣ`. We then obtain some properties of `ofUnitHom χ`.

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
def DirichletCharacter (R : Type) [Monoid R] (n : ℕ) := (ZMod n)ˣ →* Rˣ

-- TODO: move to NumberTheory.LegendreSymbol.MulCharacter?!
namespace MulChar
lemma coe_toMonoidHom {R R' : Type} [CommMonoid R] [CommMonoidWithZero R'] (χ : MulChar R R')
(x : R) : χ.toMonoidHom x = χ x := by solve_by_elim
end MulChar

open MulChar
variable {R : Type} [CommMonoidWithZero R] {n : ℕ} (χ : DirichletCharacter R n)

namespace DirichletCharacter
lemma ofUnitHom_eq_char' {a : ZMod n} (ha : IsUnit a) :
  ofUnitHom χ a = χ ha.unit := by
  conv_lhs => rw [← ha.unit_spec]
  simp only [ofUnitHom_eq, MulChar.equivToUnitHom_symm_coe]

lemma ofUnitHom_eq_zero {a : ZMod n} (ha : ¬ IsUnit a) :
  ofUnitHom χ a = 0 := by
  have := map_nonunit' (ofUnitHom χ) _ ha
  simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe] at this
  rw [← coe_toMonoidHom, this]

lemma ofUnitHom_eq_iff (ψ : DirichletCharacter R n) :
  χ = ψ ↔ ofUnitHom χ = ofUnitHom ψ := by simp only [ofUnitHom_eq, EmbeddingLike.apply_eq_iff_eq]

lemma ofUnitHom_eval_sub (x : ZMod n) :
  ofUnitHom χ (n - x) = ofUnitHom χ (-x) := by simp

lemma isPeriodic {m : ℕ} (hm : n ∣ m) (a : ℤ) :
  ofUnitHom χ (a + m) = ofUnitHom χ a := by
  rw [← ZMod.nat_cast_zmod_eq_zero_iff_dvd] at hm
  simp only [hm, add_zero]

end DirichletCharacter
