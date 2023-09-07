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
- `change_level`: Extend the Dirichlet character χ of level `n` to level `m`, where `n` divides `m`.

## Tags

dirichlet character, multiplicative character
-/
-- TODO: move to Data.ZMod.Basic?!
@[simp]
lemma cast_hom_self {n : ℕ} : ZMod.castHom dvd_rfl (ZMod n) = RingHom.id (ZMod n) :=
  RingHom.ext_zmod (ZMod.castHom dvd_rfl (ZMod n)) (RingHom.id (ZMod n))

/-- The Dirichlet character of level `n`. -/
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
  conv_lhs => rw [← (IsUnit.unit_spec ha)]
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

lemma isPeriodic (m : ℕ) (hm : n ∣ m) (a : ℤ) :
  ofUnitHom χ (a + m) = ofUnitHom χ a := by
  rw [← ZMod.nat_cast_zmod_eq_zero_iff_dvd] at hm
  simp only [hm, add_zero]

/-- Extends the Dirichlet character χ of level n to level m, where n ∣ m. -/
def change_level {m : ℕ} (hm : n ∣ m) : DirichletCharacter R n →* DirichletCharacter R m :=
{ toFun := λ ψ => ψ.comp (Units.map (ZMod.castHom hm (ZMod n))),
  map_one' := by simp,
  map_mul' := λ ψ₁ ψ₂ => MonoidHom.mul_comp _ _ _, }

lemma change_level_def {m : ℕ} (hm : n ∣ m) :
    change_level hm χ = χ.comp (Units.map (ZMod.castHom hm (ZMod n))) := rfl

namespace change_level
lemma self : change_level (dvd_refl n) χ = χ := by
  simp [change_level_def]

lemma trans {m d : ℕ} (hm : n ∣ m) (hd : m ∣ d) :
  change_level (dvd_trans hm hd) χ = change_level hd (change_level hm χ) := by
  repeat rw [change_level_def]
  rw [MonoidHom.comp_assoc, ←Units.map_comp]
  change _ = χ.comp (Units.map ↑((ZMod.castHom hm (ZMod n)).comp (ZMod.castHom hd (ZMod m))))
  congr
  simp

lemma ofUnitHom_eq {m : ℕ} (hm : n ∣ m) (a : Units (ZMod m)) :
  ofUnitHom (change_level hm χ) a = ofUnitHom χ a := by
  have ha : IsUnit ((a : ZMod m) : ZMod n)
  · rw [←@ZMod.castHom_apply _ _ _ n _ hm (a : ZMod m)]
    change IsUnit ((ZMod.castHom hm (ZMod n) : ZMod m →* ZMod n) ↑a)
    rw [←Units.coe_map (ZMod.castHom hm (ZMod n) : ZMod m →* ZMod n) a]
    apply Units.isUnit
  rw [ofUnitHom_eq_char' _ ha]
  simp only [change_level_def, ofUnitHom_eq, Units.isUnit, not_true, equivToUnitHom_symm_coe, MonoidHom.coe_comp,
    Function.comp_apply]
  congr
  simp
  congr
  rw [← Units.eq_iff]
  simp

lemma ofUnitHom_eq' {m : ℕ} (hm : n ∣ m) {a : ZMod m} (ha : IsUnit a) :
ofUnitHom (change_level hm χ) a = ofUnitHom χ a := by
  rw [←IsUnit.unit_spec ha]
  rw [ofUnitHom_eq]

end change_level

end DirichletCharacter
