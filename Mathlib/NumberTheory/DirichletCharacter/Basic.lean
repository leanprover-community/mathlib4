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
lemma toUnitHom_eq_char' {a : ZMod n} (ha : IsUnit a) : χ a = χ.toUnitHom ha.unit := by simp

lemma toUnitHom_eq_iff (ψ : DirichletCharacter R n) : toUnitHom χ = toUnitHom ψ ↔ χ = ψ := by simp

lemma eval_modulus_sub (x : ZMod n) : χ (n - x) = χ (-x) := by simp

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
  simp [changeLevel]

@[simp]
lemma changeLevel_self : changeLevel (dvd_refl n) χ = χ := by
  simp [changeLevel, ZMod.unitsMap]

lemma changeLevel_self_toUnitHom : (changeLevel (dvd_refl n) χ).toUnitHom = χ.toUnitHom := by
  rw [changeLevel_self]

lemma changeLevel_trans {m d : ℕ} (hm : n ∣ m) (hd : m ∣ d) :
    changeLevel (dvd_trans hm hd) χ = changeLevel hd (changeLevel hm χ) := by
  simp [changeLevel_def, MonoidHom.comp_assoc, ZMod.unitsMap_comp]

lemma unitsMap_comp {d m : ℕ} (hm : n ∣ m) (hd : m ∣ d) :
    (ZMod.unitsMap hm).comp (ZMod.unitsMap hd) = ZMod.unitsMap (dvd_trans hm hd) := by
  simp only [ZMod.unitsMap_def]
  rw [← Units.map_comp]
  exact congr_arg Units.map <| congr_arg RingHom.toMonoidHom <| ZMod.castHom_comp hm hd

lemma ofUnitHom_eq {m : ℕ} (hm : n ∣ m) (a : Units (ZMod m)) :
    (changeLevel hm χ) a = χ a := by
  simpa [changeLevel_def, Function.comp_apply, MonoidHom.coe_comp] using
      toUnitHom_eq_char' _ <| ZMod.IsUnit_cast_of_dvd hm a

/-- χ₀ of level d factors through χ of level n if d ∣ n and χ₀ = χ ∘ (ZMod n → ZMod d). -/
structure FactorsThrough (d : ℕ) : Prop :=
  /-- `d` divides `n`, so `d` is a potential level through which `χ` factors. -/
  (dvd : d ∣ n)
  /-- A character `χ₀` of level `d` such that `χ` is just the change in level of `χ₀` to `n`. -/
  (indChar : ∃ χ₀ : DirichletCharacter R d, χ = changeLevel dvd χ₀)

namespace FactorsThrough
lemma spec {d : ℕ} (h : FactorsThrough χ d) :
    χ = changeLevel h.dvd (Classical.choose (h.indChar)) := Classical.choose_spec (h.indChar)
end FactorsThrough

/-- The set of natural numbers for which a Dirichlet character is periodic. -/
def conductorSet : Set ℕ := {x : ℕ | FactorsThrough χ x}

-- cant use dot notation for factors_through and conductor set
lemma mem_conductorSet_iff {x : ℕ} : x ∈ conductorSet χ ↔ FactorsThrough χ x := Iff.refl _

lemma level_mem_conductorSet : n ∈ conductorSet χ :=
  (mem_conductorSet_iff _).2
    { dvd := dvd_rfl,
      indChar := ⟨χ, (changeLevel_self χ).symm⟩, }

lemma mem_conductorSet_dvd {x : ℕ} (hx : x ∈ conductorSet χ) : x ∣ n := hx.1

lemma FactorsThrough_of_mem_conductorSet {x : ℕ} (hx : x ∈ conductorSet χ) : FactorsThrough χ x :=
  hx

/-- The minimum natural number n for which a Dirichlet character is periodic.
  The Dirichlet character χ can then alternatively be reformulated on ℤ/nℤ. -/
noncomputable def conductor : ℕ := sInf (conductorSet χ)

end DirichletCharacter
