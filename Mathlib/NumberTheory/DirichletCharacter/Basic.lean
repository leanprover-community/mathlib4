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
- `conductor`: The conductor of a Dirichlet character.
- `isPrimitive`: If the level is equal to the conductor.

## TODO

- reduction, even, odd

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

lemma changeLevel_eq_cast_of_dvd {m : ℕ} (hm : n ∣ m) (a : Units (ZMod m)) :
    (changeLevel hm χ) a = χ a := by
  simpa [changeLevel_def, Function.comp_apply, MonoidHom.coe_comp] using
      toUnitHom_eq_char' _ <| ZMod.IsUnit_cast_of_dvd hm a

/-- `χ` of level `n` factors through a Dirichlet character `χ₀` of level `d` if `d ∣ n` and
`χ₀ = χ ∘ (ZMod n → ZMod d)`. -/
def FactorsThrough (d : ℕ) : Prop :=
  ∃ (h : d ∣ n) (χ₀ : DirichletCharacter R d), χ = changeLevel h χ₀

namespace FactorsThrough

/-- The fact that `d` divides `n` when `χ` factors through a Dirichlet character at level `d` -/
lemma dvd {d : ℕ} (h : FactorsThrough χ d) : d ∣ n := h.1

/-- The Dirichlet character at level `d` through which `χ` factors -/
noncomputable
def χ₀ {d : ℕ} (h : FactorsThrough χ d) : DirichletCharacter R d := Classical.choose h.2

/-- The fact that `χ` factors through `χ₀` of level `d` -/
lemma eq_changeLevel {d : ℕ} (h : FactorsThrough χ d) : χ = changeLevel h.dvd h.χ₀ :=
  Classical.choose_spec h.2

lemma same_level : FactorsThrough χ n := ⟨dvd_refl n, χ, (changeLevel_self χ).symm⟩

end FactorsThrough

/-- The set of natural numbers for which a Dirichlet character is periodic. -/
def conductorSet : Set ℕ := {x : ℕ | FactorsThrough χ x}

lemma mem_conductorSet_iff {x : ℕ} : x ∈ conductorSet χ ↔ FactorsThrough χ x := Iff.refl _

lemma level_mem_conductorSet : n ∈ conductorSet χ := FactorsThrough.same_level χ

lemma mem_conductorSet_dvd {x : ℕ} (hx : x ∈ conductorSet χ) : x ∣ n := hx.dvd

/-- The minimum natural number `n` for which a Dirichlet character is periodic.
The Dirichlet character `χ` can then alternatively be reformulated on `ℤ/nℤ`. -/
noncomputable def conductor : ℕ := sInf (conductorSet χ)

lemma conductor_mem_conductorSet : conductor χ ∈ conductorSet χ :=
  Nat.sInf_mem (Set.nonempty_of_mem (level_mem_conductorSet χ))

lemma conductor_dvd_level : conductor χ ∣ n := (conductor_mem_conductorSet χ).dvd

lemma FactorsThrough_conductor : FactorsThrough χ (conductor χ) := conductor_mem_conductorSet χ

lemma conductor_one (hn : 0 < n) : conductor (1 : DirichletCharacter R n) = 1 := by
  suffices : conductor (1 : DirichletCharacter R n) ≤ 1
  · cases' Nat.le_one_iff_eq_zero_or_eq_one.mp this with h1 h2
    · have := FactorsThrough.dvd (1 : DirichletCharacter R n) <| FactorsThrough_conductor 1
      aesop
    · exact h2
  · apply Nat.sInf_le ((mem_conductorSet_iff _).mpr ⟨one_dvd _, 1, _⟩)
    ext
    rw [changeLevel_def]
    simp

variable {χ}

lemma eq_one_iff_conductor_eq_one (hn : 0 < n) : χ = 1 ↔ conductor χ = 1 := by
  refine' ⟨λ h => by rw [h, conductor_one hn], λ hχ => _⟩
  obtain ⟨h', χ₀, h⟩ := FactorsThrough_conductor χ
  rw [h]
  ext
  rw [changeLevel_def, ZMod.unitsMap_def]
  simp only [toUnitHom_eq, ofUnitHom_eq, Units.isUnit, not_true, equivToUnitHom_symm_coe,
    MonoidHom.coe_comp, Function.comp_apply, coe_equivToUnitHom, Units.coe_map, MonoidHom.coe_coe,
    ZMod.castHom_apply, one_apply_coe]
  convert MonoidHom.map_one (χ₀ : ZMod (conductor χ) →* R)
  have : Subsingleton (ZMod (conductor χ)) := by
    rw [hχ]
    infer_instance
  simp

lemma conductor_eq_zero_iff_level_eq_zero : conductor χ = 0 ↔ n = 0 :=
  ⟨λ h => by
    rw [←zero_dvd_iff]
    convert conductor_dvd_level χ
    rw [h],
  λ h => by
    rw [conductor, Nat.sInf_eq_zero]
    left
    exact ⟨zero_dvd_iff.mpr h, ⟨changeLevel (by rw [h]) χ, by
        rw [← changeLevel_trans _ _ _, changeLevel_self _]⟩⟩⟩

variable (χ)

/-- A character is primitive if its level is equal to its conductor. -/
def isPrimitive : Prop := conductor χ = n

lemma isPrimitive_def : isPrimitive χ ↔ conductor χ = n := ⟨λ h => h, λ h => h⟩

lemma isPrimitive_one_level_one : isPrimitive (1 : DirichletCharacter R 1) :=
  Nat.dvd_one.mp (conductor_dvd_level _)

lemma isPritive_one_level_zero : isPrimitive (1 :  DirichletCharacter R 0) := by
  rw [isPrimitive_def, conductor, Nat.sInf_eq_zero]
  left
  rw [conductorSet]
  simp only [Set.mem_setOf_eq]
  fconstructor
  simp only [true_and, ZMod.cast_id', id.def, MonoidHom.coe_mk, dvd_zero]
  refine ⟨1, by simp⟩

lemma conductor_one_dvd (n : ℕ) : conductor (1 : DirichletCharacter R 1) ∣ n := by
  rw [(isPrimitive_def _).mp isPrimitive_one_level_one]
  apply one_dvd _

end DirichletCharacter
