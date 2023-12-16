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

- add
  `lemma unitsMap_surjective {n m : ℕ} (h : n ∣ m) (hm : m ≠ 0) : Function.Surjective (unitsMap h)`
  and then
  ```
  lemma changeLevel_injective {d : ℕ} (h : d ∣ n) (hn : n ≠ 0) :
      Function.Injective (changeLevel (R := R) h)
  ```
  and
  ```
  lemma changeLevel_one_iff {d : ℕ} {χ : DirichletCharacter R n} {χ' : DirichletCharacter R d}
    (hdn : d ∣ n) (hn : n ≠ 0) (h : χ = changeLevel hdn χ') : χ = 1 ↔ χ' = 1
  ```

## Tags

dirichlet character, multiplicative character
-/

/-- The type of Dirichlet characters of level `n`. -/
abbrev DirichletCharacter (R : Type*) [CommMonoidWithZero R] (n : ℕ) := MulChar (ZMod n) R

open MulChar
variable {R : Type*} [CommMonoidWithZero R] {n : ℕ} (χ : DirichletCharacter R n)

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
noncomputable def changeLevel {R : Type*} [CommMonoidWithZero R] {n m : ℕ} (hm : n ∣ m) :
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

lemma level_one (χ : DirichletCharacter R 1) : χ = 1 := by
  ext
  simp [units_eq_one]

lemma level_one' (hn : n = 1) : χ = 1 := by
  subst hn
  exact level_one _

instance : Subsingleton (DirichletCharacter R 1) := by
  refine subsingleton_iff.mpr (fun χ χ' ↦ ?_)
  simp [level_one]

noncomputable instance : Inhabited (DirichletCharacter R n) := ⟨1⟩

noncomputable instance : Unique (DirichletCharacter R 1) := Unique.mk' (DirichletCharacter R 1)

lemma changeLevel_one {d : ℕ} (h : d ∣ n) :
    changeLevel h (1 : DirichletCharacter R d) = 1 := by
  simp [changeLevel]

lemma factorsThrough_one_iff : FactorsThrough χ 1 ↔ χ = 1 := by
  refine ⟨fun ⟨_, χ₀, hχ₀⟩ ↦ ?_,
          fun h ↦ ⟨one_dvd n, 1, by rw [h, changeLevel_one]⟩⟩
  rwa [level_one χ₀, changeLevel_one] at hχ₀

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

lemma factorsThrough_conductor : FactorsThrough χ (conductor χ) := conductor_mem_conductorSet χ

lemma conductor_ne_zero (hn : n ≠ 0) : conductor χ ≠ 0 :=
  fun h ↦ hn <| Nat.eq_zero_of_zero_dvd <| h ▸ conductor_dvd_level _

lemma conductor_one (hn : n ≠ 0) : conductor (1 : DirichletCharacter R n) = 1 := by
  suffices : FactorsThrough (1 : DirichletCharacter R n) 1
  · have h : conductor (1 : DirichletCharacter R n) ≤ 1 :=
      Nat.sInf_le <| (mem_conductorSet_iff _).mpr this
    exact Nat.le_antisymm h (Nat.pos_of_ne_zero <| conductor_ne_zero _ hn)
  · exact (factorsThrough_one_iff _).mpr rfl

variable {χ}

lemma eq_one_iff_conductor_eq_one (hn : n ≠ 0) : χ = 1 ↔ conductor χ = 1 := by
  refine ⟨fun h ↦ h ▸ conductor_one hn, fun hχ ↦ ?_⟩
  obtain ⟨h', χ₀, h⟩ := factorsThrough_conductor χ
  exact (level_one' χ₀ hχ ▸ h).trans <| changeLevel_one h'

lemma conductor_eq_zero_iff_level_eq_zero : conductor χ = 0 ↔ n = 0 := by
  refine ⟨(conductor_ne_zero χ).mtr, ?_⟩
  rintro rfl
  exact Nat.sInf_eq_zero.mpr <| Or.inl <| level_mem_conductorSet χ

lemma conductor_le_conductor_mem_conductorSet {d : ℕ} (hd : d ∈ conductorSet χ) :
    χ.conductor ≤ (Classical.choose hd.2).conductor := by
  refine Nat.sInf_le <| (mem_conductorSet_iff χ).mpr <|
    ⟨dvd_trans (conductor_dvd_level _) hd.1,
     (factorsThrough_conductor (Classical.choose hd.2)).2.choose, ?_⟩
  rw [changeLevel_trans _ (conductor_dvd_level _) (FactorsThrough.dvd _ hd),
      ← (factorsThrough_conductor (Classical.choose hd.2)).2.choose_spec]
  exact FactorsThrough.eq_changeLevel χ hd

variable (χ)

/-- A character is primitive if its level is equal to its conductor. -/
def isPrimitive : Prop := conductor χ = n

lemma isPrimitive_def : isPrimitive χ ↔ conductor χ = n := Iff.rfl

lemma isPrimitive_one_level_one : isPrimitive (1 : DirichletCharacter R 1) :=
  Nat.dvd_one.mp (conductor_dvd_level _)

lemma isPritive_one_level_zero : isPrimitive (1 : DirichletCharacter R 0) :=
  conductor_eq_zero_iff_level_eq_zero.mpr rfl

lemma conductor_one_dvd (n : ℕ) : conductor (1 : DirichletCharacter R 1) ∣ n := by
  rw [(isPrimitive_def _).mp isPrimitive_one_level_one]
  apply one_dvd _

/-- The primitive character associated to a Dirichlet character. -/
noncomputable def primitiveCharacter : DirichletCharacter R χ.conductor :=
  Classical.choose (factorsThrough_conductor χ).choose_spec

lemma primitiveCharacter_isPrimitive : isPrimitive (χ.primitiveCharacter) := by
  by_cases h : χ.conductor = 0
  · rw [isPrimitive_def]
    convert conductor_eq_zero_iff_level_eq_zero.mpr h
  · exact le_antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero h) (conductor_dvd_level _)) <|
      conductor_le_conductor_mem_conductorSet <| conductor_mem_conductorSet χ

lemma primitiveCharacter_one (hn : n ≠ 0) :
    (1 : DirichletCharacter R n).primitiveCharacter = 1 := by
  rw [eq_one_iff_conductor_eq_one <| (@conductor_one R _ _ hn) ▸ Nat.one_ne_zero,
      (isPrimitive_def _).1 (1 : DirichletCharacter R n).primitiveCharacter_isPrimitive,
      conductor_one hn]

/-- Dirichlet character associated to multiplication of Dirichlet characters,
after changing both levels to the same -/
noncomputable def mul {m : ℕ} (χ₁ : DirichletCharacter R n) (χ₂ : DirichletCharacter R m) :
    DirichletCharacter R
      (Nat.lcm n m) :=
  changeLevel (Nat.dvd_lcm_left n m) χ₁ * changeLevel (Nat.dvd_lcm_right n m) χ₂

/-- Primitive character associated to multiplication of Dirichlet characters,
after changing both levels to the same -/
noncomputable def primitive_mul {m : ℕ} (χ₁ : DirichletCharacter R n)
    (χ₂ : DirichletCharacter R m) : DirichletCharacter R (mul χ₁ χ₂).conductor :=
  primitiveCharacter (mul χ₁ χ₂)

lemma mul_def {n m : ℕ} {χ : DirichletCharacter R n} {ψ : DirichletCharacter R m} :
    χ.primitive_mul ψ = primitiveCharacter _ :=
  rfl

namespace isPrimitive
lemma primitive_mul {m : ℕ} (ψ : DirichletCharacter R m) : (primitive_mul χ ψ).isPrimitive :=
  primitiveCharacter_isPrimitive _
end isPrimitive

variable {S : Type} [CommRing S] {m : ℕ} (ψ : DirichletCharacter S m)

/-- A Dirichlet character is odd if its value at -1 is -1. -/
def Odd : Prop := ψ (-1) = -1

/-- A Dirichlet character is even if its value at -1 is 1. -/
def Even : Prop := ψ (-1) = 1

lemma even_or_odd [NoZeroDivisors S] : ψ.Even ∨ ψ.Odd := by
  suffices : ψ (-1) ^ 2 = 1
  · convert sq_eq_one_iff.mp this
  · rw [← map_pow _, neg_one_sq, map_one]

lemma Odd.toUnitHom_eval_neg_one (hψ : ψ.Odd) : ψ.toUnitHom (-1) = -1 := by
  rw [← Units.eq_iff, MulChar.coe_toUnitHom]
  exact hψ

lemma Even.toUnitHom_eval_neg_one (hψ : ψ.Even) : ψ.toUnitHom (-1) = 1 := by
  rw [← Units.eq_iff, MulChar.coe_toUnitHom]
  exact hψ

lemma Odd.eval_neg (x : ZMod m) (hψ : ψ.Odd) : ψ (- x) = - ψ x := by
  rw [Odd] at hψ
  rw [← neg_one_mul, map_mul]
  simp [hψ]

lemma Even.eval_neg (x : ZMod m) (hψ : ψ.Even) : ψ (- x) = ψ x := by
  rw [Even] at hψ
  rw [← neg_one_mul, map_mul]
  simp [hψ]

end DirichletCharacter
