/-
Copyright (c) 2023 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan, Moritz Firsching, Michael Stoll
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Data.ZMod.Units
public import Mathlib.NumberTheory.MulChar.Basic

/-!
# Dirichlet Characters

Let `R` be a commutative monoid with zero. A Dirichlet character `χ` of level `n` over `R` is a
multiplicative character from `ZMod n` to `R` sending non-units to 0. We then obtain some properties
of `toUnitHom χ`, the restriction of `χ` to a group homomorphism `(ZMod n)ˣ →* Rˣ`.

Main definitions:

- `DirichletCharacter`: The type representing a Dirichlet character.
- `changeLevel`: Extend the Dirichlet character χ of level `n` to level `m`, where `n` divides `m`.
- `conductor`: The conductor of a Dirichlet character.
- `IsPrimitive`: If the level is equal to the conductor.

## Tags

dirichlet character, multiplicative character
-/

@[expose] public section

/-!
### Definitions
-/

/-- The type of Dirichlet characters of level `n`. -/
abbrev DirichletCharacter (R : Type*) [CommMonoidWithZero R] (n : ℕ) := MulChar (ZMod n) R

open MulChar

variable {R : Type*} [CommMonoidWithZero R] {n : ℕ} (χ : DirichletCharacter R n)

namespace DirichletCharacter

lemma toUnitHom_eq_char' {a : ZMod n} (ha : IsUnit a) : χ a = χ.toUnitHom ha.unit := by simp

lemma toUnitHom_inj (ψ : DirichletCharacter R n) : toUnitHom χ = toUnitHom ψ ↔ χ = ψ := by simp

lemma eval_modulus_sub (x : ZMod n) : χ (n - x) = χ (-x) := by simp

/-!
### Changing levels
-/

/-- A function that modifies the level of a Dirichlet character to some multiple
  of its original level. -/
noncomputable def changeLevel {n m : ℕ} (hm : n ∣ m) :
    DirichletCharacter R n →* DirichletCharacter R m where
  toFun ψ := MulChar.ofUnitHom (ψ.toUnitHom.comp (ZMod.unitsMap hm))
  map_one' := by ext; simp
  map_mul' ψ₁ ψ₂ := by ext; simp

lemma changeLevel_def {m : ℕ} (hm : n ∣ m) :
    changeLevel hm χ = MulChar.ofUnitHom (χ.toUnitHom.comp (ZMod.unitsMap hm)) := rfl

lemma changeLevel_toUnitHom {m : ℕ} (hm : n ∣ m) :
    (changeLevel hm χ).toUnitHom = χ.toUnitHom.comp (ZMod.unitsMap hm) := by
  simp [changeLevel]

/-- The `changeLevel` map is injective (except in the degenerate case `m = 0`). -/
lemma changeLevel_injective {m : ℕ} [NeZero m] (hm : n ∣ m) :
    Function.Injective (changeLevel (R := R) hm) := by
  intro _ _ h
  ext1 y
  obtain ⟨z, rfl⟩ := ZMod.unitsMap_surjective hm y
  rw [MulChar.ext_iff] at h
  simpa [changeLevel_def] using h z

@[simp]
lemma changeLevel_eq_one_iff {m : ℕ} {χ : DirichletCharacter R n} (hm : n ∣ m) [NeZero m] :
    changeLevel hm χ = 1 ↔ χ = 1 :=
  map_eq_one_iff _ (changeLevel_injective hm)

@[simp]
lemma changeLevel_self : changeLevel (dvd_refl n) χ = χ := by
  simp [changeLevel, ZMod.unitsMap]

lemma changeLevel_self_toUnitHom : (changeLevel (dvd_refl n) χ).toUnitHom = χ.toUnitHom := by
  rw [changeLevel_self]

lemma changeLevel_trans {m d : ℕ} (hm : n ∣ m) (hd : m ∣ d) :
    changeLevel (dvd_trans hm hd) χ = changeLevel hd (changeLevel hm χ) := by
  simp [changeLevel_def, MonoidHom.comp_assoc, ZMod.unitsMap_comp]

lemma changeLevel_eq_cast_of_dvd {m : ℕ} (hm : n ∣ m) (a : Units (ZMod m)) :
    (changeLevel hm χ) a = χ (ZMod.cast (a : ZMod m)) := by
  simp [changeLevel_def, ZMod.unitsMap_val]

/-- `χ` of level `n` factors through a Dirichlet character `χ₀` of level `d` if `d ∣ n` and
`χ₀ = χ ∘ (ZMod n → ZMod d)`. -/
def FactorsThrough (d : ℕ) : Prop :=
  ∃ (h : d ∣ n) (χ₀ : DirichletCharacter R d), χ = changeLevel h χ₀

lemma changeLevel_factorsThrough {m : ℕ} (hm : n ∣ m) : FactorsThrough (changeLevel hm χ) n :=
  ⟨hm, χ, rfl⟩

namespace FactorsThrough

variable {χ}

/-- The fact that `d` divides `n` when `χ` factors through a Dirichlet character at level `d` -/
lemma dvd {d : ℕ} (h : FactorsThrough χ d) : d ∣ n := h.1

/-- The Dirichlet character at level `d` through which `χ` factors -/
noncomputable
def χ₀ {d : ℕ} (h : FactorsThrough χ d) : DirichletCharacter R d := Classical.choose h.2

/-- The fact that `χ` factors through `χ₀` of level `d` -/
lemma eq_changeLevel {d : ℕ} (h : FactorsThrough χ d) : χ = changeLevel h.dvd h.χ₀ :=
  Classical.choose_spec h.2

/-- The character of level `d` through which `χ` factors is uniquely determined. -/
lemma existsUnique {d : ℕ} [NeZero n] (h : FactorsThrough χ d) :
    ∃! χ' : DirichletCharacter R d, χ = changeLevel h.dvd χ' := by
  rcases h with ⟨hd, χ₂, rfl⟩
  exact ⟨χ₂, rfl, fun χ₃ hχ₃ ↦ (changeLevel_injective hd hχ₃).symm⟩

variable (χ) in
lemma same_level : FactorsThrough χ n := ⟨dvd_refl n, χ, (changeLevel_self χ).symm⟩

end FactorsThrough

variable {χ} in
/-- A Dirichlet character `χ` factors through `d | n` iff its associated unit-group hom is trivial
on the kernel of `ZMod.unitsMap`. -/
lemma factorsThrough_iff_ker_unitsMap {d : ℕ} [NeZero n] (hd : d ∣ n) :
    FactorsThrough χ d ↔ (ZMod.unitsMap hd).ker ≤ χ.toUnitHom.ker := by
  refine ⟨fun ⟨_, ⟨χ₀, hχ₀⟩⟩ x hx ↦ ?_, fun h ↦ ?_⟩
  · rw [MonoidHom.mem_ker, hχ₀, changeLevel_toUnitHom, MonoidHom.comp_apply, hx, map_one]
  · let E := MonoidHom.liftOfSurjective _ (ZMod.unitsMap_surjective hd) ⟨_, h⟩
    have hE : E.comp (ZMod.unitsMap hd) = χ.toUnitHom := MonoidHom.liftOfRightInverse_comp ..
    refine ⟨hd, MulChar.ofUnitHom E, equivToUnitHom.injective (?_ : toUnitHom _ = toUnitHom _)⟩
    simp_rw [changeLevel_toUnitHom, toUnitHom_eq, ofUnitHom_eq, Equiv.apply_symm_apply, hE,
      toUnitHom_eq]

theorem factorsThrough_of_dvd_dvd {d m : ℕ} [NeZero n] (hχ : FactorsThrough χ d) (hd : d ∣ m)
    (hm : m ∣ n) :
    FactorsThrough χ m := by
  refine (factorsThrough_iff_ker_unitsMap hm).mpr fun x hx ↦ ?_
  apply (factorsThrough_iff_ker_unitsMap hχ.dvd).mp hχ
  rw [MonoidHom.mem_ker] at hx ⊢
  rw [← ZMod.unitsMap_comp hd hm, MonoidHom.comp_apply, hx, map_one]

/--
Let `χ` and `ψ` be Dirichlet characters of level `n` and `m` respectively. Assume that they agree
at level `n * m`. Then `χ` factors through `gcd(n, m)`.
-/
theorem factorsThrough_gcd {m : ℕ} [NeZero n] (ψ : DirichletCharacter R m)
    (h : χ.changeLevel (n.dvd_mul_right m) = ψ.changeLevel (m.dvd_mul_left n)) :
    χ.FactorsThrough (n.gcd m) := by
  refine (factorsThrough_iff_ker_unitsMap (n.gcd_dvd_left m)).mpr fun x hx ↦
    MonoidHom.mem_ker.mpr ?_
  rw [Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
  obtain ⟨z, hz₁, hz₂⟩ : ∃ z : ℕ, z = x.val ∧ (z : ZMod m) = 1 := by
    suffices x.val.val ≡ 1 [MOD n.gcd m] by
      obtain ⟨z, hz₁, hz₂⟩ := Nat.chineseRemainder' this
      refine ⟨z, ?_, ?_⟩
      · simpa [← ZMod.natCast_eq_natCast_iff] using hz₁
      · rwa [← ZMod.natCast_eq_natCast_iff, Nat.cast_one] at hz₂
    rwa [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, ← ZMod.natCast_val,
      Units.val_one, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff] at hx
  have hz₀ : z.gcd (n * m) = 1 := by
    refine Nat.Coprime.mul_right ?_ ?_
    · exact (ZMod.isUnit_iff_coprime _ _).mp <| hz₁ ▸ x.isUnit
    · exact (ZMod.isUnit_iff_coprime _ _).mp <| hz₂ ▸ isUnit_one
  have := changeLevel_eq_cast_of_dvd χ (n.dvd_mul_right m) (ZMod.unitOfCoprime z hz₀)
  simp only [ZMod.coe_unitOfCoprime, dvd_mul_right, ZMod.cast_natCast] at this
  rw [← hz₁, ← this, h]
  have := changeLevel_eq_cast_of_dvd ψ (m.dvd_mul_left n) (ZMod.unitOfCoprime z hz₀)
  simp only [ZMod.coe_unitOfCoprime, dvd_mul_left, ZMod.cast_natCast] at this
  rw [this, hz₂, map_one]

/-!
### Edge cases
-/

lemma level_one (χ : DirichletCharacter R 1) : χ = 1 := by
  ext
  simp [Units.eq_one]

lemma level_one' (hn : n = 1) : χ = 1 := by
  subst hn
  exact level_one _

instance : Subsingleton (DirichletCharacter R 1) := by
  refine subsingleton_iff.mpr (fun χ χ' ↦ ?_)
  simp [level_one]

noncomputable instance : Unique (DirichletCharacter R 1) := Unique.mk' (DirichletCharacter R 1)

/-- A Dirichlet character of modulus `≠ 1` maps `0` to `0`. -/
lemma map_zero' (hn : n ≠ 1) : χ 0 = 0 :=
  have := ZMod.nontrivial_iff.mpr hn; χ.map_zero

lemma changeLevel_one {d : ℕ} (h : d ∣ n) :
    changeLevel h (1 : DirichletCharacter R d) = 1 := by
  simp

lemma factorsThrough_one_iff : FactorsThrough χ 1 ↔ χ = 1 := by
  refine ⟨fun ⟨_, χ₀, hχ₀⟩ ↦ ?_,
          fun h ↦ ⟨one_dvd n, 1, by rw [h, changeLevel_one]⟩⟩
  rwa [level_one χ₀, changeLevel_one] at hχ₀

/-!
### The conductor
-/

/-- The set of natural numbers `d` such that `χ` factors through a character of level `d`. -/
def conductorSet : Set ℕ := {d : ℕ | FactorsThrough χ d}

lemma mem_conductorSet_iff {x : ℕ} : x ∈ conductorSet χ ↔ FactorsThrough χ x := Iff.refl _

lemma level_mem_conductorSet : n ∈ conductorSet χ := FactorsThrough.same_level χ

lemma mem_conductorSet_dvd {x : ℕ} (hx : x ∈ conductorSet χ) : x ∣ n := hx.dvd

theorem zero_ne_mem_conductorSet (hn : n ≠ 0) : 0 ∉ χ.conductorSet :=
  fun h ↦ hn <| Nat.eq_zero_of_zero_dvd <| FactorsThrough.dvd h

/-- The minimum natural number level `n` through which `χ` factors. -/
noncomputable def conductor : ℕ := sInf (conductorSet χ)

lemma conductor_mem_conductorSet : conductor χ ∈ conductorSet χ :=
  Nat.sInf_mem (Set.nonempty_of_mem (level_mem_conductorSet χ))

lemma conductor_dvd_level : conductor χ ∣ n := (conductor_mem_conductorSet χ).dvd

lemma factorsThrough_conductor : FactorsThrough χ (conductor χ) := conductor_mem_conductorSet χ

lemma conductor_ne_zero (hn : n ≠ 0) : conductor χ ≠ 0 :=
  fun h ↦ hn <| Nat.eq_zero_of_zero_dvd <| h ▸ conductor_dvd_level _

/-- The conductor of the trivial character is 1. -/
lemma conductor_one (hn : n ≠ 0) : conductor (1 : DirichletCharacter R n) = 1 := by
  suffices FactorsThrough (1 : DirichletCharacter R n) 1 by
    have h : conductor (1 : DirichletCharacter R n) ≤ 1 :=
      Nat.sInf_le <| (mem_conductorSet_iff _).mpr this
    exact Nat.le_antisymm h (Nat.pos_of_ne_zero <| conductor_ne_zero _ hn)
  exact (factorsThrough_one_iff _).mpr rfl

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
  rw [changeLevel_trans _ (conductor_dvd_level _) hd.dvd,
      ← (factorsThrough_conductor (Classical.choose hd.2)).2.choose_spec]
  exact hd.eq_changeLevel

variable (χ)

/-- A character is primitive if its level is equal to its conductor. -/
def IsPrimitive : Prop := conductor χ = n

lemma isPrimitive_def : IsPrimitive χ ↔ conductor χ = n := Iff.rfl

lemma isPrimitive_one_level_one : IsPrimitive (1 : DirichletCharacter R 1) :=
  Nat.dvd_one.mp (conductor_dvd_level _)

lemma isPrimitive_one_level_zero : IsPrimitive (1 : DirichletCharacter R 0) :=
  conductor_eq_zero_iff_level_eq_zero.mpr rfl

lemma conductor_one_dvd (n : ℕ) : conductor (1 : DirichletCharacter R 1) ∣ n := by
  rw [(isPrimitive_def _).mp isPrimitive_one_level_one]
  apply one_dvd _

/-- The primitive character associated to a Dirichlet character. -/
noncomputable def primitiveCharacter : DirichletCharacter R χ.conductor :=
  Classical.choose (factorsThrough_conductor χ).choose_spec

theorem changeLevel_primitiveCharacter :
    (changeLevel χ.conductor_dvd_level) χ.primitiveCharacter = χ :=
  (factorsThrough_conductor χ).choose_spec.choose_spec.symm

lemma primitiveCharacter_isPrimitive : IsPrimitive (χ.primitiveCharacter) := by
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

theorem conductor_dvd_of_mem_conductorSet {d : ℕ} (hn : n ≠ 0) (hd : d ∈ χ.conductorSet) :
    χ.conductor ∣ d := by
  have : NeZero d := ⟨by
    contrapose! hd
    exact hd ▸ zero_ne_mem_conductorSet χ hn⟩
  suffices d.gcd χ.conductor ∈ χ.conductorSet by
    have : χ.conductor ≤ d.gcd χ.conductor := Nat.sInf_le this
    contrapose! this
    refine Nat.lt_of_le_of_ne ?_ (Nat.gcd_eq_right_iff_dvd.not.mpr this)
    exact Nat.gcd_le_right _ <| Nat.pos_of_ne_zero <| conductor_ne_zero χ hn
  obtain ⟨hd, χ₀, hχ₀⟩ := hd
  suffices (changeLevel (d.dvd_mul_right χ.conductor)) χ₀ =
      (changeLevel (χ.conductor.dvd_mul_left d)) χ.primitiveCharacter by
    obtain ⟨_, χ₁, hχ₁⟩ := factorsThrough_gcd χ₀ χ.primitiveCharacter this
    refine ⟨Nat.dvd_trans (d.gcd_dvd_left χ.conductor) hd, χ₁, ?_⟩
    rw [changeLevel_trans _ (d.gcd_dvd_left χ.conductor), ← hχ₁, hχ₀]
  have : NeZero (d * χ.conductor * n) :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (NeZero.ne d) (conductor_ne_zero χ hn) ) hn⟩
  apply changeLevel_injective <| Nat.dvd_mul_right (d * χ.conductor) n
  rw [← changeLevel_trans, ← changeLevel_trans,
    changeLevel_trans _ hd (n.dvd_mul_left (d * χ.conductor)), ← hχ₀,
    changeLevel_trans χ.primitiveCharacter χ.conductor_dvd_level, changeLevel_primitiveCharacter]

/-- A divisor `d` of `n` belongs to the conductor set of `χ` if and only if the conductor of `χ`
divides `d`. -/
theorem mem_conductorSet_iff_conductor_dvd (hn : n ≠ 0) {d : ℕ} (hd : d ∣ n) :
    d ∈ χ.conductorSet ↔ χ.conductor ∣ d := by
  refine ⟨fun h ↦ conductor_dvd_of_mem_conductorSet χ hn h, fun h ↦ ?_⟩
  have : NeZero n := ⟨hn⟩
  exact factorsThrough_of_dvd_dvd χ χ.factorsThrough_conductor h hd

private theorem conductor_inv_aux (χ : DirichletCharacter R n) :
    χ⁻¹.conductor ∣ χ.conductor := by
  obtain hn | hn := eq_or_ne n 0
  · rw [conductor_eq_zero_iff_level_eq_zero.mpr hn, conductor_eq_zero_iff_level_eq_zero.mpr hn]
  rw [← mem_conductorSet_iff_conductor_dvd _ hn χ.conductor_dvd_level, mem_conductorSet_iff]
  refine ⟨χ.conductor_dvd_level, χ.primitiveCharacter⁻¹, ?_⟩
  rw [MonoidHom.map_inv, changeLevel_primitiveCharacter]

theorem conductor_inv (χ : DirichletCharacter R n) :
    χ⁻¹.conductor = χ.conductor := by
  refine dvd_antisymm χ.conductor_inv_aux ?_
  convert conductor_inv_aux χ⁻¹
  rw [inv_inv]

/-- Dirichlet character associated to multiplication of Dirichlet characters,
after changing both levels to the same -/
noncomputable def mul {m : ℕ} (χ₁ : DirichletCharacter R n) (χ₂ : DirichletCharacter R m) :
    DirichletCharacter R (Nat.lcm n m) :=
  changeLevel (Nat.dvd_lcm_left n m) χ₁ * changeLevel (Nat.dvd_lcm_right n m) χ₂

/-- Primitive character associated to multiplication of Dirichlet characters,
after changing both levels to the same -/
noncomputable def primitive_mul {m : ℕ} (χ₁ : DirichletCharacter R n)
    (χ₂ : DirichletCharacter R m) : DirichletCharacter R (mul χ₁ χ₂).conductor :=
  primitiveCharacter (mul χ₁ χ₂)

lemma mul_def {n m : ℕ} {χ : DirichletCharacter R n} {ψ : DirichletCharacter R m} :
    χ.primitive_mul ψ = primitiveCharacter (mul χ ψ) :=
  rfl

lemma primitive_mul_isPrimitive {m : ℕ} (ψ : DirichletCharacter R m) :
    IsPrimitive (primitive_mul χ ψ) :=
  primitiveCharacter_isPrimitive _

theorem conductor_mul_dvd_lcm_conductor (hn : n ≠ 0) (χ ψ : DirichletCharacter R n) :
    (χ * ψ).conductor ∣ χ.conductor.lcm ψ.conductor := by
  have h := Nat.lcm_dvd χ.conductor_dvd_level ψ.conductor_dvd_level
  rw [← mem_conductorSet_iff_conductor_dvd _ hn h, mem_conductorSet_iff]
  refine ⟨h, χ.primitiveCharacter.mul ψ.primitiveCharacter, ?_⟩
  rw [mul, MonoidHom.map_mul, ← changeLevel_trans, ← changeLevel_trans,
    changeLevel_primitiveCharacter, changeLevel_primitiveCharacter]

/-- The subgroup of Dirichlet characters of level `n` whose conductor is coprime to `d`. -/
def subgroupOfCoprimeConductor [NeZero n] (d : ℕ) :
    Subgroup (DirichletCharacter R n) where
  carrier := {χ | d.Coprime χ.conductor}
  mul_mem' hχ hψ := by
    apply Nat.Coprime.of_dvd_right (conductor_mul_dvd_lcm_conductor (NeZero.ne n) _ _)
    exact (Nat.Coprime.mul_right hχ hψ).coprime_div_right <| Nat.gcd_dvd_mul _ _
  one_mem' := by simp [conductor_one (NeZero.ne n)]
  inv_mem' hχ := by rwa [Set.mem_setOf, conductor_inv]

@[simp]
lemma mem_subgroupOfCoprimeConductor [NeZero n] (d : ℕ) (χ : DirichletCharacter R n) :
    χ ∈ subgroupOfCoprimeConductor d ↔ d.Coprime χ.conductor := Iff.rfl


/-
### Even and odd characters
-/

section CommRing

variable {S : Type*} [CommRing S] {m : ℕ} (ψ : DirichletCharacter S m)

/-- A Dirichlet character is odd if its value at -1 is -1. -/
def Odd : Prop := ψ (-1) = -1

/-- A Dirichlet character is even if its value at -1 is 1. -/
def Even : Prop := ψ (-1) = 1

lemma even_or_odd [NoZeroDivisors S] : ψ.Even ∨ ψ.Odd := by
  suffices ψ (-1) ^ 2 = 1 by convert sq_eq_one_iff.mp this
  rw [← map_pow _, neg_one_sq, map_one]

lemma not_even_and_odd [NeZero (2 : S)] : ¬(ψ.Even ∧ ψ.Odd) := by
  rintro ⟨(h : _ = 1), (h' : _ = -1)⟩
  simp only [h', neg_eq_iff_add_eq_zero, one_add_one_eq_two, two_ne_zero] at h

lemma Even.not_odd [NeZero (2 : S)] (hψ : Even ψ) : ¬Odd ψ :=
  not_and.mp ψ.not_even_and_odd hψ

lemma Odd.not_even [NeZero (2 : S)] (hψ : Odd ψ) : ¬Even ψ :=
  not_and'.mp ψ.not_even_and_odd hψ

lemma Odd.toUnitHom_eval_neg_one (hψ : ψ.Odd) : ψ.toUnitHom (-1) = -1 := by
  rw [← Units.val_inj, MulChar.coe_toUnitHom]
  exact hψ

lemma Even.toUnitHom_eval_neg_one (hψ : ψ.Even) : ψ.toUnitHom (-1) = 1 := by
  rw [← Units.val_inj, MulChar.coe_toUnitHom]
  exact hψ

lemma Odd.eval_neg (x : ZMod m) (hψ : ψ.Odd) : ψ (-x) = - ψ x := by
  rw [Odd] at hψ
  rw [← neg_one_mul, map_mul]
  simp [hψ]

lemma Even.eval_neg (x : ZMod m) (hψ : ψ.Even) : ψ (-x) = ψ x := by
  rw [Even] at hψ
  rw [← neg_one_mul, map_mul]
  simp [hψ]

/-- An even Dirichlet character is an even function. -/
lemma Even.to_fun {χ : DirichletCharacter S m} (hχ : Even χ) : Function.Even χ :=
  fun _ ↦ by rw [← neg_one_mul, map_mul, hχ, one_mul]

/-- An odd Dirichlet character is an odd function. -/
lemma Odd.to_fun {χ : DirichletCharacter S m} (hχ : Odd χ) : Function.Odd χ :=
  fun _ ↦ by rw [← neg_one_mul, map_mul, hχ, neg_one_mul]

end CommRing

end DirichletCharacter
