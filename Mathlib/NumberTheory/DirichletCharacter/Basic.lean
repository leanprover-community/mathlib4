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

dirichlet character, periodic, modulus
-/
-- TODO: move to Data.ZMod.Basic?!
@[simp]
lemma cast_hom_self {n : ℕ} : ZMod.castHom dvd_rfl (ZMod n) = RingHom.id (ZMod n) :=
  RingHom.ext_zmod (ZMod.castHom dvd_rfl (ZMod n)) (RingHom.id (ZMod n))

@[reducible]
def DirichletCharacter (R : Type) [Monoid R] (n : ℕ) := (ZMod n)ˣ →* Rˣ

-- TODO: move to NumberTheory.LegendreSymbol.MulCharacter?!
namespace MulChar
lemma coe_toMonoidHom {R R' : Type} [CommMonoid R] [CommMonoidWithZero R'] (χ : MulChar R R')
(x : R) : χ.toMonoidHom x = χ x := by solve_by_elim
end MulChar

open MulChar
-- a difference is that originally asso_dirichlet_char only required MonoidWithZero, dont know why the Comm is needed here
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

--Comm required from here
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
    have := RingHom.toMonoidHom_eq_coe (ZMod.castHom hm (ZMod n))
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

/-- χ₀ of level d factors through χ of level n if d ∣ n and χ₀ = χ ∘ (ZMod n → ZMod d). -/
structure factors_through (d : ℕ) : Prop :=
(dvd : d ∣ n)
(ind_char : ∃ χ₀ : DirichletCharacter R d, χ = change_level dvd χ₀)

namespace factors_through
lemma spec {d : ℕ} (h : factors_through χ d) :
  χ = change_level h.1 (Classical.choose (h.ind_char)) := Classical.choose_spec (h.ind_char)
end factors_through

/-- The set of natural numbers for which a Dirichlet character is periodic. -/
def conductor_set : Set ℕ := {x : ℕ | χ.factors_through x}

lemma mem_conductor_set_iff {x : ℕ} : x ∈ χ.conductor_set ↔ χ.factors_through x := Iff.refl _

lemma level_mem_conductor_set : n ∈ conductor_set χ := (mem_conductor_set_iff _).2
{ dvd := dvd_rfl,
  ind_char := ⟨χ, (change_level.self χ).symm⟩, }

lemma mem_conductor_set_dvd {x : ℕ} (hx : x ∈ χ.conductor_set) : x ∣ n := hx.1

lemma mem_conductor_set_factors_through {x : ℕ} (hx : x ∈ χ.conductor_set) : χ.factors_through x := hx

/-- The minimum natural number n for which a Dirichlet character is periodic.
  The Dirichlet character χ can then alternatively be reformulated on ℤ/nℤ. -/
noncomputable def conductor : ℕ := sInf (conductor_set χ)

namespace conductor
lemma mem_conductor_set : conductor χ ∈ conductor_set χ :=
Nat.sInf_mem (Set.nonempty_of_mem χ.level_mem_conductor_set)

lemma dvd_lev : χ.conductor ∣ n := (mem_conductor_set χ).1

lemma factors_through : χ.factors_through χ.conductor := mem_conductor_set χ

lemma eq_one (hχ : χ.conductor = 1) : χ = 1 := by
  obtain ⟨h', χ₀, h⟩ := factors_through χ
  rw [h]
  ext
  rw [Units.eq_iff, change_level_def]
  simp only [Function.comp_apply, MonoidHom.one_apply, MonoidHom.coe_comp]
  convert MonoidHom.map_one χ₀
  have : Subsingleton (ZMod (conductor χ))ˣ
  · rw [hχ]
    infer_instance
  refine Subsingleton.elim _ _

lemma one (hn : 0 < n) : (1 : DirichletCharacter R n).conductor = 1 := by
  suffices : (1 : DirichletCharacter R n).conductor ≤ 1
  · cases' Nat.le_one_iff_eq_zero_or_eq_one.mp this with h1 h2
    · exfalso
      have := factors_through.dvd (factors_through (1 : DirichletCharacter R n))
      rw [h1, zero_dvd_iff] at this
      rw [this] at hn
      apply lt_irrefl _ hn
    · exact h2
  · apply Nat.sInf_le ((mem_conductor_set_iff _).2 ⟨one_dvd _, 1, _⟩)
    ext
    rw [Units.eq_iff, change_level_def]
    simp only [MonoidHom.one_comp]

variable {χ}
lemma eq_one_iff (hn : 0 < n) : χ = 1 ↔ χ.conductor = 1 :=
⟨λ h => by { rw [h, one hn] }, λ h => by { rw [eq_one χ h] }⟩

lemma eq_zero_iff_level_eq_zero : χ.conductor = 0 ↔ n = 0 :=
⟨λ h => by
  rw [←zero_dvd_iff]
  convert dvd_lev χ
  rw [h],
  λ h => by
  rw [conductor, Nat.sInf_eq_zero]
  left
  refine ⟨zero_dvd_iff.2 h,
  ⟨change_level (by {rw [h]}) χ,
  by rw [←change_level.trans _ _ _, change_level.self _]⟩ ⟩ ⟩
end conductor

/-- A character is primitive if its level is equal to its conductor. -/
def is_primitive : Prop := χ.conductor = n

lemma is_primitive_def : χ.is_primitive ↔ χ.conductor = n := ⟨λ h => h, λ h => h⟩

namespace is_primitive
lemma one : is_primitive (1 : DirichletCharacter R 1) := Nat.dvd_one.1 (conductor.dvd_lev _)

lemma one_lev_zero : (1 : DirichletCharacter R 0).is_primitive :=
by
  rw [is_primitive_def, conductor, Nat.sInf_eq_zero]
  left
  rw [conductor_set]
  simp only [Set.mem_setOf_eq]
  fconstructor
  simp only [true_and, ZMod.cast_id', id.def, MonoidHom.coe_mk, dvd_zero]
  refine ⟨1, rfl⟩

end is_primitive

lemma conductor_one_dvd (n : ℕ) : conductor (1 : DirichletCharacter R 1) ∣ n := by
  rw [(is_primitive_def _).1 is_primitive.one]
  apply one_dvd _

/-- If m = n are positive natural numbers, then ZMod m ≃ ZMod n. -/
def ZMod.mul_equiv {a b : ℕ} (h : a = b) : ZMod a ≃* ZMod b := by rw [h]

/-- If m = n are positive natural numbers, then their Dirichlet character spaces are the same. -/
def equiv {a b : ℕ} (h : a = b) : DirichletCharacter R a ≃* DirichletCharacter R b := by { rw [h] }

/-- The primitive character associated to a Dirichlet character. -/
noncomputable def reduction : DirichletCharacter R χ.conductor :=
  Classical.choose ((conductor.factors_through χ).ind_char)

lemma mem_conductor_set_eq_conductor {d : ℕ} (hd : d ∈ χ.conductor_set) :
  χ.conductor ≤ (Classical.choose hd.2).conductor :=
by
  apply Nat.sInf_le
  rw [conductor_set]
  simp only [Set.mem_setOf_eq, MonoidHom.coe_mk]
  -- i dont know why refine wont work here
  --refine ⟨dvd_trans (conductor.dvd_lev _) hd.1, ⟨Classical.choice ⟨Exists.choose (conductor.factors_through (Classical.choice ⟨Exists.choose hd.2⟩)).2⟩, _⟩⟩
  fconstructor
  · apply dvd_trans (conductor.dvd_lev _) hd.1
  · use Classical.choose (conductor.factors_through (Classical.choose hd.2)).2
    convert factors_through.spec χ hd using 1
    -- dont know if defining k will help
    --set k : ℕ := (conductor (Classical.choice ⟨Exists.choose hd.2⟩)) with hk
    have : (ZMod.castHom (dvd_trans (conductor.dvd_lev (Classical.choose hd.2)) hd.1)
      (ZMod (conductor (Classical.choose hd.2))) : MonoidHom (ZMod n)
      (ZMod (conductor (Classical.choose hd.2)))) = ((ZMod.castHom (conductor.dvd_lev (Classical.choose hd.2))
      (ZMod (conductor (Classical.choose hd.2)))) : MonoidHom (ZMod d)
      (ZMod (conductor (Classical.choose hd.2)))).comp (ZMod.castHom hd.1
      (ZMod d) : MonoidHom (ZMod n) (ZMod d))
    · suffices : (ZMod.castHom (dvd_trans (conductor.dvd_lev (Classical.choose hd.2)) hd.1)
      (ZMod (conductor (Classical.choose hd.2)))) = ((ZMod.castHom (conductor.dvd_lev (Classical.choose hd.2))
      (ZMod (conductor (Classical.choose hd.2))))).comp (ZMod.castHom hd.1 (ZMod d))
      · rw [this]
        ext
        simp only [MonoidHom.coe_coe, RingHom.coe_comp, Function.comp_apply, ZMod.castHom_apply, MonoidHom.coe_comp]
      · apply RingHom.ext_zmod _ _
    rw [change_level_def, this, Units.map_comp, ←MonoidHom.comp_assoc]
    congr
    change change_level _ _ = _
    apply (factors_through.spec _ (conductor.factors_through _)).symm

lemma reduction_is_primitive : (χ.reduction).is_primitive := by
  by_cases χ.conductor = 0
  · rw [is_primitive_def]
    conv_rhs => rw [h]
    rw [conductor.eq_zero_iff_level_eq_zero, h]
  refine le_antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero h) (conductor.dvd_lev _))
    (mem_conductor_set_eq_conductor _ (conductor.mem_conductor_set _))

lemma reduction_one (hn : 0 < n) : (1 : DirichletCharacter R n).reduction = 1 := by
  rw [conductor.eq_one_iff _]
  · have := reduction_is_primitive (1 : DirichletCharacter R n)
    rw [is_primitive_def] at this
    rw [this, conductor.one hn]
    --convert reduction_is_primitive (1 : DirichletCharacter R n)
    --rw [conductor.one hn]
  · rw [conductor.one hn]
    apply Nat.one_pos

lemma ofUnitHom_mul (ψ : DirichletCharacter R n) :
  ofUnitHom (χ * ψ) = (ofUnitHom χ) * (ofUnitHom ψ) := by
  ext
  simp

lemma asso_primitive_conductor_eq {n : ℕ} (χ : DirichletCharacter R n) :
    χ.reduction.conductor = χ.conductor :=
(is_primitive_def χ.reduction).1 (reduction_is_primitive χ)

open Nat
/-- Primitive character associated to multiplication of Dirichlet characters,
  after changing both levels to the same -/
noncomputable def mul {m : ℕ} (χ₁ : DirichletCharacter R n) (χ₂ : DirichletCharacter R m) :=
reduction (change_level (dvd_lcm_left n m) χ₁ * change_level (dvd_lcm_right n m) χ₂)

lemma mul_def {n m : ℕ} {χ : DirichletCharacter R n} {ψ : DirichletCharacter R m} :
  χ.mul ψ = reduction (change_level _ χ * change_level _ ψ) := rfl

namespace is_primitive
lemma mul {m : ℕ} (ψ : DirichletCharacter R m) : (mul χ ψ).is_primitive :=
reduction_is_primitive _
end is_primitive

variable {S : Type} [CommRing S] {m : ℕ} (ψ : DirichletCharacter S m)

/-- A Dirichlet character is odd if its value at -1 is -1. -/
def is_odd : Prop := ψ (-1) = -1

/-- A Dirichlet character is even if its value at -1 is 1. -/
def is_even : Prop := ψ (-1) = 1

lemma is_odd_or_is_even [NoZeroDivisors S] : ψ.is_odd ∨ ψ.is_even :=
by
  suffices : (ψ (-1))^2 = 1
  · rw [←Units.eq_iff] at this
    conv_rhs at this => rw [←one_pow 2]
    rw [←sub_eq_zero] at this
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
    --simp only [Units.coe_one, Units.coe_pow] at this
    rw [_root_.sq_sub_sq, _root_.mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at this
    cases this
    · left
      rw [is_odd, ←Units.eq_iff]
      simp only [this, Units.coe_neg_one]
      assumption
    · right
      rw [is_even, ←Units.eq_iff]
      simp only [this, Units.val_one]
      assumption
  · rw [←MonoidHom.map_pow, ←MonoidHom.map_one ψ]
    congr
    rw [Units.ext_iff]
    simp only [Units.val_one, Units.coe_neg_one]
    rw [neg_one_sq, Units.val_one]

lemma odd_ofUnitHom_eval_neg_one (hψ : ψ.is_odd) :
  ofUnitHom ψ (-1) = -1 := by
  rw [is_odd] at hψ
  -- really requires ψ to be given explicitly
  convert ofUnitHom_coe ψ (-1)
  rw [hψ]
  simp

lemma even_ofUnitHom_eval_neg_one (hψ : ψ.is_even) :
  ofUnitHom ψ (-1) = 1 := by
  rw [is_even] at hψ
  convert ofUnitHom_coe ψ (-1)
  rw [hψ]
  simp

lemma asso_odd_DirichletCharacter_eval_sub (x : ZMod m) (hψ : ψ.is_odd) :
  ofUnitHom ψ (m - x) = -(ofUnitHom ψ x) := by
  rw [ofUnitHom_eval_sub, ←neg_one_mul, ←MulChar.coe_toMonoidHom,
    MonoidHom.map_mul _ _ x, MulChar.coe_toMonoidHom,
    odd_ofUnitHom_eval_neg_one _ hψ]
  simp [MulChar.coe_toMonoidHom] --make Mulchar.map_mul

lemma asso_even_DirichletCharacter_eval_sub (x : ZMod m) (hψ : ψ.is_even) :
  ofUnitHom ψ (m - x) = ofUnitHom ψ x := by
  rw [ofUnitHom_eval_sub, ←neg_one_mul, ←MulChar.coe_toMonoidHom,
    MonoidHom.map_mul, MulChar.coe_toMonoidHom,
    even_ofUnitHom_eval_neg_one _ hψ]
  simp [MulChar.coe_toMonoidHom]

end DirichletCharacter
