/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.Algebra.GroupWithZero.Range
import Mathlib.Algebra.Order.Group.Cyclic
import Mathlib.Algebra.Order.Group.Units
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Discrete Valuations

Given a linearly ordered commutative group with zero `Γ`, a valuation `v : A → Γ` on a ring `A` is
*discrete*, if there is an element `γ : Γˣ` that is `< 1` and generated the range of `v`,
implemented as `MonoidWithZeroHom.valueGroup v`. When `Γ := ℤₘ₀` (defined in
`Multiplicative.termℤₘ₀`), `γ` = ofAdd (-1)` and the condition of being discrete is
equivalent to asking that `ofAdd (-1 : ℤ)` belongs to the image, in turn equivalent to asking that
`1 : ℤ` belongs to the image of the corresponding *additive* valuation.

Note that this definition of discrete implies that the valuation is nontrivial and of rank one, as
is commonly assumed in number theory. To avoid potential confusion with other definitions of
discrete, we use the name `IsRankOneDiscrete` to refer to discrete valuations in this setting.

## Main Definitions
* `Valuation.IsRankOneDiscrete`: We define a `Γ`-valued valuation `v` to be discrete if if there is
an element `γ : Γˣ` that is `< 1` and generates the range of `v`.
* `Valuation.IsUniformizer`: Given a `Γ`-valued valuation `v` on a ring `R`, an element `π : R` is
  a uniformizer if `v π` is a generator of the value group that is `<1`.
* `Valuation.Uniformizer`: A structure bundling an element of a ring and a proof that it is a
  uniformizer.

## Main Results
* `Valuation.IsUniformizer.of_associated`: An element associated to a uniformizer is itself a
  uniformizer.
* `Valuation.associated_of_isUniformizer`: If two elements are uniformizers, they are associated.
* `Valuation.IsUniformizer.is_generator` A generator of the maximal ideal is a uniformizer when
  the valuation is discrete.
* `Valuation.IsRankOneDiscrete.mk'`: if the `valueGroup` of the valuation `v` is cyclic and
  nontrivial, then `v` is discrete.
* `Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial`: If `v` is a valuation on a field `K`
  whose value group is cyclic and nontrivial, then there exists a uniformizer for `v`.
* `Valuation.isUniformizer_of_maximalIdeal_eq_span`: Given a discrete valuation `v` on a field `K`,
  a generator of the maximal ideal of `v.valuationSubring` is a uniformizer for `v`.

## TODO
* Relate discrete valuations and discrete valuation rings (contained in the project
  <https://github.com/mariainesdff/LocalClassFieldTheory>)
-/

namespace Valuation

open LinearOrderedCommGroup MonoidWithZeroHom Set Subgroup

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

section Ring

variable {A : Type*} [Ring A] (v : Valuation A Γ)

/-- Given a linearly ordered commutative group with zero `Γ` such that `Γˣ` is
nontrivial cyclic, a valuation `v : A → Γ` on a ring `A` is *discrete*, if
`genLTOne Γˣ` belongs to the image. Note that the latter is equivalent to
asking that `1 : ℤ` belongs to the image of the corresponding additive valuation. -/
class IsRankOneDiscrete : Prop where
  exists_generator_lt_one' : ∃ (γ : Γˣ), zpowers γ = (valueGroup v) ∧ γ < 1

namespace IsRankOneDiscrete

variable [IsRankOneDiscrete v]

lemma exists_generator_lt_one : ∃ (γ : Γˣ), zpowers γ = valueGroup v ∧ γ < 1 :=
  exists_generator_lt_one'

/-- Given a discrete valuation `v`, `Valuation.IsRankOneDiscrete.generator` is a generator of
the value group that is `< 1`. -/
noncomputable def generator : Γˣ := (exists_generator_lt_one v).choose

lemma generator_zpowers_eq_valueGroup : zpowers (generator v) = valueGroup v :=
  (exists_generator_lt_one v).choose_spec.1

lemma generator_mem_valueGroup :
    (IsRankOneDiscrete.generator v) ∈ valueGroup v := by
  rw [← IsRankOneDiscrete.generator_zpowers_eq_valueGroup]
  exact mem_zpowers (IsRankOneDiscrete.generator v)

lemma generator_lt_one : generator v < 1 :=
  (exists_generator_lt_one v).choose_spec.2

lemma generator_ne_one : generator v ≠ 1 :=
  ne_of_lt <| generator_lt_one v

lemma generator_zpowers_eq_range (K : Type*) [Field K] (w : Valuation K Γ) [IsRankOneDiscrete w] :
    Units.val '' (zpowers (generator w)) = range w \ {0} := by
  rw [generator_zpowers_eq_valueGroup, valueGroup_eq_range]

lemma generator_mem_range (K : Type*) [Field K] (w : Valuation K Γ) [IsRankOneDiscrete w] :
    ↑(generator w) ∈ range w := by
  apply diff_subset
  rw [← generator_zpowers_eq_range]
  exact ⟨generator w, by simp⟩

lemma generator_ne_zero : (generator v : Γ) ≠ 0 := by simp

instance : IsCyclic <| valueGroup v := by
  rw [isCyclic_iff_exists_zpowers_eq_top, ← generator_zpowers_eq_valueGroup]
  use ⟨generator v, by simp⟩
  rw [eq_top_iff]
  rintro ⟨g, k, hk⟩
  simp only [mem_top, forall_const]
  use k
  ext
  simp [← hk]

instance : Nontrivial (valueGroup v) :=
  ⟨1, ⟨generator v, by simp [← generator_zpowers_eq_valueGroup]⟩, ne_of_gt <| generator_lt_one v⟩

instance [IsRankOneDiscrete v] : Nontrivial (valueMonoid v) := by
  by_contra H
  apply ((valueGroup v).nontrivial_iff_ne_bot).mp (by infer_instance)
  apply closure_eq_bot_iff.mpr
  rw [not_nontrivial_iff_subsingleton, subsingleton_iff] at H
  intro x hx
  specialize H ⟨x, hx⟩ ⟨1, one_mem_valueMonoid v⟩
  simpa using H

instance [IsRankOneDiscrete v] : v.IsNontrivial := by
  constructor
  obtain ⟨⟨γ, π, hπ⟩, hγ⟩ := (nontrivial_iff_exists_ne (1 : valueMonoid v)).mp (by infer_instance)
  use π
  constructor
  · simp [hπ]
  · rw [hπ]
    simp only [← MonoidWithZeroHom.coe_one, ne_eq, Subtype.mk.injEq] at hγ
    simp [hγ, Units.val_eq_one]


lemma valueGroup_genLTOne_eq_generator : (valueGroup v).genLTOne = generator v :=
  ((valueGroup v).genLTOne_unique (generator_lt_one v) (generator_zpowers_eq_valueGroup v)).symm

end IsRankOneDiscrete

section IsRankOneDiscrete

variable [hv : IsRankOneDiscrete v]

/-- An element `π : A` is a uniformizer if `v π` is a generator of the value group that is `< 1`. -/
def IsUniformizer (π : A) : Prop := v π = hv.generator

variable {v} {π : A}

namespace IsUniformizer

theorem iff : v.IsUniformizer π ↔ v π = hv.generator := refl _

theorem ne_zero (hπ : IsUniformizer v π) : π ≠ 0 := by
  intro h0
  rw [h0, IsUniformizer, map_zero] at hπ
  exact (Units.ne_zero _).symm hπ

@[simp]
lemma val (hπ : v.IsUniformizer π) : v π = hv.generator := hπ

lemma val_lt_one (hπ : v.IsUniformizer π) : v π < 1 := hπ ▸ hv.generator_lt_one

lemma val_ne_zero (hπ : v.IsUniformizer π) : v π ≠ 0 := by
  by_contra h0
  simp only [IsUniformizer, h0] at hπ
  exact (Units.ne_zero _).symm hπ

theorem val_pos (hπ : IsUniformizer v π) : 0 < v π := by
  rw [IsUniformizer.iff] at hπ; simp [zero_lt_iff, ne_eq, hπ]

lemma zpowers_eq_valueGroup (hπ : v.IsUniformizer π) :
    valueGroup v = zpowers (Units.mk0 (v π) hπ.val_ne_zero) := by
  rw [← (valueGroup v).genLTOne_zpowers_eq_top]
  congr
  simp only [val, Units.mk0_val, hπ]
  exact IsRankOneDiscrete.valueGroup_genLTOne_eq_generator v

end IsUniformizer

variable (v) in
/-- The structure `Uniformizer` bundles together the term in the ring and a proof that it is a
  uniformizer. -/
@[ext]
structure Uniformizer where
  /-- The integer underlying a `Uniformizer` -/
  val : v.integer
  valuation_gt_one : v.IsUniformizer val

namespace Uniformizer

/-- A constructor for `Uniformizer`. -/
def mk' {x : A} (hx : v.IsUniformizer x) : v.Uniformizer where
  val := ⟨x, le_of_lt hx.val_lt_one⟩
  valuation_gt_one := hx

@[simp]
instance : Coe v.Uniformizer v.integer := ⟨fun π ↦ π.val⟩

theorem ne_zero (π : Uniformizer v) : π.1.1 ≠ 0 := π.2.ne_zero

end Uniformizer

end IsRankOneDiscrete

end Ring

section CommRing

variable {R : Type*} [CommRing R] {v : Valuation R Γ} [hv : IsRankOneDiscrete v]

theorem IsUniformizer.not_isUnit {π : v.integer} (hπ : IsUniformizer v π) : ¬ IsUnit π :=
  fun h ↦ ne_of_gt hπ.val_lt_one (Integers.one_of_isUnit (integer.integers v) h).symm

end CommRing

section Ring

variable {R : Type*} [Ring R] (v : Valuation R Γ) [IsCyclic (valueGroup v)]
  [Nontrivial (valueGroup v)]

instance IsRankOneDiscrete.mk' : IsRankOneDiscrete v :=
  ⟨(valueGroup v).genLTOne,
    ⟨(valueGroup v).genLTOne_zpowers_eq_top, (valueGroup v).genLTOne_lt_one⟩⟩

end Ring

section Field

open Ideal IsLocalRing Valuation.IsRankOneDiscrete

variable {K : Type*} [Field K] (v : Valuation K Γ)

/- When the valuation is defined over a field instead that simply on a (commutative) ring, we use
the notion of `valuationSubring` instead of the weaker one of `integer` to access the
corresponding API. -/
local notation "K₀" => v.valuationSubring

section IsNontrivial

variable [IsCyclic (valueGroup v)] [Nontrivial (valueGroup v)]

theorem exists_isUniformizer_of_isCyclic_of_nontrivial : ∃ π : K₀, IsUniformizer v (π : K) := by
  simp only [IsUniformizer.iff, Subtype.exists, mem_valuationSubring_iff, exists_prop]
  set g := (valueGroup v).genLTOne with hg
  obtain ⟨⟨π, hπ⟩, hγ0⟩ : g.1 ∈ ((range v) \ {0}) := by
    rw [← valueGroup_eq_range, hg]
    exact mem_image_of_mem Units.val (valueGroup v).genLTOne_mem
  use π
  rw [hπ, hg]
  exact ⟨le_of_lt (valueGroup v).genLTOne_lt_one, by rw [valueGroup_genLTOne_eq_generator]⟩

instance : Nonempty (Uniformizer v) :=
  ⟨⟨(exists_isUniformizer_of_isCyclic_of_nontrivial v).choose,
    (exists_isUniformizer_of_isCyclic_of_nontrivial v).choose_spec⟩⟩

end IsNontrivial

section IsRankOneDiscrete

section Uniformizer

variable {v} [hv : v.IsRankOneDiscrete]

/-- An element associated to a uniformizer is itself a uniformizer. -/
theorem IsUniformizer.of_associated {π₁ π₂ : K₀} (h1 : IsUniformizer v π₁)
    (H : Associated π₁ π₂) : IsUniformizer v π₂ := by
  obtain ⟨u, hu⟩ := H
  have : v (u.1 : K) = 1 := (Integers.isUnit_iff_valuation_eq_one <|integer.integers v).mp u.isUnit
  rwa [IsUniformizer.iff, ← hu, Subring.coe_mul, map_mul, this, mul_one, ← IsUniformizer.iff]

/-- If two elements of `K₀` are uniformizers, then they are associated. -/
theorem associated_of_isUniformizer {π₁ π₂ : K₀} (h1 : IsUniformizer v π₁)
    (h2 : IsUniformizer v π₂) : Associated π₁ π₂ := by
  have hval : v ((π₁ : K)⁻¹ * π₂) = 1 := by
    simp [IsUniformizer.iff.mp h1, IsUniformizer.iff.mp h2]
  set p : v.integer := ⟨(π₁.1 : K)⁻¹ * π₂.1, (v.mem_integer_iff _).mpr (le_of_eq hval)⟩ with hp
  use ((Integers.isUnit_iff_valuation_eq_one (x := p) <| integer.integers v).mpr hval).unit
  apply_fun ((↑) : K₀ → K) using Subtype.val_injective
  simp [hp, ← mul_assoc, mul_inv_cancel₀ h1.ne_zero]

theorem exists_pow_Uniformizer {r : K₀} (hr : r ≠ 0) (π : Uniformizer v) :
    ∃ n : ℕ, ∃ u : K₀ˣ, r = (π.1 ^ n).1 * u.1 := by
  have hr₀ : v r ≠ 0 := by rw [ne_eq, zero_iff, Subring.coe_eq_zero_iff]; exact hr
  set vr : Γˣ := Units.mk0 (v r) hr₀ with hvr_def
  have hvr : vr ∈ (valueGroup v) := by
    apply mem_valueGroup
    rw [hvr_def, Units.val_mk0 hr₀]
    exact mem_range_self _
  rw [π.2.zpowers_eq_valueGroup, mem_zpowers_iff] at hvr
  obtain ⟨m, hm⟩ := hvr
  have hm' : v π.val ^ m = v r := by
    rw [hvr_def] at hm
    rw [← Units.val_mk0 hr₀, ← hm]
    simp [Units.val_zpow_eq_zpow_val, Units.val_mk0]
  have hm₀ : 0 ≤ m := by
    rw [← zpow_le_one_iff_right_of_lt_one₀ π.2.val_pos π.2.val_lt_one, hm']
    exact r.2
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hm₀
  use n
  have hpow : v (π.1.1 ^ (-m) * r) = 1 := by
    rw [map_mul, map_zpow₀, ← hm', zpow_neg, hm', inv_mul_cancel₀ hr₀]
  set a : K₀ := ⟨π.1.1 ^ (-m) * r, by apply le_of_eq hpow⟩ with ha
  have ha₀ : (↑a : K) ≠ 0 := by
    simp only [zpow_neg, ne_eq, mul_eq_zero, inv_eq_zero, ZeroMemClass.coe_eq_zero, not_or, ha]
    refine ⟨?_, hr⟩
    rw [hn, zpow_natCast, pow_eq_zero_iff', not_and_or]
    exact Or.inl π.ne_zero
  have h_unit_a : IsUnit a :=
    Integers.isUnit_of_one (integer.integers v) (isUnit_iff_ne_zero.mpr ha₀) hpow
  use h_unit_a.unit
  rw [IsUnit.unit_spec, Subring.coe_pow, ha, ← mul_assoc, zpow_neg, hn, zpow_natCast,
    mul_inv_cancel₀ (pow_ne_zero _ π.ne_zero), one_mul]

theorem Uniformizer.is_generator (π : Uniformizer v) :
    maximalIdeal v.valuationSubring = Ideal.span {π.1} := by
  apply (maximalIdeal.isMaximal _).eq_of_le
  · intro h
    rw [Ideal.span_singleton_eq_top] at h
    apply π.2.not_isUnit h
  · intro x hx
    by_cases hx₀ : x = 0
    · simp [hx₀]
    · obtain ⟨n, ⟨u, hu⟩⟩ := exists_pow_Uniformizer hx₀ π
      rw [← Subring.coe_mul, Subtype.coe_inj] at hu
      have hn : Not (IsUnit x) := fun h ↦
        (maximalIdeal.isMaximal _).ne_top (eq_top_of_isUnit_mem _ hx h)
      replace hn : n ≠ 0 := fun h ↦ by
        simp only [hu, h, pow_zero, one_mul, Units.isUnit, not_true] at hn
      simp [Ideal.mem_span_singleton, hu, dvd_pow_self _ hn]

theorem IsUniformizer.is_generator {π : v.valuationSubring} (hπ : IsUniformizer v π) :
    maximalIdeal v.valuationSubring = Ideal.span {π} :=
  Uniformizer.is_generator ⟨π, hπ⟩

theorem pow_Uniformizer_is_pow_generator (π : Uniformizer v) (n : ℕ) :
    maximalIdeal v.valuationSubring ^ n = Ideal.span {π.1 ^ n} := by
  rw [← Ideal.span_singleton_pow, Uniformizer.is_generator]

end Uniformizer

end IsRankOneDiscrete

theorem valuationSubring_not_isField [Nontrivial ↥(valueGroup v)] [IsCyclic (valueGroup v)] :
    ¬ IsField K₀ := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer_of_isCyclic_of_nontrivial v
  rintro ⟨-, -, h⟩
  have := hπ.ne_zero
  simp only [ne_eq, Subring.coe_eq_zero_iff] at this
  specialize h this
  rw [← isUnit_iff_exists_inv] at h
  exact hπ.not_isUnit h

theorem isUniformizer_of_maximalIdeal_eq_span [v.IsRankOneDiscrete] {r : K₀}
    (hr : maximalIdeal v.valuationSubring = Ideal.span {r}) :
    IsUniformizer v r := by
  have hr₀ : r ≠ 0 := by
    intro h
    rw [h, Set.singleton_zero, span_zero] at hr
    exact Ring.ne_bot_of_isMaximal_of_not_isField (maximalIdeal.isMaximal v.valuationSubring)
      (valuationSubring_not_isField v) hr
  obtain ⟨π, hπ⟩ := exists_isUniformizer_of_isCyclic_of_nontrivial v
  obtain ⟨n, u, hu⟩ := exists_pow_Uniformizer hr₀ ⟨π, hπ⟩
  rw [Uniformizer.is_generator ⟨π, hπ⟩, span_singleton_eq_span_singleton] at hr
  exact hπ.of_associated hr

end Field

end Valuation
