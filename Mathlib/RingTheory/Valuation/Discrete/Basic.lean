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

open LinearOrderedCommGroup MonoidWithZeroHom Set

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

section Ring

variable {A : Type*} [Ring A] (v : Valuation A Γ)

/-- Given a linearly ordered commutative group with zero `Γ` such that `Γˣ` is
nontrivial cyclic, a valuation `v : A → Γ` on a ring `A` is *discrete*, if
`genLTOne Γˣ` belongs to the image. Note that the latter is equivalent to
asking that `1 : ℤ` belongs to the image of the corresponding additive valuation. -/
class IsRankOneDiscrete : Prop where
  exists_generator_lt_one' : ∃ (γ : Γˣ), Subgroup.zpowers γ = (valueGroup v) ∧ γ < 1

namespace IsRankOneDiscrete

variable [IsRankOneDiscrete v]

lemma exists_generator_lt_one : ∃ (γ : Γˣ), Subgroup.zpowers γ = valueGroup v ∧ γ < 1 :=
  exists_generator_lt_one'

/-- Given a discrete valuation `v`, `Valuation.IsRankOneDiscrete.generator` is a generator of
the value group that is `< 1`. -/
noncomputable def generator : Γˣ := (exists_generator_lt_one v).choose

lemma generator_zpowers_eq_valueGroup : (Subgroup.zpowers (generator v)) = valueGroup v :=
  (exists_generator_lt_one v).choose_spec.1

lemma generator_mem_valueGroup :
    (IsRankOneDiscrete.generator v) ∈ valueGroup v := by
  rw [← IsRankOneDiscrete.generator_zpowers_eq_valueGroup]
  exact Subgroup.mem_zpowers (IsRankOneDiscrete.generator v)

lemma generator_lt_one: (generator v) < 1 :=
  (exists_generator_lt_one v).choose_spec.2

lemma generator_ne_one : (generator v) ≠ 1 :=
  ne_of_lt <| generator_lt_one v

lemma generator_zpowers_eq_range (K : Type*) [Field K] (w : Valuation K Γ) [IsRankOneDiscrete w] :
    Units.val '' (Subgroup.zpowers (generator w)) = range w \ {0} := by
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
  simp only [Subgroup.mem_top, forall_const]
  use k
  ext
  simp [← hk]

instance : Nontrivial (valueGroup v) :=
  ⟨1, ⟨generator v, by simp [← generator_zpowers_eq_valueGroup]⟩, ne_of_gt <| generator_lt_one v⟩

instance [IsRankOneDiscrete v] : Nontrivial (valueMonoid v) := by
  by_contra H
  apply ((valueGroup v).nontrivial_iff_ne_bot).mp (by infer_instance)
  apply Subgroup.closure_eq_bot_iff.mpr
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

end IsRankOneDiscrete

theorem not_isField [Nontrivial ↥(valueGroup v)] [IsCyclic (valueGroup v)] : ¬ IsField K₀ := by
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
      (not_isField v) hr
  obtain ⟨π, hπ⟩ := exists_isUniformizer_of_isCyclic_of_nontrivial v
  obtain ⟨n, u, hu⟩ := pow_Uniformizer hr₀ ⟨π, hπ⟩
  rw [Uniformizer.is_generator ⟨π, hπ⟩, span_singleton_eq_span_singleton] at hr
  exact hπ.of_associated hr

end Field

end Valuation
