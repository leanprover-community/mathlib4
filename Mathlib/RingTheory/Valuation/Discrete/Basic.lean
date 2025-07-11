/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.Algebra.GroupWithZero.Range
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.Valuation.Basic

/-!
# Discrete Valuations

Given a linearly ordered commutative group with zero `Γ`, a valuation `v : A → Γ` on a ring `A` is
*discrete*, if there is an element `γ : Γˣ` that is `< 1` and generated the range of `v`,
implemented as `MonoidHomWithZero.valueGroup v`. When `Γ := ℤᵐ⁰`, `γ = ofAdd (-1)` and the condition
of being discrete is
equivalent to asking that `ofAdd (-1 : ℤ)` belongs to the image, in turn equivalent to asking that
`1 : ℤ` belongs to the image of the corresponding *additive* valuation.

Note that this definition of discrete implies that the valuation is nontrivial and of rank one, as
is commonly assumed in number theory. To avoid potential confusion with other definitions of
discrete, we use the name `IsRankOneDiscrete` to refer to discrete valuations in this setting.

## Main Definitions
* `Valuation.IsRankOneDiscrete`: We define a `Γ`-valued valuation `v` to be discrete if if there is
an element `γ : Γˣ` that is `< 1` and generates the range of `v`,

## TODO
* Define (pre)uniformizers for nontrivial discrete valuations.
* Relate discrete valuations and discrete valuation rings (contained in the project
  <https://github.com/mariainesdff/LocalClassFieldTheory>)
-/

namespace Valuation

open Set LinearOrderedCommGroup MonoidWithZeroHom
open Function Multiplicative Set WithZero

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

variable {A : Type*} [Ring A] (v : Valuation A Γ)

/-- Given a linearly ordered commutative group with zero `Γ` such that `Γˣ` is
nontrivial cyclic, a valuation `v : A → Γ` on a ring `A` is *discrete*, if
`genLTOne Γˣ` belongs to the image. Note that the latter is equivalent to
asking that `1 : ℤ` belongs to the image of the corresponding additive valuation. -/
class IsRankOneDiscrete : Prop where
  exists_generator_lt_one' : ∃ (γ : Γˣ), Subgroup.zpowers γ = (valueGroup v) ∧ γ < 1

namespace IsRankOneDiscrete

lemma exists_generator_lt_one [IsRankOneDiscrete v] :
    ∃ (γ : Γˣ), Subgroup.zpowers γ = valueGroup v ∧ γ < 1 :=
  exists_generator_lt_one'

/-- Given a discrete valuation `v`, `Valuation.IsRankOneDiscrete.generator` is a generator of
the value group that is `< 1`. -/
noncomputable def generator [IsRankOneDiscrete v] : Γˣ := (exists_generator_lt_one v).choose

lemma generator_zpowers_eq_valueGroup [IsRankOneDiscrete v] :
    (Subgroup.zpowers (generator v)) = valueGroup v :=
  (exists_generator_lt_one v).choose_spec.1

lemma generator_lt_one [IsRankOneDiscrete v] : (generator v) < 1 :=
  (exists_generator_lt_one v).choose_spec.2

lemma generator_ne_one [IsRankOneDiscrete v] : (generator v) ≠ 1 :=
  ne_of_lt <| generator_lt_one v

lemma generator_zpowers_eq_range (K : Type*) [Field K] (w : Valuation K Γ) [IsRankOneDiscrete w] :
    Units.val '' (Subgroup.zpowers (generator w)) = range w \ {0} := by
  rw [generator_zpowers_eq_valueGroup, valueGroup_eq_range]

lemma generator_mem_range (K : Type*) [Field K] (w : Valuation K Γ) [IsRankOneDiscrete w] :
    ↑(generator w) ∈ range w := by
  apply diff_subset
  rw [← generator_zpowers_eq_range]
  exact ⟨generator w, by simp⟩

lemma generator_ne_zero [IsRankOneDiscrete v] : (generator v : Γ) ≠ 0 := by simp

instance [IsRankOneDiscrete v] : IsCyclic <| valueGroup v := by
  rw [isCyclic_iff_exists_zpowers_eq_top, ← generator_zpowers_eq_valueGroup]
  use ⟨generator v, by simp⟩
  rw [eq_top_iff]
  rintro ⟨g, k, hk⟩
  simp only [Subgroup.mem_top, forall_const]
  use k
  ext
  simp [← hk]

instance [IsRankOneDiscrete v] : Nontrivial (valueGroup v) :=
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

end Valuation
