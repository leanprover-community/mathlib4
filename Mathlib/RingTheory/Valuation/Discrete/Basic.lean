/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.Algebra.GroupWithZero.Range
import Mathlib.Algebra.Order.Group.Cyclic
import Mathlib.Algebra.Order.Group.Units
import Mathlib.RingTheory.Valuation.Basic

/-!
# Discrete Valuations

Given a linearly ordered commutative group with zero `Γ` such that `Γˣ` is nontrivial cyclic, a
valuation `v : A → Γ` on a ring `A` is *discrete*, if `genLTOne Γˣ` belongs to the image, where
`genLTOne Γˣ` is the generator of `Γˣ` that is `< 1`. When `Γ := ℤₘ₀` (defined in
`Multiplicative.termℤₘ₀`), `genLTOne Γˣ = ofAdd (-1)` and the condition of being discrete is
equivalent to asking that `ofAdd (-1 : ℤ)` belongs to the image, in turn equivalent to asking that
`1 : ℤ` belongs to the image of the corresponding *additive* valuation.


## Main Definitions
* `IsDiscrete`: We define a `Γ`-valued valuation `v` to be discrete if `Γˣ` is cyclic, nontrivial
  and `genLTOne Γˣ` generates the value group of `v`.

## TODO
* Define (pre)uniformizers for nontrivial discrete valuations.
* Relate discrete valuations and discrete valuation rings (contained in the project
  <https://github.com/mariainesdff/LocalClassFieldTheory>)
-/

namespace Valuation

open Set LinearOrderedCommGroup MonoidHomWithZero

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] [IsCyclic Γˣ] [Nontrivial Γˣ]

variable {A : Type*} [Ring A] (v : Valuation A Γ)

/-- Given a linearly ordered commutative group with zero `Γ` such that `Γˣ` is
nontrivial cyclic, a valuation `v : A → Γ` on a ring `A` is *discrete*, if
`genLTOne Γˣ` belongs to the image. Note that the latter is equivalent to
asking that `1 : ℤ` belongs to the image of the corresponding additive valuation. -/
class IsDiscrete : Prop where
  valueGroup_eq_zpowers : Subgroup.zpowers (genLTOne Γˣ) = (valueGroup v)

namespace IsDiscrete

lemma exists_generator_lt_one [IsDiscrete v] :
    ∃ (γ : Γˣ), Subgroup.zpowers γ = valueGroup v ∧ γ < 1 :=
  ⟨_, valueGroup_eq_zpowers, Subgroup.genLTOne_lt_one ..⟩

/-- Given a discrete valuation `v`, `Valuation.IsDiscrete.generator` is a generator of the value
group that is `< 1`: by definition, it coincides with `genLTOne Γˣ`. -/
noncomputable abbrev generator [IsDiscrete v] : Γˣ := genLTOne Γˣ

lemma generator_zpowers_eq_valueGroup [IsDiscrete v] :
    (Subgroup.zpowers (generator v)) = valueGroup v := valueGroup_eq_zpowers

lemma generator_lt_one [IsDiscrete v] : (generator v) < 1 :=
  Subgroup.genLTOne_lt_one ..

lemma generator_zpowers_eq_range (K : Type*) [Field K] (w : Valuation K Γ) [IsDiscrete w] :
    Units.val '' (Subgroup.zpowers (generator w)) = range w \ {0} := by
  rw [generator_zpowers_eq_valueGroup, valueGroup_eq_range]

lemma generator_mem_range (K : Type*) [Field K] (w : Valuation K Γ) [IsDiscrete w] :
    ↑(generator w) ∈ range w := by
  apply diff_subset
  rw [← generator_zpowers_eq_range]
  exact ⟨generator w, by simp⟩

lemma generator_ne_zero [IsDiscrete v] : (generator v : Γ) ≠ 0 := by simp

lemma valueGroup_IsCyclic [IsDiscrete v] : IsCyclic <| valueGroup v := by
  apply Subgroup.isCyclic

end IsDiscrete

end Valuation
