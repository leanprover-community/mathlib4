/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.Algebra.GroupWithZero.Range
import Mathlib.Algebra.Order.Group.Cyclic
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.Algebra.Order.Group.Units
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Discrete Valuations

Given a linearly ordered commutative group with zero `Γ` such that `Γˣ` is nontrivial cyclic, a
valuation `v : A → Γ` on a ring `A` is *discrete*, if `genLTOne Γˣ` belongs to the image, where
`genLTOne Γˣ` is the generator of `Γˣ` that is `< 1`. When `Γ := ℤₘ₀` (defined in
`Multiplicative.termℤₘ₀`), `genLTOne Γˣ = ofAdd (-1)` and the condition of being discrete is
equivalent to asking that `ofAdd (-1 : ℤ)` belongs to the image, in turn equivalent to asking that
`1 : ℤ` belongs to the image of the corresponding *additive* valuation.


## Main Definitions
* `IsDiscrete`: We define a `Γ`-valued valuation `v` to be discrete if `Γˣ` is cyclic and
  `genLTOne Γˣ` belongs to the image of `v`.

## TODO
* Define (pre)uniformizers for nontrivial discrete valuations.
* Relate discrete valuations and discrete valuation rings.
-/

namespace Valuation

open Function Set LinearOrderedCommGroup MonoidHomWithZero

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

variable {A : Type*} [CommRing A] [IsDomain A] (v : Valuation A Γ)

variable {v} in
lemma ne_zero_iff' (hv : v.supp.primeCompl = nonZeroDivisors A) {a : A} : v a ≠ 0 ↔ a ≠ 0 := by
  refine ⟨fun h ha ↦ (ha ▸ h) (Valuation.map_zero ..), fun h hva ↦ ?_⟩
  · replace hva : a ∈ (v.supp : Set A) := hva
    rw [← compl_compl (x := (v.supp : Set A)), mem_compl_iff] at hva
    replace hva : a ∉ (v.supp).primeCompl := hva
    simp only [hv, mem_nonZeroDivisors_iff_ne_zero, ne_eq, not_not] at hva
    exact h hva

/-- Given a linearly ordered commutative group with zero `Γ` such that `Γˣ` is
nontrivial cyclic, a valuation `v : A → Γ` on a ring `A` is *discrete*, if
`genLTOne Γˣ` belongs to the image. Note that the latter is equivalent to
asking that `1 : ℤ` belongs to the image of the corresponding additive valuation. -/
class IsDiscrete : Prop where
  supp_v' : v.supp.primeCompl = nonZeroDivisors A
  exists_generator_lt_one' : ∃ (γ : Γˣ), Subgroup.zpowers γ =
    (nonZeroDivisors_range (ne_zero_iff' supp_v')) ∧ γ < 1

namespace IsDiscrete

lemma supp_v [IsDiscrete v] : v.supp.primeCompl = nonZeroDivisors A := supp_v'

lemma exists_generator_lt_one [IsDiscrete v] :
    ∃ (γ : Γˣ), Subgroup.zpowers γ = (nonZeroDivisors_range (ne_zero_iff' (supp_v v))) ∧ γ < 1 :=
  exists_generator_lt_one'

/-- Given a discrete valuation `v`, `Valuation.IsDiscrete.generator` is a generator of the value
group that is `< 1`. -/
noncomputable def generator [IsDiscrete v] : Γˣ := (exists_generator_lt_one v).choose

lemma generator_zpowers_eq_nonZeroDivisors_range [IsDiscrete v] :
    (Subgroup.zpowers (generator v)) = (nonZeroDivisors_range (ne_zero_iff' (supp_v v))) :=
  (exists_generator_lt_one v).choose_spec.1

lemma generator_lt_one [IsDiscrete v] : (generator v) < 1 :=
  (exists_generator_lt_one v).choose_spec.2

lemma generator_zpowers_eq_range (K : Type*) [Field K] (w : Valuation K Γ) [IsDiscrete w] :
    Units.val '' (Subgroup.zpowers (generator w)) = range w \ {0} := by
  rw [generator_zpowers_eq_nonZeroDivisors_range, nonZeroDivisors_range_eq_range]

lemma generator_mem_range (K : Type*) [Field K] (w : Valuation K Γ) [IsDiscrete w] :
    ↑(generator w) ∈ range w := by
  apply diff_subset
  rw [← generator_zpowers_eq_range]
  exact ⟨generator w, by simp⟩

lemma generator_ne_zero [IsDiscrete v] : (generator v : Γ) ≠ 0 := by simp

lemma cyclic_value_group [IsDiscrete v] :
    IsCyclic <| nonZeroDivisors_range (ne_zero_iff' (supp_v v)) := by
  rw [isCyclic_iff_exists_zpowers_eq_top]
  rw [← generator_zpowers_eq_nonZeroDivisors_range]
  let γ := generator v
  have hγ : γ ∈ Subgroup.zpowers γ := by
    simp
  set η : Subgroup.zpowers γ := ⟨γ, hγ⟩ with hγ_def
  use η
  rw [eq_top_iff]
  rintro ⟨g, hg⟩
  rw [Subgroup.mem_zpowers_iff] at hg ⊢
  obtain ⟨k, hk⟩ := hg
  simp
  use k
  ext
  rw [Units.ext_iff] at hk
  exact hk

lemma nontrivial_value_group [IsDiscrete v] : Nontrivial Γˣ :=
  ⟨1, generator v, ne_of_gt <| generator_lt_one v⟩

end IsDiscrete

end Valuation
