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
* `IsDiscrete`: We define a `Γ`-valued valuation `v` to be discrete if `Γˣ` is cyclic and
  `genLTOne Γˣ` belongs to the image of `v`.

## TODO
* Define (pre)uniformizers for nontrivial discrete valuations.
* Relate discrete valuations and discrete valuation rings.
-/

namespace Valuation

open Function Set LinearOrderedCommGroup

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

variable {A : Type*} [Ring A] (v : Valuation A Γ)

/-- Given a linearly ordered commutative group with zero `Γ` such that `Γˣ` is
nontrivial cyclic, a valuation `v : A → Γ` on a ring `A` is *discrete*, if
`genLTOne Γˣ` belongs to the image. Note that the latter is equivalent to
asking that `1 : ℤ` belongs to the image of the corresponding additive valuation. -/
class IsDiscrete : Prop where
  exists_generator_lt_one' : ∃ (γ : Γˣ), Subgroup.zpowers γ = ⊤ ∧ γ < 1 ∧ ↑γ ∈ range v

lemma exists_generator_lt_one [IsDiscrete v] :
  ∃ (γ : Γˣ), Subgroup.zpowers γ = ⊤ ∧ γ < 1 ∧ ↑γ ∈ range v := IsDiscrete.exists_generator_lt_one'

/-- Given a discrete valuation `v`, `Valuation.IsDiscrete.generator` is a generator of the value
group that is `< 1`. -/
noncomputable def generator [IsDiscrete v] : Γˣ := v.exists_generator_lt_one.choose

lemma generator_zpowers_eq_top [IsDiscrete v] :
    Subgroup.zpowers (generator v) = (⊤ : Subgroup Γˣ) := v.exists_generator_lt_one.choose_spec.1

lemma generator_lt_one [IsDiscrete v] : (generator v) < 1 :=
  v.exists_generator_lt_one.choose_spec.2.1

lemma generator_mem_range [IsDiscrete v] : ↑(generator v) ∈ range v :=
  v.exists_generator_lt_one.choose_spec.2.2

lemma IsDiscrete.cyclic_value_group [IsDiscrete v] : IsCyclic Γˣ := by
  rw [isCyclic_iff_exists_zpowers_eq_top]
  exact ⟨_, generator_zpowers_eq_top v⟩


lemma IsDiscrete.nontrivial_value_group [IsDiscrete v] : Nontrivial Γˣ :=
  ⟨1, generator v, ne_of_gt <| generator_lt_one v⟩

variable {K : Type*} [Field K]

/-- A discrete valuation on a field `K` is surjective. -/
lemma IsDiscrete.surj (w : Valuation K Γ) [IsDiscrete w] : Surjective w := by
  intro c
  by_cases hc : c = 0
  · exact ⟨0, by simp [hc]⟩
  obtain ⟨π, hπ_gen, hπ_lt_one, a, ha⟩ := w.exists_generator_lt_one
  set u : Γˣ := Units.mk0 c hc with hu
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hπ_gen ▸ Subgroup.mem_top u)
  use a^k
  rw [map_zpow₀, ha]
  norm_cast
  rw [hk, hu, Units.val_mk0]

/-- A valuation on a field `K` is discrete if and only if it is surjective. -/
lemma isDiscrete_iff_surjective (w : Valuation K Γ) [IsCyclic Γˣ] [Nontrivial Γˣ] :
    IsDiscrete w ↔ Surjective w := by
  refine ⟨fun _ ↦ IsDiscrete.surj w, fun h ↦ ⟨LinearOrderedCommGroup.genLTOne Γˣ,
    by simp, ?_, by apply h⟩⟩
  simpa using (⊤ : Subgroup Γˣ).genLTOne_lt_one

instance [hv : IsDiscrete v] : IsNontrivial v where
  exists_val_nontrivial := by
    obtain ⟨γ, _, _, x, hx_v⟩ := hv
    exact ⟨x, hx_v ▸ ⟨Units.ne_zero γ, ne_of_lt (by norm_cast)⟩⟩

end Valuation
