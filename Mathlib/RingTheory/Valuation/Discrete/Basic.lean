/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.Algebra.Order.Group.Cyclic
import Mathlib.Algebra.Order.Group.Units
import Mathlib.RingTheory.Valuation.Basic

/-!
# Discrete Valuations

Given a linearly ordered commutative group with zero `Γ` such that `Γˣ` is nontrivial cyclic, a
valuation `v : A → Γ` on a ring `A` is *discrete*, if `gen_lt_one Γˣ` belongs to the image. When
`Γ := ℤₘ₀`, the latter is equivalent to asking that `ofAdd (-1 : ℤ)` belongs to the image, in turn
equivalent to asking that `1 : ℤ` belongs to the image of the corresponding *additive* valuation.


## Main Definitions
* `IsDiscrete`: We define a `Γ`-valued valuation `v` to be discrete if `Γˣ` is cyclic and
  `gen_lt_one Γˣ` belongs to the image of `v`

## TODO
* Define (pre)uniformizers for nontrivial discrete valuations.
* Relate discrete valuations and discrete valuation rings.
-/

namespace Valuation

open Function Set LinearOrderedCommGroup

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

variable {A : Type*} [Ring A] (v : Valuation A Γ)

/-- A valuation `v` on a ring `A` is (normalized) discrete if it is `ℤₘ₀`-valued and
  `ofAdd (-1 : ℤ)` belongs to the image. Note that the latter is equivalent to
  asking that `1 : ℤ` belongs to the image of the corresponding additive valuation. -/
class IsDiscrete [IsCyclic Γˣ] [Nontrivial Γˣ] : Prop where
  exists_generator_lt_one : ∃ (γ :Γˣ), Subgroup.zpowers γ = ⊤ ∧ γ < 1 ∧ ↑γ ∈ range v

variable {K : Type*} [Field K]
variable [IsCyclic Γˣ] [Nontrivial Γˣ]

/-- A discrete valuation on a field `K` is surjective. -/
lemma IsDiscrete.surj (w : Valuation K Γ) [hv : IsDiscrete w] : Surjective w := by
  intro c
  by_cases hc : c = 0
  · exact ⟨0, by simp [hc]⟩
  obtain ⟨π, hπ_gen, hπ_lt_one, a, ha⟩ := hv
  set u : Γˣ := Units.mk0 c hc with hu
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hπ_gen ▸ Subgroup.mem_top u)
  use a^k
  rw [map_zpow₀, ha]
  norm_cast
  rw [hk, hu, Units.val_mk0]

/-- A `ℤₘ₀`-valued valuation on a field `K` is discrete if and only if it is surjective. -/
lemma isDiscrete_iff_surjective (w : Valuation K Γ) :
    IsDiscrete w ↔ Surjective w := by
  refine ⟨fun _ ↦ IsDiscrete.surj w, fun h ↦ ⟨LinearOrderedCommGroup.gen_lt_one Γˣ,
    by simp, ?_, by apply h⟩⟩
  simpa using (⊤ : Subgroup Γˣ).gen_lt_one_lt_one


end Valuation
