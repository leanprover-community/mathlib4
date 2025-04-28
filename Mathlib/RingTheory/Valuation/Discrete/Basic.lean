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
valuation `v : A → Γ` on a ring `A` is *discrete*, if `genLTOne Γˣ` belongs to the image, where
`genLTOne Γˣ` is the generator of `Γˣ` that is `< 1`. When `Γ := ℤₘ₀` (defined in
`Multiplicative.termℤₘ₀`), `genLTOne Γˣ = ofAdd (-1)` and the condition of being discrete is
equivalent to asking that `ofAdd (-1 : ℤ)` belongs to the image, in turn equivalent to asking that
`1 : ℤ` belongs to the image of the corresponding *additive* valuation.


## Main Definitions
* `IsDiscrete`: We define a `Γ`-valued valuation `v` to be discrete if `Γˣ` is cyclic and
  `genLTOne Γˣ` belongs to the image of `v`

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
  exists_generator_lt_one : ∃ (γ : Γˣ), Subgroup.zpowers γ = ⊤ ∧ γ < 1 ∧ ↑γ ∈ range v

lemma exists_generator_lt_one [IsDiscrete v] :
  ∃ (γ : Γˣ), Subgroup.zpowers γ = ⊤ ∧ γ < 1 ∧ ↑γ ∈ range v := IsDiscrete.exists_generator_lt_one

lemma IsDiscrete.cyclic_value_group [IsDiscrete v] : IsCyclic Γˣ := by
  rw [isCyclic_iff_exists_zpowers_eq_top]
  exact ⟨_, (v.exists_generator_lt_one.choose_spec).1⟩

lemma IsDiscrete.nontrivial_value_group [IsDiscrete v] : Nontrivial Γˣ := by
  refine ⟨1, v.exists_generator_lt_one.choose, ?_⟩
  exact ne_of_gt <| (v.exists_generator_lt_one.choose_spec).2.1

lemma IsDiscrete.infinite_value_group [IsDiscrete v] : Infinite Γˣ := by sorry


lemma IsDiscrete.exists_mem_val_eq_genLTOne [IsDiscrete v] :
    haveI := IsDiscrete.cyclic_value_group v
    haveI := IsDiscrete.nontrivial_value_group v
    ∃ a : A, v a = LinearOrderedCommGroup.Subgroup.genLTOne (G := Γˣ) ⊤ := sorry

lemma heq (B : Type*) [DivisionRing B] (w : Valuation B Γ) [IsDiscrete w] :
    MonoidHom.mrange w = ⊤ := by
  have h_cyc := IsDiscrete.cyclic_value_group w
  have h_ntriv := IsDiscrete.nontrivial_value_group w
  ext x
  refine ⟨fun h ↦ by trivial, fun _ ↦ ?_⟩
  have := GroupWithZero.eq_zero_or_unit x
  rcases this with hx | ⟨u, hu⟩
  · rw [hx]
    exact ⟨0, Valuation.map_zero w⟩
  · rw [hu]
    have := LinearOrderedCommGroup.Subgroup.genLTOne_zpowers_eq_top (G := Γˣ) ⊤
    set γ := LinearOrderedCommGroup.Subgroup.genLTOne (G := Γˣ) ⊤ with hγ
    have hu' : u ∈ (⊤ : Subgroup _) := by simp only [Subgroup.mem_top]
    rw [← this, Subgroup.mem_zpowers_iff] at hu'
    obtain ⟨k, hk⟩ := hu'
    rw [← hk]
    let a := (IsDiscrete.exists_mem_val_eq_genLTOne w).choose
    use a ^ k
    simp only [map_zpow₀, Units.val_zpow_eq_zpow_val]
    have ha := (IsDiscrete.exists_mem_val_eq_genLTOne w).choose_spec
    rw [← ha]

-- let fromYael /-- Any ordered group is isomorphic to the units of itself adjoined with `0`. -/
open Classical in
@[simps!]
noncomputable def OrderMonoidIso.withZeroUnits {α : Type*} [GroupWithZero α] [Preorder α] :
    WithZero αˣ ≃*o α where
  toMulEquiv := WithZero.withZeroUnitsEquiv
  map_le_map_iff' {a b} := by
    simp [WithZero.withZeroUnitsEquiv]
    -- ==simp [WithZero.withZeroUnitsEquiv]
    sorry -- see Mathlib/Algebra/Order/Hom/Monoid.lean


open scoped Multiplicative in
def forYakov (B : Type*) [DivisionRing B] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {w : Valuation B Γ₀} [IsDiscrete w] : MonoidHom.mrange w ≃*o ℤₘ₀ := by
  let ω := MulEquiv.submonoidCongr (heq B w)
  let ω' : (MonoidHom.mrange w) ≃*o (⊤ : Submonoid Γ₀) := by
    use ω
    exact Iff.symm ge_iff_le

  let ξ : (⊤ : Submonoid Γ₀) ≃* Γ₀ := Submonoid.topEquiv
  let ξ' : (⊤ : Submonoid Γ₀) ≃*o Γ₀ := by
    use ξ
    exact Iff.symm ge_iff_le

  let α : Γ₀ˣ ≃* Multiplicative ℤ := by
    let ρ := zmodCyclicMulEquiv (IsDiscrete.cyclic_value_group w)
    rw [@Nat.card_eq_zero_of_infinite _ (IsDiscrete.infinite_value_group w)] at ρ
    exact ρ.symm

  let β := @WithZero.withZeroUnitsEquiv Γ₀ _ _
  let β' : WithZero Γ₀ˣ ≃*o Γ₀ := by
    use β
    intro a b
    have := GroupWithZero.eq_zero_or_unit a
    rcases this with _ | ⟨u, hu⟩
    · simp_all
    · simp_all
      have := GroupWithZero.eq_zero_or_unit b
      rcases this with _ | ⟨v, hv⟩
      · simp_all
      · rw [hv]
        dsimp [β]
        simp
        sorry

  let γ := α.withZero

  let δ := β.symm.trans γ
  let η := (ω.trans ξ).trans δ
  use η
  intro a b
  simp only [MulEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · dsimp [η, δ, γ] at h
    sorry
  sorry



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

variable [IsCyclic Γˣ] [Nontrivial Γˣ]
/-- A valuation on a field `K` is discrete if and only if it is surjective. -/
lemma isDiscrete_iff_surjective (w : Valuation K Γ) :
    IsDiscrete w ↔ Surjective w := by
  refine ⟨fun _ ↦ IsDiscrete.surj w, fun h ↦ ⟨LinearOrderedCommGroup.genLTOne Γˣ,
    by simp, ?_, by apply h⟩⟩
  simpa using (⊤ : Subgroup Γˣ).genLTOne_lt_one


end Valuation
