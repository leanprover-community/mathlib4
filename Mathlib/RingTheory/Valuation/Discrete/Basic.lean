/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.GroupTheory.ArchimedeanDensely
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

lemma IsDiscrete.mulArchimedean [IsDiscrete v] : MulArchimedean Γ := by
  constructor
  intro x y hy
  obtain ⟨g, hgen, hg_lt_one, -, ha⟩ := v.exists_generator_lt_one
  rcases le_or_lt x 1 with hx|hx
  · exact ⟨0, by simpa using hx⟩
  norm_cast at hx hy ⊢
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, g⁻¹ ^ k = x := by
    lift x to Γˣ using isUnit_iff_ne_zero.mpr (zero_lt_one.trans hx).ne'
    norm_cast
    simp only [← Subgroup.mem_zpowers_iff, Subgroup.zpowers_inv, hgen, Subgroup.mem_top]
  have hk : 0 < k := by
    simp only [Units.val_inv_eq_inv_val, ← inv_zpow', zpow_neg] at hx
    rwa [one_lt_zpow_iff_right₀] at hx
    norm_cast
    simp [hg_lt_one]
  obtain ⟨l, rfl⟩ : ∃ l : ℤ, g⁻¹ ^ l = y := by
    lift y to Γˣ using isUnit_iff_ne_zero.mpr (zero_lt_one.trans hy).ne'
    norm_cast
    simp only [← Subgroup.mem_zpowers_iff, Subgroup.zpowers_inv, hgen, Subgroup.mem_top]
  have hl : 0 < l := by
    simp only [Units.val_inv_eq_inv_val, ← inv_zpow', zpow_neg] at hy
    rwa [one_lt_zpow_iff_right₀] at hy
    norm_cast
    simp [hg_lt_one]
  lift k to ℕ using hk.le
  lift l to ℕ using hl.le
  norm_cast at hk hl ⊢
  obtain ⟨n, hn⟩ := Archimedean.arch k hl
  refine ⟨n, ?_⟩
  simp only [Units.val_inv_eq_inv_val, zpow_natCast, ← pow_mul']
  refine pow_right_monotone ?_ hn
  simp [hg_lt_one.le]

lemma IsDiscrete.nontrivial_value_group [IsDiscrete v] : Nontrivial Γˣ := by
  refine ⟨1, v.exists_generator_lt_one.choose, ?_⟩
  exact ne_of_gt <| (v.exists_generator_lt_one.choose_spec).2.1

lemma IsDiscrete.cyclic_value_group [IsDiscrete v] : IsCyclic Γˣ := by
  rw [isCyclic_iff_exists_zpowers_eq_top]
  exact ⟨_, (v.exists_generator_lt_one.choose_spec).1⟩

lemma IsDiscrete.not_denselyOrdered [IsDiscrete v] : ¬ DenselyOrdered Γ := by
  have := nontrivial_value_group v
  have H := cyclic_value_group v
  contrapose! H
  rw [← denselyOrdered_units_iff] at H
  exact not_isCyclic_of_denselyOrdered _

open Multiplicative in
lemma IsDiscrete.nonempty_mulOrderIso_multiplicative_int [IsDiscrete v] :
    Nonempty (Γ ≃*o ℤₘ₀) := by
  have := mulArchimedean v
  have := nontrivial_value_group v
  rw [LinearOrderedCommGroupWithZero.discrete_iff_not_denselyOrdered]
  exact not_denselyOrdered v

-- TODO: move elsewhere
instance {X : Type*} [Preorder X] [Nonempty X] [NoMaxOrder X] : NoMaxOrder (WithZero X) := by
  constructor
  intro x
  refine WithZero.cases_on x ?_ ?_
  · inhabit X
    exact ⟨(default : X), WithZero.zero_lt_coe _⟩
  · intro a
    obtain ⟨b, hb⟩ := exists_gt a
    refine ⟨b, ?_⟩
    simp [hb]

open Multiplicative in
lemma IsDiscrete.infinite_value_group [IsDiscrete v] : Infinite Γˣ := by
  obtain ⟨e⟩ := nonempty_mulOrderIso_multiplicative_int v
  let e' : Γˣ ≃* Multiplicative ℤ := MulEquiv.unzero (WithZero.withZeroUnitsEquiv.trans e)
  rw [e'.toEquiv.infinite_iff]
  infer_instance

-- TODO: move elsewhere
@[to_additive]
lemma Subgroup.zpowers_eq_zpowers_iff {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
    {x y : G} : Subgroup.zpowers x = Subgroup.zpowers y ↔ x = y ∨ x⁻¹ = y := by
  rw [iff_comm]
  constructor
  · rintro (rfl|rfl) <;>
    · simp
  intro h
  have hx : x ∈ Subgroup.zpowers y := by
    simp [← h]
  have hy : y ∈ Subgroup.zpowers x := by
    simp [h]
  rw [Subgroup.mem_zpowers_iff] at hx hy
  obtain ⟨k, rfl⟩ := hy
  obtain ⟨l, hl⟩ := hx
  wlog hx1 : 1 < x
  · push_neg at hx1
    rcases hx1.eq_or_lt with rfl|hx1
    · simp
    · specialize this (x := x⁻¹) (-k) (by simp [h]) (-l) (by simp [hl]) (by simp [hx1])
      simpa [or_comm] using this
  simp only [← zpow_mul] at hl
  replace hl : x ^ (k * l) = x ^ (1 : ℤ) := by simp [hl]
  rw [zpow_right_inj hx1, Int.mul_eq_one_iff_eq_one_or_neg_one] at hl
  refine hl.imp ?_ ?_ <;>
  simp +contextual

lemma IsDiscrete.exists_mem_val_eq_genLTOne [IsDiscrete v] :
    haveI := IsDiscrete.cyclic_value_group v
    haveI := IsDiscrete.nontrivial_value_group v
    ∃ a : A, v a = genLTOne (G := Γˣ) := by
  obtain ⟨g, hgen, hg_lt_one, a, ha⟩ := v.exists_generator_lt_one
  use a
  -- TODO: have the naked `getLTOne` have a lemma showing it is `< 1`
  rw [ha]
  have := IsDiscrete.cyclic_value_group v
  have := IsDiscrete.nontrivial_value_group v
  norm_cast
  rw [← Subgroup.genLTOne_zpowers_eq_top ⊤, Subgroup.zpowers_eq_zpowers_iff] at hgen
  refine hgen.resolve_right ?_
  refine ((genLTOne_lt_one Γˣ).trans ?_).ne'
  simp [hg_lt_one]

variable {K : Type*} [DivisionRing K]
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

lemma heq (w : Valuation K Γ) [IsDiscrete w] :
    MonoidHom.mrange w = ⊤ := by
  ext y
  simp only [MonoidHom.mem_mrange, Submonoid.mem_top, iff_true]
  exact IsDiscrete.surj w y

variable [IsCyclic Γˣ] [Nontrivial Γˣ]
/-- A valuation on a field `K` is discrete if and only if it is surjective. -/
lemma isDiscrete_iff_surjective (w : Valuation K Γ) :
    IsDiscrete w ↔ Surjective w := by
  refine ⟨fun _ ↦ IsDiscrete.surj w, fun h ↦ ⟨LinearOrderedCommGroup.genLTOne Γˣ,
    by simp, ?_, by apply h⟩⟩
  simpa using (⊤ : Subgroup Γˣ).genLTOne_lt_one


end Valuation
