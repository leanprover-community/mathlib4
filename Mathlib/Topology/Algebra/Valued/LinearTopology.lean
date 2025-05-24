/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.Topology.Algebra.Valued.ValuedField

/-!
# Valuation rings of valued fields have a linear topology

## Main Results
* `IsLinearTopology.of_isDiscreteValuationRing`: for a valued field `K`,
  the valuation ring `𝒪[K]` has a linear topology, when the valuation ring is a DVR.

-/
open Valued Filter Topology

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

instance IsLinearTopology.of_isDiscreteValuationRing :
    IsLinearTopology 𝒪[K] 𝒪[K] := by
  by_cases hd : DiscreteTopology K
  · have : DiscreteTopology 𝒪[K] := inferInstance
    infer_instance
  rw [isLinearTopology_iff_hasBasis_ideal]
  have := (hasBasis_nhds_zero K Γ₀).comap (Subtype.val : 𝒪[K] → K)
  have hn0 : 𝓝 (0 : 𝒪[K]) = comap Subtype.val (𝓝 0) := nhds_induced Subtype.val 0
  rw [← hn0] at this
  refine this.to_hasBasis ?_ ?_
  · intro y _
    let I : Set 𝒪[K] := {x : 𝒪[K] | Valued.v (x : K) < y}
    lift I to Ideal 𝒪[K] with I' hI'
    · simp only [Set.mem_setOf_eq, ZeroMemClass.coe_zero, map_zero, Subring.coe_add,
      Subtype.forall, smul_eq_mul, Subring.coe_mul, map_mul, I,]
      refine ⟨by simp, fun _ _ _ _ ↦ Valued.v.map_add_lt, ?_⟩
      intro a ha b hb hva
      suffices v a * v b < 1 * y by simpa
      apply mul_lt_mul_of_le_of_lt_of_nonneg_of_pos ha hva zero_le'
      norm_num
    refine ⟨I', ?_, ?_⟩
    · refine IsOpen.mem_nhds ?_ ?_
      · simpa [hI', I] using continuous_subtype_val.isOpen_preimage _ (isOpen_ball _ _)
      · simp
    · simp [hI', I]
  · intro I hI
    have hI' : I ≠ ⊥ := by
      rintro rfl
      simp only [Submodule.bot_coe] at hI
      have : DiscreteTopology 𝒪[K] := by
        rw [discreteTopology_iff_singleton_mem_nhds]
        intro y
        simpa using singleton_add_mem_nhds_of_nhds_zero y hI
      rw [Valued.discreteTopology_valuationRing_iff_discreteTopology] at this
      contradiction
    obtain ⟨x, hx, hx0⟩ : ∃ y ∈ I, y ≠ 0 := Submodule.exists_mem_ne_zero_of_ne_bot hI'
    let y : Γ₀ := Valued.v (x : K)
    lift y to Γ₀ˣ with y' hy'
    · simp [y, hx0]
    refine ⟨y', trivial, ?_⟩
    simp only [Set.preimage_setOf_eq, y, hy']
    intro a ha
    simp only [Set.mem_setOf_eq, y] at ha
    have hax : Valued.v ((a : K) / x) ≤ 1 := by
      simp only [map_div₀, y]
      rw [div_le_one₀]
      · exact ha.le
      · simp [Valued.v.pos_iff, hx0]
    have : a = x * ⟨_, hax⟩ := by
      ext
      simp only [Subring.coe_mul, y]
      rw [mul_div_cancel₀]
      simpa using hx0
    rw [this, SetLike.mem_coe]
    exact Ideal.IsTwoSided.mul_mem_of_left _ hx
