/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.Topology.Algebra.Valued.ValuedField

/-!
# Valuation rings of valued fields have a linear topology

## Main Results
* `IsLinearTopology.of_isDiscreteValuationRing`: for a valued field `K`,
  the valuation ring `𝒪[K]` has a linear topology, when the valuation ring is a DVR.

-/
open Valued Filter Topology

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀]

lemma Valued.maximalIdeal_eq_ball :
    (𝓂[K] : Set 𝒪[K]) = {x : 𝒪[K] | Valued.v (x : K) < 1} := by
  ext
  simp [Valuation.Integer.not_isUnit_iff_valuation_lt_one]

lemma _root_.Irreducible.maximalIdeal_pow_succ_eq_ball_pow [IsDiscreteValuationRing 𝒪[K]]
    {ϖ : 𝒪[K]} (h : Irreducible ϖ) (n : ℕ) :
    ((𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) : Set 𝒪[K]) =
      {x : 𝒪[K] | Valued.v (x : K) < (Valued.v (ϖ : K)) ^ n} := by
  ext x
  simp only [h.maximalIdeal_eq, Ideal.span_singleton_pow, SetLike.mem_coe,
    Ideal.mem_span_singleton, ← map_pow, Set.mem_setOf_eq]
  constructor
  · rintro ⟨c, rfl⟩
    simp only [pow_succ, mul_assoc, Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow]
    have : Valued.v (ϖ : K) * Valued.v (c : K) < 1 := by
      refine mul_lt_one_of_nonneg_of_lt_one_left zero_le' ?_ c.prop
      simp [← Valuation.Integer.not_isUnit_iff_valuation_lt_one, h.not_isUnit]
    simpa using mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (le_refl _) this
      zero_le' (by simp [← map_pow, Valued.v.pos_iff, h.ne_zero])
  · rcases eq_or_ne x 0 with rfl|hx
    · simp
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx h
    have : Valued.v (u : K) = 1 := (Valuation.integer.integers Valued.v).valuation_unit u
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, this, map_pow, one_mul,
      Units.isUnit, IsUnit.dvd_mul_left]
    intro H
    rw [pow_lt_pow_iff_right_of_lt_one₀ ] at H
    · exact pow_dvd_pow ϖ H
    · simp [Valued.v.pos_iff, h.ne_zero]
    · simp [← Valuation.Integer.not_isUnit_iff_valuation_lt_one, h.not_isUnit]

lemma Valued.v_eq_one_iff_of_discreteTopology
    [MulArchimedean Γ₀] [DiscreteTopology K] {x : K} :
    Valued.v x = 1 ↔ x ≠ 0 := by
  have : ({0} : Set K) ∈ 𝓝 0 := by simp
  rw [mem_nhds_zero] at this
  obtain ⟨y, hy⟩ := this
  simp only [Set.subset_singleton_iff, Set.mem_setOf_eq] at hy
  rcases lt_or_le (1 : Γ₀) y with h1 | h1
  · specialize hy 1
    simp [h1.not_le] at hy
  rw [← Valued.v.pos_iff]
  constructor <;> intro h
  · simp [h]
  wlog hx1 : 1 < (Valued.v x) generalizing x y
  · push_neg at hx1
    rcases hx1.eq_or_lt with hx1 | hx1
    · exact hx1
    have hx0 : 0 < Valued.v x⁻¹ := by simp [h]
    specialize @this x⁻¹ y hy h1 hx0 ?_
    · simp [one_lt_inv₀ h, hx1]
    simpa using this
  obtain ⟨n, hn⟩ := MulArchimedean.arch (y : Γ₀)⁻¹ hx1
  rw [Valued.v.pos_iff] at h
  have : v (x ^ (n + 1))⁻¹ < y := by
    refine (inv_le_of_inv_le₀ (by simp) hn).trans_lt' ?_
    simp only [map_inv₀, map_pow]
    rw [inv_lt_inv₀]
    · exact pow_lt_pow_right₀ hx1 (by simp)
    · simp [← map_pow, Valued.v.pos_iff, h]
    · simp [← map_pow, Valued.v.pos_iff, h]
  simpa [h] using hy _ this

instance IsLinearTopology.of_isDiscreteValuationRing {K Γ₀ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀]
    [MulArchimedean Γ₀]
    [Valued K Γ₀]
    [IsDiscreteValuationRing 𝒪[K]] :
    IsLinearTopology 𝒪[K] 𝒪[K] := by
  rw [isLinearTopology_iff_hasBasis_ideal, hasBasis_iff]
  intro U
  have : U ∈ 𝓝 0 ↔ (Subtype.val '' U) ∈ 𝓝 0 := by
    rw [← image_mem_map_iff Subtype.val_injective, map_nhds_subtype_coe_eq_nhds]
    · simp
    · rw [eventually_nhds_iff]
      exact ⟨𝒪[K], by simp, isOpen_integer K, by simp [Valuation.mem_integer_iff]⟩
  rw [this, Valued.mem_nhds_zero]
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hp0 {n} : 0 < Valued.v (p : K) ^ n := by
    rw [← map_pow, Valued.v.pos_iff]
    simp [hp.ne_zero]
  constructor
  · intro ⟨x, hx⟩
    rw [Set.subset_image_iff] at hx
    obtain ⟨V, hVU, hV⟩ := hx
    obtain ⟨n, hn⟩ : ∃ n : ℕ, Valued.v (p : K) ^ n < x := by
      suffices ∃ n : ℕ, (x : Γ₀)⁻¹ ≤ (Valued.v (p : K) ^ n)⁻¹ by
        obtain ⟨n, hn⟩ := this
        refine ⟨n + 1, ?_⟩
        rw [inv_le_inv₀] at hn
        · refine hn.trans_lt' ?_
          refine pow_lt_pow_right_of_lt_one₀ ?_ ?_ ?_
          · simpa using hp0 (n := 1)
          · exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hp.not_isUnit
          · simp
        · simp
        · exact hp0
      simp_rw [← inv_pow]
      apply MulArchimedean.arch (x : Γ₀)⁻¹
      rw [one_lt_inv₀]
      · exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hp.not_isUnit
      · simpa using hp0 (n := 1)
    replace hV : V = {y : 𝒪[K] | Valued.v (y : K) < x} := by
      ext ⟨y, hy⟩
      simp only [Set.mem_setOf_eq]
      constructor <;> intro h
      · exact hV.le ⟨⟨y, hy⟩, h, rfl⟩
      · obtain ⟨z, hz, rfl⟩ := hV.ge h
        simp [hz]
    replace hV : {y : 𝒪[K] | Valued.v (y : K) < Valued.v (p : K) ^ n} ⊆ U := by
      refine subset_trans (subset_trans ?_ hV.ge) hVU
      rw [Set.setOf_subset_setOf]
      intro
      exact hn.trans'
    rw [← hp.maximalIdeal_pow_succ_eq_ball_pow] at hV
    · refine ⟨_, ?_, hV⟩
      rw [hp.maximalIdeal_pow_succ_eq_ball_pow]
      refine IsOpen.mem_nhds ?_ ?_
      · simpa using continuous_subtype_val.isOpen_preimage _ (isOpen_ball _ _)
      · simp [hp0]
  · rintro ⟨V, hV, hV'⟩
    rcases eq_or_ne V ⊥ with hv0|hV0
    · -- contradiction, the bottom ideal is not open in the valuation ring of a valued field
      simp only [hv0, Submodule.bot_coe] at hV
      rw [mem_nhds_iff] at hV
      obtain ⟨s, hs, hs', hs0⟩ := hV
      simp only [hv0, Submodule.bot_coe, Set.subset_singleton_iff] at hs
      replace hs : s = {0} := le_antisymm hs (by simpa using hs0)
      have : IsOpen ({0} : Set 𝒪[K]) := by rwa [← hs]
      replace this : IsOpen ({0} : Set K) := by
        simpa using (isOpen_integer _).isOpenMap_subtype_val _ this
      have _ := discreteTopology_of_isOpen_singleton_zero this
      have hp1 : Valued.v (p : K) < 1 := by
        exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hp.not_isUnit
      simp [(Valued.v_eq_one_iff_of_discreteTopology (x := (p : K))).mpr
        (by simpa using hp.ne_zero)] at hp1
    obtain ⟨n, hn⟩ : ∃ n : ℕ, V = 𝓂[K] ^ n := by
      refine exists_maximalIdeal_pow_eq_of_principal 𝒪[K] ?_ _ hV0
      exact IsPrincipalIdealRing.principal _
    refine ⟨Units.mk0 (Valued.v (p : K) ^ n) hp0.ne', ?_⟩
    simp only [Units.val_mk0]
    rw [Set.subset_image_iff]
    refine ⟨((𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) : Set 𝒪[K]), ?_, ?_⟩
    · exact subset_trans (Ideal.pow_le_pow_right (Nat.le_succ n)) (subset_trans hn.ge hV')
    · rw [hp.maximalIdeal_pow_succ_eq_ball_pow]
      ext
      simp only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, exists_and_left, exists_prop,
        exists_eq_right_right, and_iff_left_iff_imp]
      intro hx
      refine hx.le.trans ?_
      rw [← map_pow, ← Subring.coe_pow]
      exact Subtype.prop (p ^ n : 𝒪[K])
