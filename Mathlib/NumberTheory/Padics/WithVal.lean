/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.Algebra.Valued.WithVal

/-!
# Equivalence between `ℚ_[p]` and `WithVal v`

-/

variable {p : ℕ} [Fact p.Prime]

open NNReal WithZero

-- TODO: use Rat.padicValuation after #27667
lemma Padic.continuous_cast_withVal : Continuous ((Rat.castHom ℚ_[p]).comp
    (WithVal.equiv ((Padic.mulValuation (p := p)).comap (Rat.castHom ℚ_[p]))).toRingHom) := by
  rw [continuous_iff_continuousAt]
  intro x U
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, Rat.coe_castHom, RingHom.coe_coe,
    Function.comp_apply, Metric.mem_nhds_iff, gt_iff_lt, Filter.mem_map, Valued.mem_nhds,←
    Set.image_subset_iff, forall_exists_index, and_imp]
  intro ε hε hU
  obtain ⟨y, hy⟩ := rat_dense p 0 hε
  lift ε to ℝ≥0 using hε.le
  -- inventing a non-zero element of the ball
  have hp : (p : ℝ≥0)⁻¹ < 1 := by simp [inv_lt_one_iff₀, Nat.Prime.one_lt Fact.out]
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hp (Units.mk0 ε (by simpa using hε.ne'))
  simp only [inv_pow, Units.val_mk0, ← NNReal.coe_lt_coe] at hn
  use Units.mk0 (exp (-n : ℤ)) (by simp)
  refine subset_trans ?_ hU
  intro y
  simp only [Units.val_mk0, Set.mem_image, Set.mem_setOf_eq,
    Metric.mem_ball, dist_eq_norm, forall_exists_index, and_imp]
  rintro y h rfl
  set x' : ℚ := (WithVal.equiv
    ((Padic.mulValuation (p := p)).comap (Rat.castHom ℚ_[p]))) x with hx
  set y' : ℚ := (WithVal.equiv
    ((Padic.mulValuation (p := p)).comap (Rat.castHom ℚ_[p]))) y with hy
  change Valuation.comap _ _ (y' - x') < exp _ at h
  refine hn.trans' ?_
  simp only [← Rat.cast_sub, padicNormE.eq_padicNorm, padicNorm, zpow_neg, NNReal.coe_inv,
    NNReal.coe_pow, NNReal.coe_natCast]
  split_ifs with hxy
  · simp only [Rat.cast_zero, inv_pos]
    exact pow_pos (by simp [Nat.Prime.pos Fact.out]) _
  · simp only [Rat.cast_inv, Rat.cast_zpow, Rat.cast_natCast]
    rw [inv_lt_inv₀, ← zpow_natCast, zpow_lt_zpow_iff_right₀]
    · simpa [← Rat.cast_sub, hxy] using h
    · exact_mod_cast Nat.Prime.one_lt Fact.out
    · exact zpow_pos (by simp [Nat.Prime.pos Fact.out]) _
    · exact pow_pos (by simp [Nat.Prime.pos Fact.out]) _

lemma Padic.isUniformInducing_cast_withVal : IsUniformInducing ((Rat.castHom ℚ_[p]).comp
    (WithVal.equiv ((Padic.mulValuation (p := p)).comap (Rat.castHom ℚ_[p]))).toRingHom) := by
  constructor
  rw [uniformity_eq_comap_nhds_zero, uniformity_eq_comap_nhds_zero, Filter.comap_comap]
  ext U
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, Rat.coe_castHom, RingHom.coe_coe,
    Function.comp_apply, Filter.mem_comap, Set.preimage_comp, Set.preimage_subset_iff,
    Set.mem_preimage, ← Rat.cast_sub, ← map_sub, Prod.forall]
  constructor
  · rintro ⟨V, hV, hV'⟩
    refine ⟨((Rat.castHom ℚ_[p]).comp
    (WithVal.equiv ((Padic.mulValuation (p := p)).comap (Rat.castHom ℚ_[p]))).toRingHom) ⁻¹' V,
      ?_, ?_⟩
    · exact continuous_cast_withVal.continuousAt hV
    · simpa using hV'
  · rintro ⟨V, hV, hV'⟩
    simp only [Metric.mem_nhds_iff, gt_iff_lt]
    rw [Valued.mem_nhds_zero] at hV
    obtain ⟨γ, hγ⟩ := hV
    let ε : ℚ := p ^ (log γ : ℤ)
    refine ⟨_, ⟨ε, ?_, subset_refl _⟩, ?_⟩
    · simp only [ε, Rat.cast_zpow, Rat.cast_natCast]
      refine zpow_pos ?_ _
      exact_mod_cast Nat.Prime.pos Fact.out
    · intro x y hab
      refine hV' x y (hγ ?_)
      simp only [Set.mem_setOf_eq]
      set x' : ℚ := (WithVal.equiv
        ((Padic.mulValuation (p := p)).comap (Rat.castHom ℚ_[p]))) x with hx
      set y' : ℚ := (WithVal.equiv
        ((Padic.mulValuation (p := p)).comap (Rat.castHom ℚ_[p]))) y with hy
      simp only [Rat.cast_lt, map_sub, ← hy, ← hx, Metric.mem_ball,
        dist_zero_right, padicNormE.eq_padicNorm, ε] at hab
      change Valuation.comap _ _ (y' - x') < γ.val
      simp only [Valuation.comap_apply, eq_ratCast, mulValuation_toFun, Rat.cast_eq_zero,
        valuation_ratCast]
      split_ifs with hxy
      · simp
      · rw [← lt_log_iff_exp_lt (by simp)]
        rwa [padicNorm.eq_zpow_of_nonzero hxy, zpow_lt_zpow_iff_right₀] at hab
        exact_mod_cast Nat.Prime.one_lt Fact.out

lemma Padic.isDenseInducing_cast_withVal : IsDenseInducing ((Rat.castHom ℚ_[p]).comp
    (WithVal.equiv ((Padic.mulValuation (p := p)).comap (Rat.castHom ℚ_[p]))).toRingHom) := by
  refine Padic.isUniformInducing_cast_withVal.isDenseInducing ?_
  intro
  simpa using Padic.denseRange_ratCast _ _
