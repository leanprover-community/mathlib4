/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.NumberTheory.NumberField.FinitePlaces
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Algebra.Valued.WithVal

/-!
# Equivalence between `ℚ_[p]` and `WithVal v`

-/

variable {p : ℕ} [Fact p.Prime]

open NNReal WithZero UniformSpace

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
  -- nhds_discrete causes timeouts on TC search
  simpa [-nhds_discrete] using Padic.denseRange_ratCast p _

open Completion in
open scoped Valued in
/-- The p-adic numbers are isomophic as a field to the completion of the rationals at
the p-adic valuation. -/
noncomputable
def Padic.withValRingEquiv :
    ((Padic.mulValuation (p := p)).comap (Rat.castHom ℚ_[p])).Completion ≃+* ℚ_[p] where
  toFun := (Completion.extensionHom ((Rat.castHom ℚ_[p]).comp
    (WithVal.equiv ((Padic.mulValuation (p := p)).comap (Rat.castHom ℚ_[p]))).toRingHom)
    Padic.isUniformInducing_cast_withVal.uniformContinuous.continuous)
  invFun := Padic.isDenseInducing_cast_withVal.extend coe'
  left_inv y := by
    induction y using induction_on
    · generalize_proofs _ _ _ H
      refine isClosed_eq ?_ continuous_id
      exact (uniformContinuous_uniformly_extend Padic.isUniformInducing_cast_withVal
        (Padic.denseRange_ratCast p) (uniformContinuous_coe _)).continuous.comp
        (continuous_extension)
    · rw [extensionHom_coe]
      apply IsDenseInducing.extend_eq
      exact continuous_coe _
  right_inv y := by
    induction y using isClosed_property (Padic.denseRange_ratCast p)
    · refine isClosed_eq ?_ continuous_id
      refine continuous_extension.comp ?_
      exact (uniformContinuous_uniformly_extend Padic.isUniformInducing_cast_withVal
        (Padic.denseRange_ratCast p) (uniformContinuous_coe _)).continuous
    · have : ∀ q : ℚ, Padic.isDenseInducing_cast_withVal.extend coe' q = coe'
        ((WithVal.equiv ((Padic.mulValuation (p := p)).comap (Rat.castHom ℚ_[p]))).symm q) := by
        intro q
        apply IsDenseInducing.extend_eq
        exact continuous_coe _
      rw [this, extensionHom_coe]
      simp
  map_mul' := map_mul _
  map_add' := map_add _


@[simp]
lemma Padic.coe_withValRingEquiv :
    ⇑(Padic.withValRingEquiv (p := p)) = Completion.extension
      (Rat.cast ∘ (WithVal.equiv ((Padic.mulValuation (p := p)).comap (Rat.castHom ℚ_[p])))) :=
  rfl

@[simp]
lemma Padic.coe_withValRingEquiv_symm :
    ⇑(Padic.withValRingEquiv (p := p)).symm =
      Padic.isDenseInducing_cast_withVal.extend Completion.coe' := by
  rfl

-- is `IsUniformInducing f -> IsUniformInducing (extension f)` true? If so, would golf this.
lemma Padic.uniformContinuous_withValRingEquiv :
    UniformContinuous (Padic.withValRingEquiv (p := p)) := by
  suffices UniformContinuous (Padic.withValRingEquiv (p := p)).toAddMonoidHom from this
  apply uniformContinuous_addMonoidHom_of_continuous
  exact Completion.continuous_extension

lemma Padic.uniformContinuous_withValRingEquiv_symm :
    UniformContinuous (Padic.withValRingEquiv (p := p)).symm := by
  suffices UniformContinuous (Padic.withValRingEquiv (p := p)).symm.toAddMonoidHom from this
  exact uniformContinuous_uniformly_extend Padic.isUniformInducing_cast_withVal
    (Padic.denseRange_ratCast p) (Completion.uniformContinuous_coe _)

/-- The p-adic numbers are isomophic as uniform spaces to the completion of the rationals at
the p-adic valuation. -/
noncomputable
def Padic.withValUniformEquiv :
    ((Padic.mulValuation (p := p)).comap (Rat.castHom ℚ_[p])).Completion ≃ᵤ ℚ_[p] where
  __ := Padic.withValRingEquiv
  uniformContinuous_toFun := Padic.uniformContinuous_withValRingEquiv
  uniformContinuous_invFun := Padic.uniformContinuous_withValRingEquiv_symm
