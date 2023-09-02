/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.NormedSpace.HahnBanach.SeparatingDual

/-!
# Rademacher theorem: a Lipschitz function is differentiable almost everywhere

-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

open Filter MeasureTheory Measure FiniteDimensional NNReal ENNReal

theorem LipschitzWith.ae_lineDifferentiableAt_of_prod
    {C : ℝ≥0} {f : E × ℝ → ℝ} (hf : LipschitzWith C f) {μ : Measure E} :
    ∀ᵐ p ∂(μ.prod volume), LineDifferentiableAt ℝ f p (0, 1) := by
  apply (ae_prod_mem_iff_ae_ae_mem (measurableSet_lineDifferentiableAt hf.continuous)).2
  apply eventually_of_forall (fun x ↦ ?_)
  have : ∀ᵐ (y : ℝ), DifferentiableAt ℝ (fun z ↦ f (x, z)) y := by
    apply LipschitzWith.ae_differentiableAt (C := C)
    intro z z'
    convert hf (x, z) (x, z')
    simp [Prod.edist_eq]
  filter_upwards [this] with y hy
  have h'y : DifferentiableAt ℝ (fun z ↦ f (x, z)) (y + 0) := by simpa using hy
  have : DifferentiableAt ℝ (fun t ↦ y + t) 0 :=
    (differentiable_id.const_add _).differentiableAt
  simpa only [LineDifferentiableAt, Prod.smul_mk, smul_zero, smul_eq_mul, mul_one, Prod.mk_add_mk,
    add_zero] using h'y.comp 0 this

variable {μ : Measure E} [IsAddHaarMeasure μ]

theorem LipschitzWith.ae_lineDifferentiableAt
    {C : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith C f) (v : E) :
    ∀ᵐ p ∂μ, LineDifferentiableAt ℝ f p v := by
  rcases eq_or_ne v 0 with rfl|hv
  · simp [lineDifferentiableAt_zero]
  let n := finrank ℝ E
  let F := Fin (n-1) → ℝ
  obtain ⟨L, hL⟩ : ∃ L : (F × ℝ) ≃L[ℝ] E, L (0, 1) = v := by
    have : Nontrivial E := nontrivial_of_ne v 0 hv
    have M : (F × ℝ) ≃L[ℝ] E := by
      apply ContinuousLinearEquiv.ofFinrankEq
      simpa using Nat.sub_add_cancel finrank_pos
    obtain ⟨N, hN⟩ : ∃ N : E ≃L[ℝ] E, N (M (0, 1)) = v :=
      SeparatingDual.exists_continuousLinearEquiv_apply_eq (by simp) hv
    exact ⟨M.trans N, hN⟩
  let ρ : Measure (F × ℝ) := addHaar.prod volume
  have : IsAddHaarMeasure (Measure.map L ρ) := L.isAddHaarMeasure_map ρ
  suffices H : ∀ᵐ p ∂(Measure.map L ρ), LineDifferentiableAt ℝ f p v from
    absolutelyContinuous_isAddHaarMeasure _ _ H
  apply (ae_map_iff L.continuous.aemeasurable (measurableSet_lineDifferentiableAt hf.continuous)).2
  have : ∀ᵐ p ∂ρ, LineDifferentiableAt ℝ (f ∘ L) p (0, 1) :=
    (hf.comp L.lipschitz).ae_lineDifferentiableAt_of_prod
  filter_upwards [this] with p hp
  have h'p : LineDifferentiableAt ℝ (f ∘ (L : (F × ℝ) →ₗ[ℝ] E)) p (0, 1) := hp
  rw [← hL]
  exact LineDifferentiableAt.of_comp h'p

theorem LipschitzWith.memℒp_lineDeriv {C : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith C f) (v : E) :
    Memℒp (fun x ↦ lineDeriv ℝ f x v) ∞ μ :=
  memℒp_top_of_bound (aestronglyMeasurable_lineDeriv hf.continuous μ)
    (C * ‖v‖) (eventually_of_forall (fun _x ↦ norm_lineDeriv_le_of_lipschitz ℝ hf))

open scoped Topology
open Metric Set

/-- Deplacer, et utiliser dans locallyuniformlimit-/
theorem IsCompact.cthickening {α : Type*} [PseudoMetricSpace α] [ProperSpace α] {s : Set α}
    (hs : IsCompact s) {r : ℝ} : IsCompact (cthickening r s) :=
  isCompact_of_isClosed_bounded isClosed_cthickening (bounded hs).cthickening

theorem glouglou {C D : ℝ≥0} {f g : E → ℝ} (hf : LipschitzWith C f) (hg : LipschitzWith D g)
    (h'g : HasCompactSupport g) (v : E) :
    ∫ x, lineDeriv ℝ f x v * g x ∂μ = - ∫ x, f x * lineDeriv ℝ g x v ∂μ := by
  have : Tendsto (fun (t : ℝ) ↦ ∫ x, (t⁻¹ • (f (x + t • v) - f x)) * g x ∂μ) (𝓝[>] 0)
              (𝓝 (∫ x, lineDeriv ℝ f x v * g x ∂μ)) := by
    sorry
    /- apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ (C * ‖v‖) * ‖g x‖)
    · apply eventually_of_forall (fun t ↦ ?_)
      apply AEStronglyMeasurable.mul ?_ hg.continuous.aestronglyMeasurable
      apply aestronglyMeasurable_const.smul
      apply AEStronglyMeasurable.sub _ hf.continuous.measurable.aestronglyMeasurable
      apply AEMeasurable.aestronglyMeasurable
      exact hf.continuous.measurable.comp_aemeasurable' (aemeasurable_id'.add_const _)
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      apply eventually_of_forall (fun x ↦ ?_)
      calc ‖t⁻¹ • (f (x + t • v) - f x) * g x‖
        = (t⁻¹ * ‖f (x + t • v) - f x‖) * ‖g x‖ := by simp [norm_mul, ht.le]
      _ ≤ (t⁻¹ * (C * ‖(x + t • v) - x‖)) * ‖g x‖ := by
        gcongr; exact LipschitzWith.norm_sub_le hf (x + t • v) x
      _ = (C * ‖v‖) *‖g x‖ := by field_simp [norm_smul, abs_of_nonneg ht.le]; ring
    · exact (Continuous.integrable_of_hasCompactSupport hg.continuous h'g).norm.const_mul _
    · filter_upwards [hf.ae_lineDifferentiableAt v] with x hx
      exact hx.hasLineDerivAt.tendsto_nhdsWithin_right.mul tendsto_const_nhds
    -/
  have : Tendsto (fun (t : ℝ) ↦ ∫ x, (t⁻¹ • (g (x + t • v) - g x)) * f x ∂μ) (𝓝[>] 0)
              (𝓝 (∫ x, lineDeriv ℝ g x v * f x ∂μ)) := by
    let K := cthickening (‖v‖) (tsupport g)
    have : IsCompact K := IsCompact.cthickening h'g
    apply tendsto_integral_filter_of_dominated_convergence
        (K.indicator (fun x ↦ (D * ‖v‖) * ‖f x‖))
    · apply eventually_of_forall (fun t ↦ ?_)
      apply AEStronglyMeasurable.mul ?_ hf.continuous.aestronglyMeasurable
      apply aestronglyMeasurable_const.smul
      apply AEStronglyMeasurable.sub _ hg.continuous.measurable.aestronglyMeasurable
      apply AEMeasurable.aestronglyMeasurable
      exact hg.continuous.measurable.comp_aemeasurable' (aemeasurable_id'.add_const _)
    · filter_upwards [Ioc_mem_nhdsWithin_Ioi' zero_lt_one] with t ht
      have t_pos : 0 < t := ht.1
      apply eventually_of_forall (fun x ↦ ?_)
      by_cases hx : x ∈ K
      · calc ‖t⁻¹ • (g (x + t • v) - g x) * f x‖
          = (t⁻¹ * ‖g (x + t • v) - g x‖) * ‖f x‖ := by simp [norm_mul, t_pos.le]
        _ ≤ (t⁻¹ * (D * ‖(x + t • v) - x‖)) * ‖f x‖ := by
          gcongr; exact LipschitzWith.norm_sub_le hg (x + t • v) x
        _ = (D * ‖v‖) *‖f x‖ := by field_simp [norm_smul, abs_of_nonneg t_pos.le]; ring
        _ = K.indicator (fun x ↦ (D * ‖v‖) * ‖f x‖) x := by rw [indicator_of_mem hx]
      · have A : g x = 0 := by
          rw [← Function.nmem_support]
          contrapose! hx
          exact self_subset_cthickening _ (subset_tsupport _ hx)
        have B : g (x + t • v) = 0 := by
          rw [← Function.nmem_support]
          contrapose! hx
          apply mem_cthickening_of_dist_le _ _  (‖v‖) (tsupport g) (subset_tsupport _ hx)
          simp only [dist_eq_norm, sub_add_cancel', norm_neg, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg t_pos.le, norm_pos_iff]
          exact mul_le_of_le_one_left (norm_nonneg v) ht.2
        simp only [B, A, _root_.sub_self, smul_eq_mul, mul_zero, zero_mul, norm_zero]
        exact indicator_nonneg (fun y hy ↦ by positivity) _
    ·
      sorry -- exact (Continuous.integrable_of_hasCompactSupport hg.continuous h'g).norm.const_mul _
    · filter_upwards [hg.ae_lineDifferentiableAt v] with x hx
      exact hx.hasLineDerivAt.tendsto_nhdsWithin_right.mul tendsto_const_nhds
