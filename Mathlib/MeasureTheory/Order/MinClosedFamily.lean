/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Topology.Order.MonotoneConvergence

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Generic Essential-Infimum Selection for Min-Closed Function Families

This module provides a generic, pure measure-theoretic selection
theorem for families of non-negative functions on a finite measure space:

Given:
- A measurable space `Ω` and a finite measure `μ` on `Ω` (`[IsFiniteMeasure μ]`),
- An upper bound `T : ℝ≥0`,
- An arbitrary lower envelope `S : Ω → ℝ≥0` (no measurability or stopping assumptions),
- A nonempty family `D ⊆ (Ω → ℝ≥0)` of measurable functions (`∀ f ∈ D, Measurable f`),
- Closed under pointwise binary minimum: `∀ f₁ ∈ D, ∀ f₂ ∈ D, (fun ω ↦ min (f₁ ω) (f₂ ω)) ∈ D`,
- Pointwise bounded: `∀ f ∈ D, ∀ ω, S ω ≤ f ω` and `∀ f ∈ D, ∀ ω, f ω ≤ T`.

There exists:
1. A minimizing sequence `fseq : ℕ → Ω → ℝ≥0` in `D`,
2. Pointwise antitone: `∀ n ω, fseq (n + 1) ω ≤ fseq n ω`,
3. Pointwise converging to `fstar`,
4. Pointwise representation equality: `∀ ω, fstar ω = ⨅ n, fseq n ω`,
5. Measurability: `Measurable fstar`,
6. Pointwise envelope bounds: `∀ ω, S ω ≤ fstar ω` and `∀ ω, fstar ω ≤ T`,
7. Competitor domination: `∀ g ∈ D, fstar ≤ᵐ[μ] g` (almost everywhere for each competitor).

All auxiliary variational and dominated-convergence lemmas are private to prevent
namespace pollution. Exactly one public generic theorem is exported.
-/

@[expose] public section
noncomputable section

namespace MeasureTheory

open Filter Topology Set
open scoped NNReal ENNReal

section MinClosedFamily

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {D : Set (Ω → ℝ≥0)} {T : ℝ≥0}

/-! ### Private Support: Integrability of Bounded Measurable Functions -/

private theorem integrable_of_bounded_measurable {f : Ω → ℝ≥0} (hm : Measurable f)
    (hle : ∀ ω, f ω ≤ T) : Integrable (fun ω ↦ (f ω : ℝ)) μ := by
  have hm_real : Measurable (fun ω ↦ (f ω : ℝ)) :=
    NNReal.continuous_coe.measurable.comp hm
  refine Integrable.mono' (integrable_const (T : ℝ)) hm_real.aestronglyMeasurable
    (Eventually.of_forall fun ω ↦ ?_)
  rw [Real.norm_of_nonneg (NNReal.coe_nonneg _)]
  exact NNReal.coe_le_coe.mpr (hle ω)

/-! ### Private Support: Scalar Expectation Infimum -/

private def familyExpectations (μ : Measure Ω) (D : Set (Ω → ℝ≥0)) : Set ℝ :=
  (fun f ↦ ∫ ω, (f ω : ℝ) ∂μ) '' D

omit [IsFiniteMeasure μ] in
private theorem familyExpectations_nonempty (hD : D.Nonempty) :
    (familyExpectations μ D).Nonempty := by
  obtain ⟨f, hf⟩ := hD
  exact ⟨∫ ω, (f ω : ℝ) ∂μ, ⟨f, hf, rfl⟩⟩

omit [IsFiniteMeasure μ] in
private theorem familyExpectations_bddBelow (D : Set (Ω → ℝ≥0)) :
    BddBelow (familyExpectations μ D) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨f, _, rfl⟩
  exact integral_nonneg fun ω ↦ NNReal.coe_nonneg (f ω)

private def familyInfimumMean (μ : Measure Ω) (D : Set (Ω → ℝ≥0)) : ℝ :=
  sInf (familyExpectations μ D)

omit [IsFiniteMeasure μ] in
private theorem familyInfimumMean_le {f : Ω → ℝ≥0} (hf : f ∈ D) :
    familyInfimumMean μ D ≤ ∫ ω, (f ω : ℝ) ∂μ :=
  csInf_le (familyExpectations_bddBelow D) ⟨f, hf, rfl⟩

omit [IsFiniteMeasure μ] in
private theorem exists_near_minimizer (hD : D.Nonempty) (ε : ℝ) (hε : 0 < ε) :
    ∃ f ∈ D, ∫ ω, (f ω : ℝ) ∂μ < familyInfimumMean μ D + ε := by
  have hne : (familyExpectations μ D).Nonempty := familyExpectations_nonempty hD
  have hlt : sInf (familyExpectations μ D) < sInf (familyExpectations μ D) + ε :=
    lt_add_of_pos_right _ hε
  obtain ⟨x, ⟨f, hf, rfl⟩, hxlt⟩ := exists_lt_of_csInf_lt hne hlt
  exact ⟨f, hf, hxlt⟩

omit [IsFiniteMeasure μ] in
private theorem exists_minimizing_sequence (hD : D.Nonempty) :
    ∃ σ : ℕ → Ω → ℝ≥0,
      (∀ n, σ n ∈ D) ∧
      (∀ n, ∫ ω, (σ n ω : ℝ) ∂μ < familyInfimumMean μ D + 1 / ((n : ℝ) + 1)) := by
  classical
  have hopt : ∀ n : ℕ, ∃ f ∈ D, ∫ ω, (f ω : ℝ) ∂μ < familyInfimumMean μ D + 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    exact exists_near_minimizer hD (1 / ((n : ℝ) + 1)) hpos
  choose σ hσ using hopt
  exact ⟨σ, fun n ↦ (hσ n).1, fun n ↦ (hσ n).2⟩

/-! ### Private Support: Cumulative Pointwise Minimum Construction -/

private def cumulativeMin (σ : ℕ → Ω → ℝ≥0) : ℕ → Ω → ℝ≥0
  | 0 => σ 0
  | n + 1 => fun ω ↦ min (cumulativeMin σ n ω) (σ (n + 1) ω)

omit mΩ [IsFiniteMeasure μ] in
private theorem cumulativeMin_mem (σ : ℕ → Ω → ℝ≥0) (hσ : ∀ n, σ n ∈ D)
    (hmin : ∀ f₁ ∈ D, ∀ f₂ ∈ D, (fun ω ↦ min (f₁ ω) (f₂ ω)) ∈ D) (n : ℕ) :
    cumulativeMin σ n ∈ D := by
  induction n with
  | zero => exact hσ 0
  | succ n ih => exact hmin (cumulativeMin σ n) ih (σ (n + 1)) (hσ (n + 1))

omit mΩ [IsFiniteMeasure μ] in
private theorem cumulativeMin_succ (σ : ℕ → Ω → ℝ≥0) (n : ℕ) (ω : Ω) :
    cumulativeMin σ (n + 1) ω = min (cumulativeMin σ n ω) (σ (n + 1) ω) :=
  rfl

omit mΩ [IsFiniteMeasure μ] in
private theorem cumulativeMin_anti (σ : ℕ → Ω → ℝ≥0) (n : ℕ) (ω : Ω) :
    cumulativeMin σ (n + 1) ω ≤ cumulativeMin σ n ω := by
  rw [cumulativeMin_succ]
  exact min_le_left _ _

omit mΩ [IsFiniteMeasure μ] in
private theorem cumulativeMin_antitone (σ : ℕ → Ω → ℝ≥0) (ω : Ω) :
    Antitone (fun n ↦ cumulativeMin σ n ω) :=
  antitone_nat_of_succ_le (fun n ↦ cumulativeMin_anti σ n ω)

omit mΩ [IsFiniteMeasure μ] in
private theorem cumulativeMin_le_sample (σ : ℕ → Ω → ℝ≥0) (n : ℕ) (ω : Ω) :
    cumulativeMin σ n ω ≤ σ n ω := by
  cases n with
  | zero => exact le_rfl
  | succ n =>
    rw [cumulativeMin_succ]
    exact min_le_right _ _

omit mΩ [IsFiniteMeasure μ] in
private theorem cumulativeMin_ge_S {S : Ω → ℝ≥0} (σ : ℕ → Ω → ℝ≥0) (hσ : ∀ n, σ n ∈ D)
    (hge : ∀ f ∈ D, ∀ ω, S ω ≤ f ω)
    (_hmin : ∀ f₁ ∈ D, ∀ f₂ ∈ D, (fun ω ↦ min (f₁ ω) (f₂ ω)) ∈ D) (n : ℕ) (ω : Ω) :
    S ω ≤ cumulativeMin σ n ω :=
  hge (cumulativeMin σ n) (cumulativeMin_mem σ hσ _hmin n) ω

omit mΩ [IsFiniteMeasure μ] in
private theorem cumulativeMin_le_T (σ : ℕ → Ω → ℝ≥0) (hσ : ∀ n, σ n ∈ D)
    (hle : ∀ f ∈ D, ∀ ω, f ω ≤ T)
    (_hmin : ∀ f₁ ∈ D, ∀ f₂ ∈ D, (fun ω ↦ min (f₁ ω) (f₂ ω)) ∈ D) (n : ℕ) (ω : Ω) :
    cumulativeMin σ n ω ≤ T :=
  hle (cumulativeMin σ n) (cumulativeMin_mem σ hσ _hmin n) ω

private theorem cumulativeMin_integral_le_sample (σ : ℕ → Ω → ℝ≥0) (hσ : ∀ n, σ n ∈ D)
    (hm : ∀ f ∈ D, Measurable f) (hle : ∀ f ∈ D, ∀ ω, f ω ≤ T)
    (_hmin : ∀ f₁ ∈ D, ∀ f₂ ∈ D, (fun ω ↦ min (f₁ ω) (f₂ ω)) ∈ D) (n : ℕ) :
    (∫ ω, (cumulativeMin σ n ω : ℝ) ∂μ) ≤ ∫ ω, (σ n ω : ℝ) ∂μ := by
  refine integral_mono_of_nonneg (Eventually.of_forall fun ω ↦ NNReal.coe_nonneg _)
    (integrable_of_bounded_measurable (hm (σ n) (hσ n)) (hle (σ n) (hσ n)))
    (Eventually.of_forall fun ω ↦ NNReal.coe_le_coe.mpr (cumulativeMin_le_sample σ n ω))

private theorem cumulativeMin_integral_tendsto (σ : ℕ → Ω → ℝ≥0) (hσ : ∀ n, σ n ∈ D)
    (hopt : ∀ n, ∫ ω, (σ n ω : ℝ) ∂μ < familyInfimumMean μ D + 1 / ((n : ℝ) + 1))
    (hm : ∀ f ∈ D, Measurable f) (hle : ∀ f ∈ D, ∀ ω, f ω ≤ T)
    (hmin : ∀ f₁ ∈ D, ∀ f₂ ∈ D, (fun ω ↦ min (f₁ ω) (f₂ ω)) ∈ D) :
    Tendsto (fun n ↦ ∫ ω, (cumulativeMin σ n ω : ℝ) ∂μ) atTop
      (𝓝 (familyInfimumMean μ D)) := by
  have hlow (n : ℕ) : familyInfimumMean μ D ≤ ∫ ω, (cumulativeMin σ n ω : ℝ) ∂μ :=
    familyInfimumMean_le (cumulativeMin_mem σ hσ hmin n)
  have hhigh (n : ℕ) : (∫ ω, (cumulativeMin σ n ω : ℝ) ∂μ) ≤
      familyInfimumMean μ D + 1 / ((n : ℝ) + 1) :=
    (cumulativeMin_integral_le_sample σ hσ hm hle hmin n).trans (hopt n).le
  have hlim : Tendsto (fun n : ℕ ↦ familyInfimumMean μ D + 1 / ((n : ℝ) + 1)) atTop
      (𝓝 (familyInfimumMean μ D)) := by
    have ht := (tendsto_const_nhds (x := familyInfimumMean μ D)).add
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [add_zero] using ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim hlow hhigh

/-! ### Private Support: Pointwise Limit Functions -/

private def pointwiseLimit (σ : ℕ → Ω → ℝ≥0) : Ω → ℝ≥0 :=
  fun ω ↦ ⨅ n, cumulativeMin σ n ω

omit mΩ [IsFiniteMeasure μ] in
private theorem pointwiseLimit_le_cumulativeMin (σ : ℕ → Ω → ℝ≥0) (n : ℕ) (ω : Ω) :
    pointwiseLimit σ ω ≤ cumulativeMin σ n ω :=
  ciInf_le (OrderBot.bddBelow _) n

omit mΩ [IsFiniteMeasure μ] in
private theorem pointwiseLimit_ge_S {S : Ω → ℝ≥0} (σ : ℕ → Ω → ℝ≥0) (hσ : ∀ n, σ n ∈ D)
    (hge : ∀ f ∈ D, ∀ ω, S ω ≤ f ω)
    (_hmin : ∀ f₁ ∈ D, ∀ f₂ ∈ D, (fun ω ↦ min (f₁ ω) (f₂ ω)) ∈ D) (ω : Ω) :
    S ω ≤ pointwiseLimit σ ω :=
  le_ciInf fun n ↦ cumulativeMin_ge_S σ hσ hge _hmin n ω

omit mΩ [IsFiniteMeasure μ] in
private theorem pointwiseLimit_le_T (σ : ℕ → Ω → ℝ≥0) (hσ : ∀ n, σ n ∈ D)
    (hle : ∀ f ∈ D, ∀ ω, f ω ≤ T)
    (_hmin : ∀ f₁ ∈ D, ∀ f₂ ∈ D, (fun ω ↦ min (f₁ ω) (f₂ ω)) ∈ D) (ω : Ω) :
    pointwiseLimit σ ω ≤ T :=
  (pointwiseLimit_le_cumulativeMin σ 0 ω).trans (cumulativeMin_le_T σ hσ hle _hmin 0 ω)

omit mΩ [IsFiniteMeasure μ] in
private theorem tendsto_cumulativeMin_pointwiseLimit (σ : ℕ → Ω → ℝ≥0) (ω : Ω) :
    Tendsto (fun n ↦ cumulativeMin σ n ω) atTop (𝓝 (pointwiseLimit σ ω)) :=
  tendsto_atTop_ciInf (cumulativeMin_antitone σ ω) (OrderBot.bddBelow _)

omit mΩ [IsFiniteMeasure μ] in
private theorem tendsto_cumulativeMin_coe_pointwiseLimit (σ : ℕ → Ω → ℝ≥0) (ω : Ω) :
    Tendsto (fun n ↦ ((cumulativeMin σ n ω : ℝ≥0) : ℝ)) atTop (𝓝 ((pointwiseLimit σ ω : ℝ≥0) :
      ℝ)) :=
  NNReal.continuous_coe.continuousAt.tendsto.comp (tendsto_cumulativeMin_pointwiseLimit σ ω)

omit [IsFiniteMeasure μ] in
private theorem measurable_pointwiseLimit (σ : ℕ → Ω → ℝ≥0) (hσ : ∀ n, σ n ∈ D)
    (hm : ∀ f ∈ D, Measurable f)
    (hmin : ∀ f₁ ∈ D, ∀ f₂ ∈ D, (fun ω ↦ min (f₁ ω) (f₂ ω)) ∈ D) :
    Measurable (pointwiseLimit σ) := by
  have hm_n (n : ℕ) : Measurable (cumulativeMin σ n) :=
    hm _ (cumulativeMin_mem σ hσ hmin n)
  exact Measurable.iInf hm_n

/-! ### Private Support: Dominated Convergence for Competitors -/

private theorem competitor_difference_integral_tendsto_zero (σ : ℕ → Ω → ℝ≥0) (hσ : ∀ n, σ n ∈ D)
    (hopt : ∀ n, ∫ ω, (σ n ω : ℝ) ∂μ < familyInfimumMean μ D + 1 / ((n : ℝ) + 1))
    (hm : ∀ f ∈ D, Measurable f) (hle : ∀ f ∈ D, ∀ ω, f ω ≤ T)
    (hmin : ∀ f₁ ∈ D, ∀ f₂ ∈ D, (fun ω ↦ min (f₁ ω) (f₂ ω)) ∈ D)
    {g : Ω → ℝ≥0} (hg : g ∈ D) :
    Tendsto (fun n ↦ ∫ ω, ((cumulativeMin σ n ω : ℝ) - (min (cumulativeMin σ n ω) (g ω) : ℝ)) ∂μ)
      atTop (𝓝 0) := by
  have hlow (n : ℕ) : 0 ≤ ∫ ω, ((cumulativeMin σ n ω : ℝ) - (min (cumulativeMin σ n ω) (g ω) :
    ℝ)) ∂μ := by
    refine integral_nonneg (fun ω ↦ ?_)
    exact sub_nonneg.mpr (min_le_left _ _)
  have hhigh (n : ℕ) :
      (∫ ω, ((cumulativeMin σ n ω : ℝ) - (min (cumulativeMin σ n ω) (g ω) : ℝ)) ∂μ) <
        1 / ((n : ℝ) + 1) := by
    have hfn_mem := cumulativeMin_mem σ hσ hmin n
    have hmin_mem : (fun ω ↦ min (cumulativeMin σ n ω) (g ω)) ∈ D :=
      hmin (cumulativeMin σ n) hfn_mem g hg
    have hI_le : familyInfimumMean μ D ≤ ∫ ω, (min (cumulativeMin σ n ω) (g ω) : ℝ) ∂μ :=
      familyInfimumMean_le hmin_mem
    have hint_sub : (∫ ω, ((cumulativeMin σ n ω : ℝ) - (min (cumulativeMin σ n ω) (g ω) : ℝ)) ∂μ) =
        (∫ ω, (cumulativeMin σ n ω : ℝ) ∂μ) - (∫ ω, (min (cumulativeMin σ n ω) (g ω) : ℝ) ∂μ) := by
      exact integral_sub
        (integrable_of_bounded_measurable (hm _ hfn_mem) (hle _ hfn_mem))
        (integrable_of_bounded_measurable (hm _ hmin_mem) (hle _ hmin_mem))
    rw [hint_sub]
    have hup : (∫ ω, (cumulativeMin σ n ω : ℝ) ∂μ) ≤ ∫ ω, (σ n ω : ℝ) ∂μ :=
      cumulativeMin_integral_le_sample σ hσ hm hle hmin n
    have hup2 : (∫ ω, (cumulativeMin σ n ω : ℝ) ∂μ) < familyInfimumMean μ D + 1 / ((n : ℝ) + 1) :=
      hup.trans_lt (hopt n)
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_one_div_add_atTop_nhds_zero_nat hlow (fun n ↦ (hhigh n).le)

private theorem competitor_difference_integral_limit_zero (σ : ℕ → Ω → ℝ≥0) (hσ : ∀ n, σ n ∈ D)
    (hopt : ∀ n, ∫ ω, (σ n ω : ℝ) ∂μ < familyInfimumMean μ D + 1 / ((n : ℝ) + 1))
    (hm : ∀ f ∈ D, Measurable f) (hle : ∀ f ∈ D, ∀ ω, f ω ≤ T)
    (hmin : ∀ f₁ ∈ D, ∀ f₂ ∈ D, (fun ω ↦ min (f₁ ω) (f₂ ω)) ∈ D)
    {g : Ω → ℝ≥0} (hg : g ∈ D) :
    ∫ ω, ((pointwiseLimit σ ω : ℝ) - (min (pointwiseLimit σ ω) (g ω) : ℝ)) ∂μ = 0 := by
  let F : ℕ → Ω → ℝ := fun n ω ↦
    (cumulativeMin σ n ω : ℝ) - (min (cumulativeMin σ n ω) (g ω) : ℝ)
  let f : Ω → ℝ := fun ω ↦
    (pointwiseLimit σ ω : ℝ) - (min (pointwiseLimit σ ω) (g ω) : ℝ)
  have hF_meas (n : ℕ) : AEStronglyMeasurable (F n) μ := by
    have hfn_mem := cumulativeMin_mem σ hσ hmin n
    have hmin_mem := hmin (cumulativeMin σ n) hfn_mem g hg
    have h1 := (hm _ hfn_mem).coe_nnreal_real
    have h2 := (hm _ hmin_mem).coe_nnreal_real
    exact (h1.sub h2).aestronglyMeasurable
  have h_bound (n : ℕ) : ∀ᵐ ω ∂μ, ‖F n ω‖ ≤ (T : ℝ) := by
    refine Eventually.of_forall fun ω ↦ ?_
    have hpos : 0 ≤ F n ω := sub_nonneg.mpr (min_le_left _ _)
    rw [Real.norm_of_nonneg hpos]
    have hle_n : (cumulativeMin σ n ω : ℝ) ≤ (T : ℝ) :=
      NNReal.coe_le_coe.mpr (cumulativeMin_le_T σ hσ hle hmin n ω)
    have hmin_pos : 0 ≤ (min (cumulativeMin σ n ω : ℝ) (g ω : ℝ)) :=
      le_min (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
    linarith
  have h_lim : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ F n ω) atTop (𝓝 (f ω)) := by
    refine Eventually.of_forall fun ω ↦ ?_
    dsimp [F, f]
    have h1 := tendsto_cumulativeMin_coe_pointwiseLimit σ ω
    exact h1.sub (Tendsto.min h1 tendsto_const_nhds)
  have hdct := tendsto_integral_of_dominated_convergence (fun _ ↦ (T : ℝ)) hF_meas
    (integrable_const (T : ℝ)) h_bound h_lim
  have hzero := competitor_difference_integral_tendsto_zero σ hσ hopt hm hle hmin hg
  exact tendsto_nhds_unique hdct hzero

private theorem pointwiseLimit_le_competitor_ae (σ : ℕ → Ω → ℝ≥0) (hσ : ∀ n, σ n ∈ D)
    (hopt : ∀ n, ∫ ω, (σ n ω : ℝ) ∂μ < familyInfimumMean μ D + 1 / ((n : ℝ) + 1))
    (hm : ∀ f ∈ D, Measurable f) (hle : ∀ f ∈ D, ∀ ω, f ω ≤ T)
    (hmin : ∀ f₁ ∈ D, ∀ f₂ ∈ D, (fun ω ↦ min (f₁ ω) (f₂ ω)) ∈ D)
    {g : Ω → ℝ≥0} (hg : g ∈ D) :
    pointwiseLimit σ ≤ᵐ[μ] g := by
  let f : Ω → ℝ := fun ω ↦
    (pointwiseLimit σ ω : ℝ) - (min (pointwiseLimit σ ω) (g ω) : ℝ)
  have hpos : 0 ≤ f := fun ω ↦ sub_nonneg.mpr (min_le_left _ _)
  have hfi : Integrable f μ := by
    have h1 : Integrable (fun ω ↦ (pointwiseLimit σ ω : ℝ)) μ := by
      refine Integrable.mono' (integrable_const (T : ℝ)) ?_ (Eventually.of_forall fun ω ↦ ?_)
      · exact (measurable_pointwiseLimit σ hσ hm hmin).coe_nnreal_real.aestronglyMeasurable
      · rw [Real.norm_of_nonneg (NNReal.coe_nonneg _)]
        exact NNReal.coe_le_coe.mpr (pointwiseLimit_le_T σ hσ hle hmin ω)
    have h2 : Integrable (fun ω ↦ (min (pointwiseLimit σ ω) (g ω) : ℝ)) μ := by
      refine Integrable.mono' (integrable_const (T : ℝ)) ?_ (Eventually.of_forall fun ω ↦ ?_)
      · have hm1 := (measurable_pointwiseLimit σ hσ hm hmin).coe_nnreal_real
        have hm2 := (hm g hg).coe_nnreal_real
        exact (hm1.min hm2).aestronglyMeasurable
      · rw [Real.norm_of_nonneg (le_min (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))]
        exact (min_le_left _ _).trans (NNReal.coe_le_coe.mpr (pointwiseLimit_le_T σ hσ hle hmin ω))
    exact h1.sub h2
  have hint_zero := competitor_difference_integral_limit_zero σ hσ hopt hm hle hmin hg
  have hae_zero : f =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg hpos hfi).mp hint_zero
  filter_upwards [hae_zero] with ω hω
  dsimp [f] at hω
  have heq : (pointwiseLimit σ ω : ℝ) = min (pointwiseLimit σ ω : ℝ) (g ω : ℝ) := sub_eq_zero.mp hω
  have hle_real : (pointwiseLimit σ ω : ℝ) ≤ (g ω : ℝ) := min_eq_left_iff.mp heq.symm
  exact NNReal.coe_le_coe.mp hle_real

/-! ### Headline Generic Theorem -/

/-- **Generic Essential-Infimum Selection for Min-Closed Function Families**.
Given any nonempty family `D` of non-negative measurable functions on a finite measure space,
bounded below by an arbitrary lower envelope `S` and above by deterministic `T`, closed under
pointwise minimum:
1. There exists a decreasing sequence `fseq n ∈ D`.
2. `fseq` is pointwise antitone: `∀ n ω, fseq (n + 1) ω ≤ fseq n ω`.
3. The sequence converges pointwise to `fstar`.
4. Pointwise representation equality: `∀ ω, fstar ω = ⨅ n, fseq n ω`.
5. `fstar` is measurable: `Measurable fstar`.
6. Pointwise envelope bounds hold: `∀ ω, S ω ≤ fstar ω` and `∀ ω, fstar ω ≤ T`.
7. Lower bound domination: `∀ g ∈ D, fstar ≤ᵐ[μ] g` almost everywhere for each competitor. -/
theorem exists_essential_infimum_selection_of_min_closed
    {S : Ω → ℝ≥0}
    (hD_nonempty : D.Nonempty)
    (hD_meas : ∀ f ∈ D, Measurable f)
    (hD_min : ∀ f₁ ∈ D, ∀ f₂ ∈ D, (fun ω ↦ min (f₁ ω) (f₂ ω)) ∈ D)
    (hD_ge : ∀ f ∈ D, ∀ ω, S ω ≤ f ω)
    (hD_le : ∀ f ∈ D, ∀ ω, f ω ≤ T) :
    ∃ (fseq : ℕ → Ω → ℝ≥0) (fstar : Ω → ℝ≥0),
      (∀ n, fseq n ∈ D) ∧
      (∀ n ω, fseq (n + 1) ω ≤ fseq n ω) ∧
      (∀ ω, Tendsto (fun n ↦ fseq n ω) atTop (𝓝 (fstar ω))) ∧
      (∀ ω, fstar ω = ⨅ n, fseq n ω) ∧
      Measurable fstar ∧
      (∀ ω, S ω ≤ fstar ω) ∧
      (∀ ω, fstar ω ≤ T) ∧
      (∀ g ∈ D, fstar ≤ᵐ[μ] g) := by
  obtain ⟨σ, hσ_mem, hσ_opt⟩ := exists_minimizing_sequence (μ := μ) (D := D) hD_nonempty
  let fseq := cumulativeMin σ
  let fstar := pointwiseLimit σ
  refine ⟨fseq, fstar, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun n ↦ cumulativeMin_mem σ hσ_mem hD_min n
  · exact fun n ω ↦ cumulativeMin_anti σ n ω
  · exact fun ω ↦ tendsto_cumulativeMin_pointwiseLimit σ ω
  · exact fun ω ↦ rfl
  · exact measurable_pointwiseLimit σ hσ_mem hD_meas hD_min
  · exact fun ω ↦ pointwiseLimit_ge_S σ hσ_mem hD_ge hD_min ω
  · exact fun ω ↦ pointwiseLimit_le_T σ hσ_mem hD_le hD_min ω
  · exact fun g hg ↦
      pointwiseLimit_le_competitor_ae σ hσ_mem hσ_opt hD_meas hD_le hD_min hg

end MinClosedFamily

end MeasureTheory
